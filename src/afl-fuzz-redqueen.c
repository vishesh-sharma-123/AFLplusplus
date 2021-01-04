/*
   american fuzzy lop++ - redqueen implementation on top of cmplog
   ---------------------------------------------------------------

   Originally written by Michal Zalewski

   Forkserver design by Jann Horn <jannhorn@googlemail.com>

   Now maintained by by Marc Heuse <mh@mh-sec.de>,
                        Heiko Eißfeldt <heiko.eissfeldt@hexco.de> and
                        Andrea Fioraldi <andreafioraldi@gmail.com>

   Copyright 2016, 2017 Google Inc. All rights reserved.
   Copyright 2019-2020 AFLplusplus Project. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   Shared code to handle the shared memory. This is used by the fuzzer
   as well the other components like afl-tmin, afl-showmap, etc...

 */

#include <limits.h>
#include "afl-fuzz.h"
#include "cmplog.h"

///// Colorization

struct range {

  u32           start;
  u32           end;
  struct range *next;
  struct range *prev;
  u8            ok;

};

struct tainted {

  u32             pos;
  u32             len;
  struct tainted *next;
  struct tainted *prev;

};

static struct range *add_range(struct range *ranges, u32 start, u32 end) {

  struct range *r = ck_alloc_nozero(sizeof(struct range));
  r->start = start;
  r->end = end;
  r->next = ranges;
  r->ok = 0;
  if (likely(ranges)) ranges->prev = r;
  return r;

}

static struct range *pop_biggest_range(struct range **ranges) {

  struct range *r = *ranges;
  struct range *rmax = NULL;
  u32           max_size = 0;

  while (r) {

    if (!r->ok) {

      u32 s = 1 + r->end - r->start;

      if (s >= max_size) {

        max_size = s;
        rmax = r;

      }

    }

    r = r->next;

  }

  return rmax;

}

static u8 get_exec_checksum(afl_state_t *afl, u8 *buf, u32 len, u64 *cksum) {

  if (unlikely(common_fuzz_stuff(afl, buf, len))) { return 1; }

  *cksum = hash64(afl->fsrv.trace_bits, afl->fsrv.map_size, HASH_CONST);
  return 0;

}

/* replace everything with different values but stay in the same type */
static void type_replace(afl_state_t *afl, u8 *buf, u32 len) {

  u32 i;
  u8  c;
  for (i = 0; i < len; ++i) {

    // wont help for UTF or non-latin charsets
    do {

      switch (buf[i]) {

        case 'A' ... 'F':
          c = 'A' + rand_below(afl, 1 + 'F' - 'A');
          break;
        case 'a' ... 'f':
          c = 'a' + rand_below(afl, 1 + 'f' - 'a');
          break;
        case '0':
          c = '1';
          break;
        case '1':
          c = '0';
          break;
        case '2' ... '9':
          c = '2' + rand_below(afl, 1 + '9' - '2');
          break;
        case 'G' ... 'Z':
          c = 'G' + rand_below(afl, 1 + 'Z' - 'G');
          break;
        case 'g' ... 'z':
          c = 'g' + rand_below(afl, 1 + 'z' - 'g');
          break;
        case '!' ... '*':
          c = '!' + rand_below(afl, 1 + '*' - '!');
          break;
        case ',' ... '.':
          c = ',' + rand_below(afl, 1 + '.' - ',');
          break;
        case ':' ... '@':
          c = ':' + rand_below(afl, 1 + '@' - ':');
          break;
        case '[' ... '`':
          c = '[' + rand_below(afl, 1 + '`' - '[');
          break;
        case '{' ... '~':
          c = '{' + rand_below(afl, 1 + '~' - '{');
          break;
        case '+':
          c = '/';
          break;
        case '/':
          c = '+';
          break;
        case ' ':
          c = '\t';
          break;
        case '\t':
          c = ' ';
          break;
          /*
                case '\r':
                case '\n':
                  // nothing ...
                  break;
          */
        default:
          c = (buf[i] ^ 0xff);

      }

    } while (c == buf[i]);

    buf[i] = c;

  }

}

static u8 colorization(afl_state_t *afl, u8 *buf, u32 len, u64 exec_cksum,
                       struct tainted **taints) {

  struct range *  ranges = add_range(NULL, 0, len), *rng;
  struct tainted *taint = NULL;
  u8 *            backup = ck_alloc_nozero(len);
  u8 *            changed = ck_alloc_nozero(len);

  u64 orig_hit_cnt, new_hit_cnt;
  orig_hit_cnt = afl->queued_paths + afl->unique_crashes;

  afl->stage_name = "colorization";
  afl->stage_short = "colorization";
  afl->stage_max = (len << 1);

  afl->stage_cur = 0;
  memcpy(backup, buf, len);
  memcpy(changed, buf, len);
  type_replace(afl, changed, len);

  while ((rng = pop_biggest_range(&ranges)) != NULL &&
         afl->stage_cur < afl->stage_max) {

    u32 s = 1 + rng->end - rng->start;
    memcpy(buf + rng->start, changed + rng->start, s);

    u64 cksum;
    u64 start_us = get_cur_time_us();
    if (unlikely(get_exec_checksum(afl, buf, len, &cksum))) {

      goto checksum_fail;

    }

    u64 stop_us = get_cur_time_us();

    /* Discard if the mutations change the path or if it is too decremental
      in speed - how could the same path have a much different speed
      though ...*/
    // fprintf(stderr, "result: %llx <-> %llx %u-%u\n", cksum, exec_cksum,
    //        rng->start, rng->end);
    if (cksum != exec_cksum ||
        ((stop_us - start_us > 3 * afl->queue_cur->exec_us) &&
         likely(!afl->fixed_seed))) {

      memcpy(buf + rng->start, backup + rng->start, s);

      if (s > 1) {  // to not add 0 size ranges

        ranges = add_range(ranges, rng->start, rng->start - 1 + s / 2);
        ranges = add_range(ranges, rng->start + s / 2, rng->end);
        // fprintf(stderr, "split: s=%u %u-%u + %u-%u\n", s, rng->start,
        // rng->start - 1 + s / 2, rng->start - 1 + s / 2 , rng->end);

      }

      if (ranges == rng) {

        ranges = rng->next;
        if (ranges) { ranges->prev = NULL; }

      } else if (rng->next) {

        rng->prev->next = rng->next;
        rng->next->prev = rng->prev;

      } else {

        if (rng->prev) { rng->prev->next = NULL; }

      }

      free(rng);

    } else {

      rng->ok = 1;

    }

    ++afl->stage_cur;

  }

  rng = ranges;
  while (rng) {

    // if (rng->ok == 1) fprintf(stderr, "R: %u-%u\n", rng->start, rng->end);
    rng = rng->next;

  }

  u32 i = 1;
  u32 positions = 0;
  while (i) {

  restart:
    i = 0;
    struct range *r = NULL;
    u32           pos = (u32)-1;
    rng = ranges;

    while (rng) {

      if (rng->ok == 1 && rng->start < pos) {

        if (taint && taint->pos + taint->len == rng->start) {

          taint->len += (1 + rng->end - rng->start);
          positions += (1 + rng->end - rng->start);
          rng->ok = 2;
          goto restart;

        } else {

          r = rng;
          pos = rng->start;

        }

      }

      rng = rng->next;

    }

    if (r) {

      struct tainted *t = ck_alloc_nozero(sizeof(struct tainted));
      t->pos = r->start;
      t->len = 1 + r->end - r->start;
      positions += (1 + r->end - r->start);
      if (likely(taint)) { taint->prev = t; }
      t->next = taint;
      t->prev = NULL;
      taint = t;
      r->ok = 2;
      i = 1;

    }

  }

  *taints = taint;

  /* temporary: clean ranges */
  while (ranges) {

    rng = ranges;
    ranges = rng->next;
    ck_free(rng);

  }

  /* it makes no sense to retry in the next cycle, it will be the same result.
    so either we force full colorization as long as it takes or we try only
    once with a high enough number of tries. */
  if (afl->stage_cur < afl->stage_max) {

    afl->queue_cur->fully_colorized = 1;

  } else {

    // 2 makes no difference but allows us in the future to detect those seeds
    // that did not fully colorize.
    afl->queue_cur->fully_colorized = 2;

  }

  new_hit_cnt = afl->queued_paths + afl->unique_crashes;
  //#ifdef _DEBUG
  char fn[4096];
  snprintf(fn, sizeof(fn), "%s/introspection_color.txt", afl->out_dir);
  FILE *f = fopen(fn, "a");
  if (f) {

    fprintf(f,
            "Colorization: fname=%s len=%u result=%u execs=%u found=%llu "
            "taint=%u\n",
            afl->queue_cur->fname, len, afl->queue_cur->fully_colorized,
            afl->stage_cur, new_hit_cnt - orig_hit_cnt, positions);
    fclose(f);

  }

  //#endif
  afl->stage_finds[STAGE_COLORIZATION] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_COLORIZATION] += afl->stage_cur;
  ck_free(backup);
  ck_free(changed);

  return 0;

checksum_fail:
  ck_free(backup);
  ck_free(changed);

  return 1;

}

///// Input to State replacement

static u8 its_fuzz(afl_state_t *afl, u8 *buf, u32 len, u8 *status) {

  u64 orig_hit_cnt, new_hit_cnt;

  orig_hit_cnt = afl->queued_paths + afl->unique_crashes;

  if (unlikely(common_fuzz_stuff(afl, buf, len))) { return 1; }

  new_hit_cnt = afl->queued_paths + afl->unique_crashes;

  if (unlikely(new_hit_cnt != orig_hit_cnt)) {

    *status = 1;

  } else {

    *status = 2;

  }

  return 0;

}

static int strntoll(const char *str, size_t sz, char **end, int base,
                    long long *out) {

  char        buf[64];
  long long   ret;
  const char *beg = str;

  for (; beg && sz && *beg == ' '; beg++, sz--) {};

  if (!sz) return 1;
  if (sz >= sizeof(buf)) sz = sizeof(buf) - 1;

  memcpy(buf, beg, sz);
  buf[sz] = '\0';
  ret = strtoll(buf, end, base);
  if ((ret == LLONG_MIN || ret == LLONG_MAX) && errno == ERANGE) return 1;
  if (end) *end = (char *)beg + (*end - buf);
  *out = ret;

  return 0;

}

static int strntoull(const char *str, size_t sz, char **end, int base,
                     unsigned long long *out) {

  char               buf[64];
  unsigned long long ret;
  const char *       beg = str;

  for (; beg && sz && *beg == ' '; beg++, sz--)
    ;

  if (!sz) return 1;
  if (sz >= sizeof(buf)) sz = sizeof(buf) - 1;

  memcpy(buf, beg, sz);
  buf[sz] = '\0';
  ret = strtoull(buf, end, base);
  if (ret == ULLONG_MAX && errno == ERANGE) return 1;
  if (end) *end = (char *)beg + (*end - buf);
  *out = ret;

  return 0;

}

static u8 cmp_extend_encoding(afl_state_t *afl, struct cmp_header *h,
                              u64 pattern, u64 repl, u64 o_pattern,
                              u64 changed_val, u32 idx, u8 *orig_buf, u8 *buf,
                              u32 len, u8 do_reverse, u8 *status) {

  //(void)(changed_val); // TODO
  // we can use the information in changed_val to see if there is a computable
  // i2s transformation.
  // if (pattern != o_pattern && repl != changed_val)
  //   switch(pattern != o_pattern) {

  //      detect uppercase <-> lowercase, base64, hex encoding, etc.:
  //      repl = reverse_transform(TYPE, pattern);
  //    }
  //  not 100% but would have a chance to be detected

  u64 *buf_64 = (u64 *)&buf[idx];
  u32 *buf_32 = (u32 *)&buf[idx];
  u16 *buf_16 = (u16 *)&buf[idx];
  u8 * buf_8 = &buf[idx];
  u64 *o_buf_64 = (u64 *)&orig_buf[idx];
  u32 *o_buf_32 = (u32 *)&orig_buf[idx];
  u16 *o_buf_16 = (u16 *)&orig_buf[idx];
  u8 * o_buf_8 = &orig_buf[idx];

  u32 its_len = len - idx;

  u8 *               endptr;
  u8                 use_num = 0, use_unum = 0;
  unsigned long long unum;
  long long          num;

  if (afl->queue_cur->is_ascii) {

    endptr = buf_8;
    if (strntoll(buf_8, len - idx, (char **)&endptr, 0, &num)) {

      if (!strntoull(buf_8, len - idx, (char **)&endptr, 0, &unum))
        use_unum = 1;

    } else

      use_num = 1;

  }

  if (use_num && (u64)num == pattern) {

    size_t old_len = endptr - buf_8;
    size_t num_len = snprintf(NULL, 0, "%lld", num);

    u8 *new_buf = afl_realloc((void **)&afl->out_scratch_buf, len + num_len);
    if (unlikely(!new_buf)) { PFATAL("alloc"); }
    memcpy(new_buf, buf, idx);

    snprintf(new_buf + idx, num_len, "%lld", num);
    memcpy(new_buf + idx + num_len, buf_8 + old_len, len - idx - old_len);

    if (unlikely(its_fuzz(afl, new_buf, len, status))) { return 1; }

  } else if (use_unum && unum == pattern) {

    size_t old_len = endptr - buf_8;
    size_t num_len = snprintf(NULL, 0, "%llu", unum);

    u8 *new_buf = afl_realloc((void **)&afl->out_scratch_buf, len + num_len);
    if (unlikely(!new_buf)) { PFATAL("alloc"); }
    memcpy(new_buf, buf, idx);

    snprintf(new_buf + idx, num_len, "%llu", unum);
    memcpy(new_buf + idx + num_len, buf_8 + old_len, len - idx - old_len);

    if (unlikely(its_fuzz(afl, new_buf, len, status))) { return 1; }

  }

  if (SHAPE_BYTES(h->shape) >= 8 && *status != 1) {

    if (its_len >= 8 && *buf_64 == pattern && *o_buf_64 == o_pattern) {

      *buf_64 = repl;
      if (unlikely(its_fuzz(afl, buf, len, status))) { return 1; }
      *buf_64 = pattern;

    }

    // reverse encoding
    if (do_reverse && *status != 1) {

      if (unlikely(cmp_extend_encoding(afl, h, SWAP64(pattern), SWAP64(repl),
                                       SWAP64(o_pattern), SWAP64(changed_val),
                                       idx, orig_buf, buf, len, 0, status))) {

        return 1;

      }

    }

  }

  if (SHAPE_BYTES(h->shape) >= 4 && *status != 1) {

    if (its_len >= 4 && *buf_32 == (u32)pattern &&
        *o_buf_32 == (u32)o_pattern) {

      *buf_32 = (u32)repl;
      if (unlikely(its_fuzz(afl, buf, len, status))) { return 1; }
      *buf_32 = pattern;

    }

    // reverse encoding
    if (do_reverse && *status != 1) {

      if (unlikely(cmp_extend_encoding(afl, h, SWAP32(pattern), SWAP32(repl),
                                       SWAP32(o_pattern), SWAP32(changed_val),
                                       idx, orig_buf, buf, len, 0, status))) {

        return 1;

      }

    }

  }

  if (SHAPE_BYTES(h->shape) >= 2 && *status != 1) {

    if (its_len >= 2 && *buf_16 == (u16)pattern &&
        *o_buf_16 == (u16)o_pattern) {

      *buf_16 = (u16)repl;
      if (unlikely(its_fuzz(afl, buf, len, status))) { return 1; }
      *buf_16 = (u16)pattern;

    }

    // reverse encoding
    if (do_reverse && *status != 1) {

      if (unlikely(cmp_extend_encoding(afl, h, SWAP16(pattern), SWAP16(repl),
                                       SWAP16(o_pattern), SWAP16(changed_val),
                                       idx, orig_buf, buf, len, 0, status))) {

        return 1;

      }

    }

  }

  /* avoid CodeQL warning on unsigned overflow */
  if (/* SHAPE_BYTES(h->shape) >= 1 && */ *status != 1) {

    if (its_len >= 1 && *buf_8 == (u8)pattern && *o_buf_8 == (u8)o_pattern) {

      *buf_8 = (u8)repl;
      if (unlikely(its_fuzz(afl, buf, len, status))) { return 1; }
      *buf_8 = (u8)pattern;

    }

  }

  return 0;

}

static void try_to_add_to_dict(afl_state_t *afl, u64 v, u8 shape) {

  u8 *b = (u8 *)&v;

  u32 k;
  u8  cons_ff = 0, cons_0 = 0;
  for (k = 0; k < shape; ++k) {

    if (b[k] == 0) {

      ++cons_0;

    } else if (b[k] == 0xff) {

      ++cons_0;

    } else {

      cons_0 = cons_ff = 0;

    }

    if (cons_0 > 1 || cons_ff > 1) { return; }

  }

  maybe_add_auto(afl, (u8 *)&v, shape);

  u64 rev;
  switch (shape) {

    case 1:
      break;
    case 2:
      rev = SWAP16((u16)v);
      maybe_add_auto(afl, (u8 *)&rev, shape);
      break;
    case 4:
      rev = SWAP32((u32)v);
      maybe_add_auto(afl, (u8 *)&rev, shape);
      break;
    case 8:
      rev = SWAP64(v);
      maybe_add_auto(afl, (u8 *)&rev, shape);
      break;

  }

}

static u8 cmp_fuzz(afl_state_t *afl, u32 key, u8 *orig_buf, u8 *buf, u32 len,
                   struct tainted *taint) {

  struct cmp_header *h = &afl->shm.cmp_map->headers[key];
  struct tainted *   t;
  u32                i, j, idx, have_taint = 1;
  u32                loggeds = h->hits;
  if (h->hits > CMP_MAP_H) { loggeds = CMP_MAP_H; }

  u8 status = 0;
  // opt not in the paper
  u32 fails;
  u8  found_one = 0;

  /* loop cmps are useless, detect and ignore them */
  u64 s_v0, s_v1;
  u8  s_v0_fixed = 1, s_v1_fixed = 1;
  u8  s_v0_inc = 1, s_v1_inc = 1;
  u8  s_v0_dec = 1, s_v1_dec = 1;

  // fprintf(stderr, "key: %u\n", key);

  for (i = 0; i < loggeds; ++i) {

    fails = 0;

    struct cmp_operands *o = &afl->shm.cmp_map->log[key][i];

    // loop detection code
    if (i == 0) {

      s_v0 = o->v0;
      s_v1 = o->v1;

    } else {

      if (s_v0 != o->v0) { s_v0_fixed = 0; }
      if (s_v1 != o->v1) { s_v1_fixed = 0; }
      if (s_v0 + 1 != o->v0) { s_v0_inc = 0; }
      if (s_v1 + 1 != o->v1) { s_v1_inc = 0; }
      if (s_v0 - 1 != o->v0) { s_v0_dec = 0; }
      if (s_v1 - 1 != o->v1) { s_v1_dec = 0; }
      s_v0 = o->v0;
      s_v1 = o->v1;

    }

    struct cmp_operands *orig_o = &afl->orig_cmp_map->log[key][i];

    // opt not in the paper
    for (j = 0; j < i; ++j) {

      if (afl->shm.cmp_map->log[key][j].v0 == o->v0 &&
          afl->shm.cmp_map->log[key][i].v1 == o->v1) {

        goto cmp_fuzz_next_iter;

      }

    }

    // fprintf(stderr, "Handling: %llx->%llx vs %llx->%llx\n", orig_o->v0,
    // o->v0,
    //        orig_o->v1, o->v1);

    if (taint) {

      t = taint;

      while (t->next) {

        t = t->next;

      }

    } else {

      have_taint = 0;
      t = NULL;

    }

    for (idx = 0; idx < len && fails < 8; ++idx) {

      if (have_taint) {

        if (!t || idx < t->pos) {

          continue;

        } else if (idx == t->pos + t->len - 1) {

          t = t->prev;

        }

      }

      status = 0;
      if (o->v0 != orig_o->v0) {

        if (unlikely(cmp_extend_encoding(afl, h, o->v0, o->v1, orig_o->v0,
                                         orig_o->v1, idx, orig_buf, buf, len, 1,
                                         &status))) {

          return 1;

        }

      }

      if (status == 2) {

        ++fails;

      } else if (status == 1) {

        break;

      }

      status = 0;
      if (o->v1 != orig_o->v1) {

        if (unlikely(cmp_extend_encoding(afl, h, o->v1, o->v0, orig_o->v1,
                                         orig_o->v0, idx, orig_buf, buf, len, 1,
                                         &status))) {

          return 1;

        }

      }

      if (status == 2) {

        ++fails;

      } else if (status == 1) {

        break;

      }

    }

    if (status == 1) { found_one = 1; }

    // If failed, add to dictionary
    if (fails == 8) {

      if (afl->pass_stats[key].total == 0) {

        try_to_add_to_dict(afl, o->v0, SHAPE_BYTES(h->shape));
        try_to_add_to_dict(afl, o->v1, SHAPE_BYTES(h->shape));

      }

    }

  cmp_fuzz_next_iter:
    afl->stage_cur++;

  }

  if (loggeds > 3 && ((s_v0_fixed && s_v1_inc) || (s_v1_fixed && s_v0_inc) ||
                      (s_v0_fixed && s_v1_dec) || (s_v1_fixed && s_v0_dec))) {

    afl->pass_stats[key].total = afl->pass_stats[key].faileds = 0xff;

  }

  if (!found_one && afl->pass_stats[key].faileds < 0xff) {

    afl->pass_stats[key].faileds++;

  }

  if (afl->pass_stats[key].total < 0xff) { afl->pass_stats[key].total++; }

  return 0;

}

static u8 rtn_extend_encoding(afl_state_t *afl, u8 *pattern, u8 *repl,
                              u8 *o_pattern, u32 idx, u8 *orig_buf, u8 *buf,
                              u32 len, u8 *status) {

  u32 i;
  u32 its_len = MIN((u32)32, len - idx);

  u8 save[32];
  memcpy(save, &buf[idx], its_len);

  for (i = 0; i < its_len; ++i) {

    if (pattern[i] != buf[idx + i] || o_pattern[i] != orig_buf[idx + i] ||
        *status == 1) {

      break;

    }

    buf[idx + i] = repl[i];

    if (unlikely(its_fuzz(afl, buf, len, status))) { return 1; }

  }

  memcpy(&buf[idx], save, i);
  return 0;

}

static u8 rtn_fuzz(afl_state_t *afl, u32 key, u8 *orig_buf, u8 *buf, u32 len,
                   struct tainted *taint) {

  struct tainted *   t;
  struct cmp_header *h = &afl->shm.cmp_map->headers[key];
  u32                i, j, idx, have_taint = 1;

  u32 loggeds = h->hits;
  if (h->hits > CMP_MAP_RTN_H) { loggeds = CMP_MAP_RTN_H; }

  u8 status = 0;
  // opt not in the paper
  u32 fails = 0;
  u8  found_one = 0;

  for (i = 0; i < loggeds; ++i) {

    fails = 0;

    struct cmpfn_operands *o =
        &((struct cmpfn_operands *)afl->shm.cmp_map->log[key])[i];

    struct cmpfn_operands *orig_o =
        &((struct cmpfn_operands *)afl->orig_cmp_map->log[key])[i];

    // opt not in the paper
    for (j = 0; j < i; ++j) {

      if (!memcmp(&((struct cmpfn_operands *)afl->shm.cmp_map->log[key])[j], o,
                  sizeof(struct cmpfn_operands))) {

        goto rtn_fuzz_next_iter;

      }

    }

    if (taint) {

      t = taint;
      while (t->next) {

        t = t->next;

      }

    } else {

      have_taint = 0;
      t = NULL;

    }

    for (idx = 0; idx < len && fails < 8; ++idx) {

      if (have_taint) {

        if (!t || idx < t->pos) {

          continue;

        } else if (idx == t->pos + t->len - 1) {

          t = t->prev;

        }

      }

      status = 0;

      if (unlikely(rtn_extend_encoding(afl, o->v0, o->v1, orig_o->v0, idx,
                                       orig_buf, buf, len, &status))) {

        return 1;

      }

      if (status == 2) {

        ++fails;

      } else if (status == 1) {

        break;

      }

      status = 0;

      if (unlikely(rtn_extend_encoding(afl, o->v1, o->v0, orig_o->v1, idx,
                                       orig_buf, buf, len, &status))) {

        return 1;

      }

      if (status == 2) {

        ++fails;

      } else if (status == 1) {

        break;

      }

    }

    if (status == 1) { found_one = 1; }

    // If failed, add to dictionary
    if (fails == 8) {

      if (afl->pass_stats[key].total == 0) {

        maybe_add_auto(afl, o->v0, SHAPE_BYTES(h->shape));
        maybe_add_auto(afl, o->v1, SHAPE_BYTES(h->shape));

      }

    }

  rtn_fuzz_next_iter:
    afl->stage_cur++;

  }

  if (!found_one && afl->pass_stats[key].faileds < 0xff) {

    afl->pass_stats[key].faileds++;

  }

  if (afl->pass_stats[key].total < 0xff) { afl->pass_stats[key].total++; }

  return 0;

}

///// Input to State stage

// afl->queue_cur->exec_cksum
u8 input_to_state_stage(afl_state_t *afl, u8 *orig_buf, u8 *buf, u32 len,
                        u64 exec_cksum) {

  u8 r = 1;
  if (unlikely(!afl->orig_cmp_map)) {

    afl->orig_cmp_map = ck_alloc_nozero(sizeof(struct cmp_map));

  }

  if (unlikely(!afl->pass_stats)) {

    afl->pass_stats = ck_alloc(sizeof(struct afl_pass_stat) * CMP_MAP_W);

  }

  // do it manually, forkserver clear only afl->fsrv.trace_bits
  memset(afl->shm.cmp_map->headers, 0, sizeof(afl->shm.cmp_map->headers));

  if (unlikely(common_fuzz_cmplog_stuff(afl, buf, len))) { return 1; }

  memcpy(afl->orig_cmp_map, afl->shm.cmp_map, sizeof(struct cmp_map));

  struct tainted *taint = NULL;

  if (unlikely(colorization(afl, buf, len, exec_cksum, &taint))) { return 1; }

  struct tainted *t = taint;
  while (t) {

    // fprintf(stderr, "T: pos=%u len=%u\n", t->pos, t->len);
    t = t->next;

  }

  // do it manually, forkserver clear only afl->fsrv.trace_bits
  memset(afl->shm.cmp_map->headers, 0, sizeof(afl->shm.cmp_map->headers));

  if (unlikely(common_fuzz_cmplog_stuff(afl, buf, len))) { return 1; }

  u64 orig_hit_cnt, new_hit_cnt;
  u64 orig_execs = afl->fsrv.total_execs;
  orig_hit_cnt = afl->queued_paths + afl->unique_crashes;

  afl->stage_name = "input-to-state";
  afl->stage_short = "its";
  afl->stage_max = 0;
  afl->stage_cur = 0;

  u32 k;
  for (k = 0; k < CMP_MAP_W; ++k) {

    if (!afl->shm.cmp_map->headers[k].hits) { continue; }

    if (/*afl->pass_stats[k].total &&
        (rand_below(afl, afl->pass_stats[k].total) >=
             afl->pass_stats[k].faileds ||*/
        afl->pass_stats[k].total == 0xff) {

      afl->shm.cmp_map->headers[k].hits = 0;  // ignore this cmp

    }

    if (afl->shm.cmp_map->headers[k].type == CMP_TYPE_INS) {

      afl->stage_max +=
          MIN((u32)(afl->shm.cmp_map->headers[k].hits), (u32)CMP_MAP_H);

    } else {

      afl->stage_max +=
          MIN((u32)(afl->shm.cmp_map->headers[k].hits), (u32)CMP_MAP_RTN_H);

    }

  }

  for (k = 0; k < CMP_MAP_W; ++k) {

    if (!afl->shm.cmp_map->headers[k].hits) { continue; }

    if (afl->shm.cmp_map->headers[k].type == CMP_TYPE_INS) {

      if (unlikely(cmp_fuzz(afl, k, orig_buf, buf, len, taint))) {

        goto exit_its;

      }

    } else {

      if (unlikely(rtn_fuzz(afl, k, orig_buf, buf, len, taint))) {

        goto exit_its;

      }

    }

  }

  r = 0;

exit_its:
  new_hit_cnt = afl->queued_paths + afl->unique_crashes;
  afl->stage_finds[STAGE_ITS] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_ITS] += afl->fsrv.total_execs - orig_execs;

  memcpy(buf, orig_buf, len);

  return r;

}

