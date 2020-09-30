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

// TODO get rid of qsort_r, it is GNU only
#define _GNU_SOURCE // for qsort_r

#include <limits.h>
#include "afl-fuzz.h"
#include "cmplog.h"

///// Colorization

struct range {

  u32           start;
  u32           end;
  struct range *next;

};

static struct range *add_range(struct range *ranges, u32 start, u32 end) {

  struct range *r = ck_alloc_nozero(sizeof(struct range));
  r->start = start;
  r->end = end;
  r->next = ranges;
  return r;

}

static struct range *pop_biggest_range(struct range **ranges) {

  struct range *r = *ranges;
  struct range *prev = NULL;
  struct range *rmax = NULL;
  struct range *prev_rmax = NULL;
  u32           max_size = 0;

  while (r) {

    u32 s = r->end - r->start;
    if (s >= max_size) {

      max_size = s;
      prev_rmax = prev;
      rmax = r;

    }

    prev = r;
    r = r->next;

  }

  if (rmax) {

    if (prev_rmax) {

      prev_rmax->next = rmax->next;

    } else {

      *ranges = rmax->next;

    }

  }

  return rmax;

}

static u8 get_exec_checksum(afl_state_t *afl, u8 *buf, u32 len, u64 *cksum) {

  if (unlikely(common_fuzz_stuff(afl, buf, len))) { return 1; }

  *cksum = hash64(afl->fsrv.trace_bits, afl->fsrv.map_size, HASH_CONST);
  return 0;

}

static void rand_replace(afl_state_t *afl, u8 *buf, u32 len) {

  u32 i;
  for (i = 0; i < len; ++i) {

    buf[i] = rand_below(afl, 256);

  }

}

static u8 colorization(afl_state_t *afl, u8 *buf, u32 len, u64 exec_cksum) {

  struct range *ranges = add_range(NULL, 0, len);
  u8 *          backup = ck_alloc_nozero(len);

  u8 needs_write = 0;

  u64 orig_hit_cnt, new_hit_cnt;
  orig_hit_cnt = afl->queued_paths + afl->unique_crashes;

  afl->stage_name = "colorization";
  afl->stage_short = "colorization";
  afl->stage_max = 1000;

  struct range *rng = NULL;
  afl->stage_cur = 0;
  while ((rng = pop_biggest_range(&ranges)) != NULL &&
         afl->stage_cur < afl->stage_max) {

    u32 s = rng->end - rng->start;

    if (s != 0) {

      /* Range not empty */

      memcpy(backup, buf + rng->start, s);
      rand_replace(afl, buf + rng->start, s);

      u64 cksum;
      u64 start_us = get_cur_time_us();
      if (unlikely(get_exec_checksum(afl, buf, len, &cksum))) {

        goto checksum_fail;

      }

      u64 stop_us = get_cur_time_us();

      /* Discard if the mutations change the paths or if it is too decremental
        in speed */
      if (cksum != exec_cksum ||
          ((stop_us - start_us > 2 * afl->queue_cur->exec_us) &&
           likely(!afl->fixed_seed))) {

        ranges = add_range(ranges, rng->start, rng->start + s / 2);
        ranges = add_range(ranges, rng->start + s / 2 + 1, rng->end);
        memcpy(buf + rng->start, backup, s);

      } else {

        needs_write = 1;

      }

    }

    ck_free(rng);
    rng = NULL;
    ++afl->stage_cur;

  }

  if (afl->stage_cur < afl->stage_max) { afl->queue_cur->fully_colorized = 1; }

  new_hit_cnt = afl->queued_paths + afl->unique_crashes;
  afl->stage_finds[STAGE_COLORIZATION] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_COLORIZATION] += afl->stage_cur;
  ck_free(backup);

  ck_free(rng);
  rng = NULL;

  while (ranges) {

    rng = ranges;
    ranges = rng->next;
    ck_free(rng);
    rng = NULL;

  }

  // save the input with the high entropy

  if (needs_write) {

    s32 fd;

    if (afl->no_unlink) {

      fd = open(afl->queue_cur->fname, O_WRONLY | O_CREAT | O_TRUNC, 0600);

    } else {

      unlink(afl->queue_cur->fname);                       /* ignore errors */
      fd = open(afl->queue_cur->fname, O_WRONLY | O_CREAT | O_EXCL, 0600);

    }

    if (fd < 0) { PFATAL("Unable to create '%s'", afl->queue_cur->fname); }

    ck_write(fd, buf, len, afl->queue_cur->fname);
    afl->queue_cur->len = len;  // no-op, just to be 100% safe

    close(fd);

  }

  return 0;

checksum_fail:
  if (rng) { ck_free(rng); }
  ck_free(backup);

  while (ranges) {

    rng = ranges;
    ranges = rng->next;
    ck_free(rng);
    rng = NULL;

  }

  // TODO: clang notices a _potential_ leak of mem pointed to by rng

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
                              u64 pattern, u64 repl, u64 o_pattern, u32 idx,
                              u8 *orig_buf, u8 *buf, u32 len, u8 do_reverse,
                              u8 *status, struct afl_cmp_tag* tags, u16 parent_cmp_id, u8 must_skip) {

  if (!buf) { FATAL("BUG: buf was NULL. Please report this.\n"); }

  u64 *buf_64 = (u64 *)&buf[idx];
  u32 *buf_32 = (u32 *)&buf[idx];
  u16 *buf_16 = (u16 *)&buf[idx];
  u8 * buf_8 = &buf[idx];
  u64 *o_buf_64 = (u64 *)&orig_buf[idx];
  u32 *o_buf_32 = (u32 *)&orig_buf[idx];
  u16 *o_buf_16 = (u16 *)&orig_buf[idx];
  u8 * o_buf_8 = &orig_buf[idx];

  u32 its_len = len - idx;
  // *status = 0;

  u8 *               endptr;
  u8                 use_num = 0, use_unum = 0;
  unsigned long long unum;
  long long          num;
  
  u8 is_ascii = afl->queue_cur->is_ascii;

  if (is_ascii) {

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

#define TAG_ASSIGN(idx) \
  if (tags[idx].cnt == 0 || (SHAPE_BYTES(h->shape) >= 4 && h->shape > tags[idx].shape)) { \
    tags[idx].cnt = h->cnt; \
    tags[idx].id = h->id; \
    tags[idx].parent_id = parent_cmp_id; \
    tags[idx].shape = h->shape; \
  }

  if (SHAPE_BYTES(h->shape) >= 8) {

    if (its_len >= 8 && *buf_64 == pattern && *o_buf_64 == o_pattern) {

      if (afl->fmtrev_enabled && !is_ascii) {
      
        // TODO verify real correspondence executin the cmplog binary with a bitflip
      
        TAG_ASSIGN(idx)
        TAG_ASSIGN(idx +1)
        TAG_ASSIGN(idx +2)
        TAG_ASSIGN(idx +3)
        TAG_ASSIGN(idx +4)
        TAG_ASSIGN(idx +5)
        TAG_ASSIGN(idx +6)
        TAG_ASSIGN(idx +7)

        afl->parent_cmp_id = h->id;
      
      }

      if (!must_skip && *status != 1) {

        *buf_64 = repl;
        if (unlikely(its_fuzz(afl, buf, len, status))) { return 1; }
        *buf_64 = pattern;
        
      }

    }

    // reverse encoding
    if (do_reverse) {

      if (unlikely(cmp_extend_encoding(afl, h, SWAP64(pattern), SWAP64(repl),
                                       SWAP64(o_pattern), idx, orig_buf, buf,
                                       len, 0, status, tags, parent_cmp_id, must_skip))) {

        return 1;

      }

    }

  }

  if (SHAPE_BYTES(h->shape) >= 4) {

    if (its_len >= 4 && *buf_32 == (u32)pattern &&
        *o_buf_32 == (u32)o_pattern) {

      if (afl->fmtrev_enabled && !is_ascii) {
      
        // TODO verify real correspondence executin the cmplog binary with a bitflip
      
        TAG_ASSIGN(idx)
        TAG_ASSIGN(idx +1)
        TAG_ASSIGN(idx +2)
        TAG_ASSIGN(idx +3)

        afl->parent_cmp_id = h->id;
      
      }

      if (!must_skip && *status != 1) {

        *buf_32 = (u32)repl;
        if (unlikely(its_fuzz(afl, buf, len, status))) { return 1; }
        *buf_32 = pattern;

      }

    }

    // reverse encoding
    if (do_reverse) {

      if (unlikely(cmp_extend_encoding(afl, h, SWAP32(pattern), SWAP32(repl),
                                       SWAP32(o_pattern), idx, orig_buf, buf,
                                       len, 0, status, tags, parent_cmp_id, must_skip))) {

        return 1;

      }

    }

  }

  if (SHAPE_BYTES(h->shape) >= 2) {

    if (its_len >= 2 && *buf_16 == (u16)pattern &&
        *o_buf_16 == (u16)o_pattern) {

      if (afl->fmtrev_enabled && !is_ascii) {
      
        // TODO verify real correspondence executin the cmplog binary with a bitflip
      
        TAG_ASSIGN(idx)
        TAG_ASSIGN(idx +1)

        afl->parent_cmp_id = h->id;
      
      }

      if (!must_skip && *status != 1) {

        *buf_16 = (u16)repl;
        if (unlikely(its_fuzz(afl, buf, len, status))) { return 1; }
        *buf_16 = (u16)pattern;

      }

    }

    // reverse encoding
    if (do_reverse) {

      if (unlikely(cmp_extend_encoding(afl, h, SWAP16(pattern), SWAP16(repl),
                                       SWAP16(o_pattern), idx, orig_buf, buf,
                                       len, 0, status, tags, parent_cmp_id, must_skip))) {

        return 1;

      }

    }

  }

  if (SHAPE_BYTES(h->shape) >= 1) {

    if (its_len >= 1 && *buf_8 == (u8)pattern && *o_buf_8 == (u8)o_pattern) {

      if (afl->fmtrev_enabled && !is_ascii) {
      
        // TODO verify real correspondence executin the cmplog binary with a bitflip
      
        TAG_ASSIGN(idx)

        afl->parent_cmp_id = h->id;
      
      }

      if (!must_skip && *status != 1) {

        *buf_8 = (u8)repl;
        if (unlikely(its_fuzz(afl, buf, len, status))) { return 1; }
        *buf_8 = (u8)pattern;
        
      }

    }

  }

#undef TAG_ASSIGN

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

static u8 cmp_fuzz(afl_state_t *afl, struct cmp_map* cmp_map, u32 key, u8 *orig_buf, u8 *buf, u32 len, struct afl_cmp_tag* tags, u8 must_skip) {

  struct cmp_header *h = &cmp_map->headers[key];
  u32                i, j, idx;

  u32 loggeds = h->hits;
  if (h->hits > CMP_MAP_H) { loggeds = CMP_MAP_H; }

  u8 status = 0;
  // opt not in the paper
  u32 fails;
  u8  found_one = 0;
  u8  failed_once = 0;

  /* loop cmps are useless, detect and ignore them */
  u64 s_v0, s_v1;
  u8  s_v0_fixed = 1, s_v1_fixed = 1;
  u8  s_v0_inc = 1, s_v1_inc = 1;
  u8  s_v0_dec = 1, s_v1_dec = 1;

  u16 parent_cmp_id = afl->parent_cmp_id;

  for (i = 0; i < loggeds; ++i) {

    fails = 0;

    struct cmp_operands *o = &cmp_map->log[key][i];

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

      if (cmp_map->log[key][j].v0 == o->v0 &&
          cmp_map->log[key][i].v1 == o->v1) {

        goto cmp_fuzz_next_iter;

      }

    }
    
    for (idx = 0; idx < len && fails < 8; ++idx) {

      status = 0;
      if (unlikely(cmp_extend_encoding(afl, h, o->v0, o->v1, orig_o->v0, idx, orig_buf, buf, len, 1, &status, tags, parent_cmp_id, must_skip))) {

        return 1;

      }

      if (status == 2) {

        ++fails;

      } else if (status == 1) {

        break;

      }

      status = 0;
      if (unlikely(cmp_extend_encoding(afl, h, o->v1, o->v0, orig_o->v1, idx, orig_buf, buf, len, 1, &status, tags, parent_cmp_id, must_skip))) {

        return 1;

      }

      if (status == 2) {

        ++fails;

      } else if (status == 1) {

        break;

      }

    }

    if (status == 1) found_one = 1;
    if (fails) failed_once = 1;

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

  if (!must_skip) {

    if (!found_one && afl->pass_stats[key].faileds < 0xff) {

      afl->pass_stats[key].faileds++;

    }
    
    if (!found_one && !failed_once && afl->pass_stats[key].not_i2s < 0xff) {

      afl->pass_stats[key].not_i2s++;

    }

    if (afl->pass_stats[key].total < 0xff) { afl->pass_stats[key].total++; }
  
  }

  return 0;

}

static u8 rtn_extend_encoding(afl_state_t *afl, u8 *pattern, u8 *repl,
                              u8 *o_pattern, u32 idx, u8 *orig_buf, u8 *buf,
                              u32 len, u8 *status) {

  u32 i;
  u32 its_len = MIN((u32)32, len - idx);

  u8 save[32];
  memcpy(save, &buf[idx], its_len);

  *status = 0;

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

static u8 rtn_fuzz(afl_state_t *afl, struct cmp_map* cmp_map, u32 key, u8 *orig_buf, u8 *buf, u32 len) {

  struct cmp_header *h = &cmp_map->headers[key];
  u32                i, j, idx;

  u32 loggeds = h->hits;
  if (h->hits > CMP_MAP_RTN_H) { loggeds = CMP_MAP_RTN_H; }

  u8 status = 0;
  // opt not in the paper
  u32 fails = 0;
  u8  found_one = 0;

  for (i = 0; i < loggeds; ++i) {

    fails = 0;

    struct cmpfn_operands *o =
        &((struct cmpfn_operands *)cmp_map->log[key])[i];

    struct cmpfn_operands *orig_o =
        &((struct cmpfn_operands *)afl->orig_cmp_map->log[key])[i];

    // opt not in the paper
    for (j = 0; j < i; ++j) {

      if (!memcmp(&((struct cmpfn_operands *)cmp_map->log[key])[j], o,
                  sizeof(struct cmpfn_operands))) {

        goto rtn_fuzz_next_iter;

      }

    }

    for (idx = 0; idx < len && fails < 8; ++idx) {

      if (unlikely(rtn_extend_encoding(afl, o->v0, o->v1, orig_o->v0, idx,
                                       orig_buf, buf, len, &status))) {

        return 1;

      }

      if (status == 2) {

        ++fails;

      } else if (status == 1) {

        break;

      }

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

/*
TODO

save in another tmp map the cmp map after colorization. use that map in the old
code, not the one in shared mem (done)

sort cmps in temporal order (done)

do not skip of pass stats fail, but pass a boolean and skip the executions

use another flag similar to pass stats but for i2s, call it i2s_stats and use it
like old pass stats (done)

on a match, before executin the put, bitflip the pattern and execute the cmplog
binary. if we see the same change in the cmp operand, taint the pattern.

apply weizz tagging.

add cnt field collection to qemu mode.

*/

static int compare_cmp_cnt(const void *p1, const void *p2, void *arg) {

  struct cmp_map* m = arg;
  return m->headers[*(u16*)p1].cnt - m->headers[*(u16*)p2].cnt;

}

// afl->queue_cur->exec_cksum
u8 input_to_state_stage(afl_state_t *afl, u8 *orig_buf, u8 *buf, u32 len,
                        u64 exec_cksum) {

  u8 r = 1;
  struct cmp_map* cmp_map = NULL;
  
  struct afl_cmp_tag* tags = ck_alloc(sizeof(struct afl_cmp_tag) * len);

  if (afl->orig_cmp_map == NULL) {

    afl->orig_cmp_map = ck_alloc_nozero(sizeof(struct cmp_map));

  }

  if (afl->pass_stats == NULL) {

    afl->pass_stats = ck_alloc(sizeof(struct afl_pass_stat) * CMP_MAP_W);

  }

  // do it manually, forkserver clear only afl->fsrv.trace_bits
  memset(afl->shm.cmp_map->headers, 0, sizeof(afl->shm.cmp_map->headers));

  if (unlikely(common_fuzz_cmplog_stuff(afl, buf, len))) { return 1; }

  memcpy(afl->orig_cmp_map, afl->shm.cmp_map, sizeof(struct cmp_map));

  if (unlikely(colorization(afl, buf, len, exec_cksum))) { return 1; }

  // do it manually, forkserver clear only afl->fsrv.trace_bits
  memset(afl->shm.cmp_map->headers, 0, sizeof(afl->shm.cmp_map->headers));

  if (unlikely(common_fuzz_cmplog_stuff(afl, buf, len))) { return 1; }
  
  cmp_map = ck_alloc_nozero(sizeof(struct cmp_map));
  memcpy(cmp_map, afl->shm.cmp_map, sizeof(struct cmp_map));
  
  u64 orig_hit_cnt, new_hit_cnt;
  u64 orig_execs = afl->fsrv.total_execs;
  orig_hit_cnt = afl->queued_paths + afl->unique_crashes;

  afl->stage_name = "input-to-state";
  afl->stage_short = "its";
  afl->stage_max = 0;
  afl->stage_cur = 0;

  u16 sorted_cmps[CMP_MAP_W];
  u32 sorted_cmps_len = 0;

  u32 k;
  for (k = 0; k < CMP_MAP_W; ++k) {

    if (!cmp_map->headers[k].hits) { continue; }

    sorted_cmps[sorted_cmps_len++] = (u16)k;

    if (afl->pass_stats[k].total) {
    
      if (afl->pass_stats[k].not_i2s > 2)
        cmp_map->headers[k].hits = 0;  // ignore this cmp
    
      if (afl->pass_stats[k].total == 0xff || rand_below(afl, afl->pass_stats[k].total) >= afl->pass_stats[k].faileds)
         afl->shm.cmp_map->headers[k].hits = 0;  // skip fuzz this cmp
    
    }

    if (cmp_map->headers[k].type == CMP_TYPE_INS) {

      afl->stage_max +=
          MIN((u32)(cmp_map->headers[k].hits), (u32)CMP_MAP_H);

    } else {

      afl->stage_max +=
          MIN((u32)(cmp_map->headers[k].hits), (u32)CMP_MAP_RTN_H);

    }

  }
  
  qsort_r(sorted_cmps, sorted_cmps_len, sizeof(u16), compare_cmp_cnt, cmp_map);

  u32 i;
  for (i = 0; i < sorted_cmps_len; ++i) {

    k = sorted_cmps[i];

    if (!cmp_map->headers[k].hits) continue;

    u8 must_skip = !afl->shm.cmp_map->headers[k].hits && cmp_map->headers[k].hits;

    if (cmp_map->headers[k].type == CMP_TYPE_INS) {

      if (unlikely(cmp_fuzz(afl, cmp_map, k, orig_buf, buf, len, tags, must_skip)))
        goto exit_its;

    } else if (!must_skip) { // TODO weizz for subroutines

      if (unlikely(rtn_fuzz(afl, cmp_map, k, orig_buf, buf, len)))
        goto exit_its;

    }

  }

  r = 0;

  // debgug print tags
  for (i = 0; i < len; ++i) {
    fprintf(stderr, "'%c' %x [%d %d %d]\n", buf[i], buf[i], tags[i].id, tags[i].cnt, SHAPE_BYTES(tags[i].shape));
  }
  fprintf(stderr, "=====================\n");

exit_its:
  new_hit_cnt = afl->queued_paths + afl->unique_crashes;
  afl->stage_finds[STAGE_ITS] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_ITS] += afl->fsrv.total_execs - orig_execs;
  
  if (cmp_map) ck_free(cmp_map);

  memcpy(orig_buf, buf, len);
  
  if (r) ck_free(tags);

  return r;

}

