/*
   american fuzzy lop++ - weizz implementation on top of cmplog
   ------------------------------------------------------------

   Originally written by Andrea Fioraldi

   Now maintained by Marc Heuse <mh@mh-sec.de>,
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

#include "afl-fuzz.h"

#define SIMILARITY_EPSILON 4

enum {

  BUILD_STRATEGY_RAND,
  BUILD_STRATEGY_SIMILAR,
  BUILD_STRATEGY_INCREMENTAL,
  
  BUILD_STRATEGIES

};

static u8 seek_chunk_end(afl_state_t *afl, struct afl_cmp_tag* tags, u32 fields_cnt, u32 start_tag_field, u32 i, u32 len, u32* end, u32* chunk_fields, u8 build_strategy) {

  u32 end_tag_field;

  u32 cur_field = start_tag_field;
  u32 last_seen = tags[i].id;

  u8 found = 0;

  /* Search for the end */
  switch (build_strategy) {
  
    case BUILD_STRATEGY_RAND: { // random tag end
    
      end_tag_field = cur_field + rand_below(afl, fields_cnt - cur_field);
      for (; i < len; ++i) {
      
        if (last_seen != tags[i].id) ++cur_field;
        last_seen = tags[i].id;
      
        if (cur_field == end_tag_field) {
        
          u32 end_id = tags[i].id;
          while (i < len && tags[i].id == end_id) i++;

          *end = i;
          found = 1;
          break;
        
        }
      
      }
      
      break;
    
    }
    
    case BUILD_STRATEGY_SIMILAR: { // similar tag end
    
      u32 start_id = last_seen;
      for (; i < len; ++i) {
      
        if (last_seen != tags[i].id) {
        
          if (abs((s32)tags[i].id - (s32)start_id) < SIMILARITY_EPSILON) {
          
            *end = i;
            found = 1;
            end_tag_field = cur_field;
            break;
          
          }
          
          ++cur_field;
          
        }
        last_seen = tags[i].id;
      
      }
      
      break;
    
    }
    
    case BUILD_STRATEGY_INCREMENTAL: { // incremental
    
      u32 start_cnt = tags[i].cnt;
      u32 start_parent = tags[i].parent_id;

      for (; i < len; ++i) {
          
        if (last_seen != tags[i].id) {

          ++cur_field;
          
          if (tags[i].cnt == 0) {
            
            // pick untaggeds with a probability
            if (rand_below(afl, 2)) break;
          
          } else if (tags[i].id == start_parent) {
          
            // do nothing atm
          
          } else if (tags[i].cnt < start_cnt) {
          
            // 1 byte tolerance
            if (i +1 >= len || tags[i +1].cnt < start_cnt)
              break;
          
          }
          
        }
        last_seen = tags[i].id;
      
      }
      
      *end = i;
      found = 1;
      end_tag_field = cur_field;

      break;
    
    }
  
  }
  
  *chunk_fields = end_tag_field - start_tag_field +1;
  
  return !found;

}

static u8 get_chunk_of_type(afl_state_t *afl, u32 type, struct afl_cmp_tag* tags, u32 len, u32* start, u32* end, u32* chunk_fields, u8 build_strategy) {

  if (len == 0) return 1;

  u32 cur_field = 0;
  u32 typed_fields = 0;
  
  /* Search for a start field */
  u32 i;
  u32 last_seen = tags[0].id;
  for (i = 0; i < len; ++i) {
  
    if (last_seen != tags[i].id) {
    
      ++cur_field;
      if (tags[i].id == type) ++typed_fields;
      
    }
    
    last_seen = tags[i].id;
  
  }
  
  if (typed_fields == 0) return 1;
  
  u32 fields_cnt = cur_field +1;
  cur_field = 0;
  
  u32 start_tag_typed_field = rand_below(afl, typed_fields);
  u32 start_tag_field = 0;
  last_seen = tags[0].id;
  typed_fields = 0;

  for (i = 0; i < len; ++i) {
  
    if (last_seen != tags[i].id) {
    
      ++cur_field;
      if (tags[i].id == type) ++typed_fields;
      
    }
    
    last_seen = tags[i].id;
    
    if (typed_fields == start_tag_typed_field) {
    
      start_tag_field = cur_field;
      *start = i;
      break;
    
    }
  
  }
  
  return seek_chunk_end(afl, tags, fields_cnt, start_tag_field, i, len, end, chunk_fields, build_strategy);
  
}

static u8 get_chunk_with_parent(afl_state_t *afl, u32 parent, struct afl_cmp_tag* tags, u32 len, u32* start, u32* end, u32* chunk_fields, u8 build_strategy) {

  if (len == 0) return 1;

  u32 cur_field = 0;
  u32 typed_fields = 0;
  
  /* Search for a start field */
  u32 i;
  u32 last_seen = tags[0].id;
  for (i = 0; i < len; ++i) {
  
    if (last_seen != tags[i].id) {
    
      ++cur_field;
      if (tags[i].parent_id == parent) ++typed_fields;
      
    }
    
    last_seen = tags[i].id;
  
  }
  
  if (typed_fields == 0) return 1;
  
  u32 fields_cnt = cur_field +1;
  cur_field = 0;
  
  u32 start_tag_typed_field = rand_below(afl, typed_fields);
  u32 start_tag_field = 0;
  last_seen = tags[0].id;
  typed_fields = 0;

  for (i = 0; i < len; ++i) {
  
    if (last_seen != tags[i].id) {
    
      ++cur_field;
      if (tags[i].parent_id == parent) ++typed_fields;
      
    }
    
    last_seen = tags[i].id;
    
    if (typed_fields == start_tag_typed_field) {
    
      start_tag_field = cur_field;
      *start = i;
      break;
    
    }
  
  }
  
  return seek_chunk_end(afl, tags, fields_cnt, start_tag_field, i, len, end, chunk_fields, build_strategy);
  
}


static u8 get_random_chunk(afl_state_t *afl, struct afl_cmp_tag* tags, u32 fields_cnt, u32 len, u32* start, u32* end, u32* chunk_fields, u8 build_strategy) {

  if (len == 0) return 1;

  u32 start_tag_field = rand_below(afl, fields_cnt);
  u32 cur_field = 0;
  
  u8 found = 0;
  
  /* Search for a start field */
  u32 i;
  u32 last_seen = tags[0].id;
  for (i = 0; i < len; ++i) {
  
    if (last_seen != tags[i].id) ++cur_field;
    last_seen = tags[i].id;
  
    if (cur_field == start_tag_field) {
    
      if (tags[i].cnt == 0) { // untagged
      
        while (i < len && tags[i].cnt == 0) i++;
        if (i < len) {
        
          ++start_tag_field;
          ++cur_field;

        } else return 1; // error, untagged
      
      }
      
      *start = i;
      found = 1;
      break;
    
    }
  
  }
  
  if (!found) return 1;

  return seek_chunk_end(afl, tags, fields_cnt, start_tag_field, i, len, end, chunk_fields, build_strategy);

}

u8 weizz_mutation(afl_state_t *afl, struct afl_cmp_tag* tags, u32* fields_cnt, u8 *buf, u32* temp_len) {

  u8 structure_changed = 0;
  u8 build_strategy = rand_below(afl, BUILD_STRATEGIES); // different algo to build chunks
  
  switch (rand_below(afl, 3)) {
  
    case 0: { // delete a chunk
    
      u32 del_from = 0, del_to = 0;

      if (*temp_len < 2) break;
      
      u32 chunk_fields = 0;
      if (get_random_chunk(afl, tags, *fields_cnt, *temp_len, &del_from, &del_to, &chunk_fields, build_strategy))
          break;

      // avoid to have an empty buf
      if (del_to - del_from == (*temp_len)) break;

      memmove(buf + del_from, buf + del_to, (*temp_len) - del_to);
      memmove(tags + del_from, tags + del_to, ((*temp_len) - del_to) * sizeof(struct afl_cmp_tag));
      
      (*temp_len) -= (del_to - del_from);

      structure_changed = 1;
      *fields_cnt -= chunk_fields;

      break;
    
    }
  
    case 1: { // splice two chunks
    
      if (afl->queued_paths < 2) break;

      /* Pick a random queue entry and seek to it. */

      u32 tid;
      do
        tid = rand_below(afl, afl->queued_paths);
      while (tid == afl->current_entry);

      struct queue_entry *target = afl->queue_buf[tid];

      /* Make sure that the target has a reasonable length. */

      while (target && !target->weizz_tags && (target->len < 2 || target == afl->queue_cur))
        target = target->next;

      if (!target || !target->weizz_tags) break;
      
      u32 dest_fields = 0, dest_start, dest_end;
      if (get_random_chunk(afl, tags, *fields_cnt, *temp_len, &dest_start, &dest_end, &dest_fields, build_strategy))
          break;

      u32 chunk_type = tags[dest_start].id;

      /* Read the testcase into a new buffer. */

      s32 fd = open(target->fname, O_RDONLY);

      if (unlikely(fd < 0)) {

        PFATAL("Unable to open '%s'", target->fname);

      }

      u32 new_len = target->len;
      u8 *new_buf = afl_realloc(AFL_BUF_PARAM(in_scratch), new_len);
      if (unlikely(!new_buf)) { PFATAL("alloc"); }

      ck_read(fd, new_buf, new_len, target->fname);

      close(fd);
      
      u32 src_fields = 0, src_start = 0, src_end = 0;
      if (get_chunk_of_type(afl, chunk_type, target->weizz_tags, new_len, &src_start, &src_end, &src_fields, build_strategy))
          break;

      u32 dest_len = dest_end - dest_start;
      u32 src_len = src_end - src_start;
      
      if (*temp_len - dest_len + src_len > MAX_FILE)
        break;
      
      buf = afl_realloc(AFL_BUF_PARAM(out), *temp_len - dest_len + src_len);
      if (unlikely(!buf)) { PFATAL("alloc"); }
      
      tags = afl_realloc(AFL_BUF_PARAM(tags), (*temp_len - dest_len + src_len) * sizeof(struct afl_cmp_tag));
      if (unlikely(!tags)) { PFATAL("alloc"); }

      /* Tail */
      memmove(buf + dest_start + src_len, buf + dest_end, *temp_len - dest_end);
      memmove(tags + dest_start + src_len, tags + dest_end, (*temp_len - dest_end) * sizeof(struct afl_cmp_tag));

      /* Spliced part */
      memcpy(buf + dest_start, new_buf + src_start, src_len);
      memcpy(tags + dest_start, target->weizz_tags + src_start, src_len * sizeof(struct afl_cmp_tag));

      *temp_len -= dest_len;
      *temp_len += src_len;

      structure_changed = 1;
      *fields_cnt -= dest_fields;
      *fields_cnt += src_fields;

      break;
    
    }
  
    case 2: {  // add a chunk
    
      if (afl->queued_paths < 2) break;

      /* Pick a random queue entry and seek to it. */

      u32 tid;
      do
        tid = rand_below(afl, afl->queued_paths);
      while (tid == afl->current_entry);

      struct queue_entry *target = afl->queue_buf[tid];

      /* Make sure that the target has a reasonable length. */

      while (target && !target->weizz_tags && (target->len < 2 || target == afl->queue_cur))
        target = target->next;

      if (!target || !target->weizz_tags) break;
      
      u32 dest_fields = 0, dest_start, dest_end;
      if (get_random_chunk(afl, tags, *fields_cnt, *temp_len, &dest_start, &dest_end, &dest_fields, build_strategy))
          break;

      u32 chunk_parent = tags[dest_start].parent_id;

      /* Read the testcase into a new buffer. */

      s32 fd = open(target->fname, O_RDONLY);

      if (unlikely(fd < 0)) {

        PFATAL("Unable to open '%s'", target->fname);

      }

      u32 new_len = target->len;
      u8 *new_buf = afl_realloc(AFL_BUF_PARAM(in_scratch), new_len);
      if (unlikely(!new_buf)) { PFATAL("alloc"); }

      ck_read(fd, new_buf, new_len, target->fname);

      close(fd);
      
      u32 src_fields = 0, src_start = 0, src_end = 0;
      if (get_chunk_with_parent(afl, chunk_parent, target->weizz_tags, new_len, &src_start, &src_end, &src_fields, build_strategy))
          break;

      u32 src_len = src_end - src_start;
      
      if (*temp_len + src_len > MAX_FILE)
        break;
      
      u32 insert_at;
      if (rand_below(afl, 2)) insert_at = dest_start;
      else insert_at = dest_end;
      
      buf = afl_realloc(AFL_BUF_PARAM(out), *temp_len + src_len);
      if (unlikely(!buf)) { PFATAL("alloc"); }
      
      tags = afl_realloc(AFL_BUF_PARAM(tags), (*temp_len + src_len) * sizeof(struct afl_cmp_tag));
      if (unlikely(!tags)) { PFATAL("alloc"); }

      /* Tail */
      memmove(buf + insert_at + src_len, buf + insert_at, *temp_len - insert_at);
      memmove(tags + insert_at + src_len, tags + insert_at, (*temp_len - insert_at) * sizeof(struct afl_cmp_tag));

      /* Added part */
      memcpy(buf + insert_at, new_buf + src_start, src_len);
      memcpy(tags + insert_at, target->weizz_tags + src_start, src_len * sizeof(struct afl_cmp_tag));

      *temp_len += src_len;

      structure_changed = 1;
      *fields_cnt += src_fields;

      break;
    
    }
  
  }

  return structure_changed;

}

u32 weizz_count_fields(struct afl_cmp_tag* tags, u32 len) {

  if (len == 0) return 0;

  u32 cur_field = 0;
  
  u32 i;
  u32 last_seen = tags[0].id;
  for (i = 0; i < len; ++i) {
  
    if (last_seen != tags[i].id) ++cur_field;
    last_seen = tags[i].id;
  
  }
  
  return cur_field +1;

}
