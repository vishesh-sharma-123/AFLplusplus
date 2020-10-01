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

enum {

  BUILD_STRATEGY_RAND,
  BUILD_STRATEGY_SIMILAR,
  BUILD_STRATEGY_INCREMENTAL,
  
  BUILD_STRATEGIES

};

static u8 get_random_chunk(afl_state_t *afl, struct afl_cmp_tag* tags, u32 fields_cnt, u32 len, u32* start, u32* end, u8 build_strategy) {

  if (len == 0) return 1;

  u32 start_tag_field = rand_below(afl, fields_cnt);
  u32 cur_field = 0;
  
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
      break;
    
    }
  
  }

  /* Search for the end */
  switch (build_strategy) {
  
    case BUILD_STRATEGY_RAND: { // random tag end
    
      u32 end_tag_field = cur_field + rand_below(afl, fields_cnt - cur_field);
      for (; i < len; ++i) {
      
        if (last_seen != tags[i].id) ++cur_field;
        last_seen = tags[i].id;
      
        if (cur_field == end_tag_field) {
        
          u32 end_id = tags[i].id;
          while (i < len && tags[i].id == end_id) i++;

          *end = i;
          break;
        
        }
      
      }
    
      break;
    
    }
    
    case BUILD_STRATEGY_SIMILAR: { // similar tag end
    
      return 1;
      break;
    
    }
    
    case BUILD_STRATEGY_INCREMENTAL: { // incremental
    
      return 1;
      break;
    
    }
  
  }
  
  return 0;

}

u8 weizz_mutation(afl_state_t *afl, struct afl_cmp_tag* tags, u32 fields_cnt, u8 *buf, u32* temp_len) {

  u8 structure_changed = 0;
  u8 build_strategy = rand_below(afl, BUILD_STRATEGIES); // different algo to build chunks
  
  switch (rand_below(afl, 3)) {
  
    case 0: { // delete a chunk
    
      u32 del_from = 0, del_to = 0;

      if (*temp_len < 2) break;

      if (get_random_chunk(afl, tags, fields_cnt, *temp_len, &del_from, &del_to, build_strategy))
          break;

      // avoid to have an empty buf
      if (del_to - del_from == (*temp_len)) break;

      memmove(buf + del_from, buf + del_to, (*temp_len) - del_to);
      memmove(tags + del_from, tags + del_to, ((*temp_len) - del_to) * sizeof(struct afl_cmp_tag));
      
      (*temp_len) -= (del_to - del_from);

      structure_changed = 1;

      break;
    
    }
  
    case 1: { // splice two chunks
    
      break;
    
    }
  
    case 2: {  // add a chunk
    
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
