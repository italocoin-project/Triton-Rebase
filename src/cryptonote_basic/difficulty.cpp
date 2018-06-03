// Copyright (c) 2014-2018, The Monero Project
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without modification, are
// permitted provided that the following conditions are met:
//
// 1. Redistributions of source code must retain the above copyright notice, this list of
//    conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright notice, this list
//    of conditions and the following disclaimer in the documentation and/or other
//    materials provided with the distribution.
//
// 3. Neither the name of the copyright holder nor the names of its contributors may be
//    used to endorse or promote products derived from this software without specific
//    prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY
// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
// THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
// STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
// THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// Parts of this file are originally copyright (c) 2012-2013 The Cryptonote developers

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "common/int-util.h"
#include "crypto/hash.h"
#include "cryptonote_config.h"
#include "difficulty.h"

#undef MONERO_DEFAULT_LOG_CATEGORY
#define MONERO_DEFAULT_LOG_CATEGORY "difficulty"

namespace cryptonote {

  using std::size_t;
  using std::uint64_t;
  using std::vector;

#if defined(__x86_64__)
  static inline void mul(uint64_t a, uint64_t b, uint64_t &low, uint64_t &high) {
    low = mul128(a, b, &high);
  }

#else

  static inline void mul(uint64_t a, uint64_t b, uint64_t &low, uint64_t &high) {
    // __int128 isn't part of the standard, so the previous function wasn't portable. mul128() in Windows is fine,
    // but this portable function should be used elsewhere. Credit for this function goes to latexi95.

    uint64_t aLow = a & 0xFFFFFFFF;
    uint64_t aHigh = a >> 32;
    uint64_t bLow = b & 0xFFFFFFFF;
    uint64_t bHigh = b >> 32;

    uint64_t res = aLow * bLow;
    uint64_t lowRes1 = res & 0xFFFFFFFF;
    uint64_t carry = res >> 32;

    res = aHigh * bLow + carry;
    uint64_t highResHigh1 = res >> 32;
    uint64_t highResLow1 = res & 0xFFFFFFFF;

    res = aLow * bHigh;
    uint64_t lowRes2 = res & 0xFFFFFFFF;
    carry = res >> 32;

    res = aHigh * bHigh + carry;
    uint64_t highResHigh2 = res >> 32;
    uint64_t highResLow2 = res & 0xFFFFFFFF;

    //Addition

    uint64_t r = highResLow1 + lowRes2;
    carry = r >> 32;
    low = (r << 32) | lowRes1;
    r = highResHigh1 + highResLow2 + carry;
    uint64_t d3 = r & 0xFFFFFFFF;
    carry = r >> 32;
    r = highResHigh2 + carry;
    high = d3 | (r << 32);
  }

#endif

  static inline bool cadd(uint64_t a, uint64_t b) {
    return a + b < a;
  }

  static inline bool cadc(uint64_t a, uint64_t b, bool c) {
    return a + b < a || (c && a + b == (uint64_t) -1);
  }

  bool check_hash(const crypto::hash &hash, difficulty_type difficulty) {
    uint64_t low, high, top, cur;
    // First check the highest word, this will most likely fail for a random hash.
    mul(swap64le(((const uint64_t *) &hash)[3]), difficulty, top, high);
    if (high != 0) {
      return false;
    }
    mul(swap64le(((const uint64_t *) &hash)[0]), difficulty, low, cur);
    mul(swap64le(((const uint64_t *) &hash)[1]), difficulty, low, high);
    bool carry = cadd(cur, low);
    cur = high;
    mul(swap64le(((const uint64_t *) &hash)[2]), difficulty, low, high);
    carry = cadc(cur, low, carry);
    carry = cadc(high, top, carry);
    return !carry;
  }

  difficulty_type next_difficulty(uint64_t height,std::vector<std::uint64_t> timestamps, std::vector<difficulty_type> cumulative_difficulties, size_t target_seconds) {

       if(height >= 24860){
    	 int64_t T = target_seconds;

    	//printf("size ts:%lu\n",timestamps.size());

       size_t length = timestamps.size();
       assert(length == cumulative_difficulties.size());

       uint64_t  t = 0,d=0;

    	 int64_t solvetime=0;
    	 int64_t diff = 0;

        for (size_t i = 1; i < length; i++) {
            solvetime = timestamps[i] - timestamps[i-1];
    	      diff = cumulative_difficulties[i] - cumulative_difficulties[i-1];
    	//printf("%lu: TS:%lu    solvetime:%d,  diff:%d\n",i,timestamps[i],solvetime,diff);

    	//cap crazy  values
        if (solvetime < 0) { solvetime = 0; }

            t +=  solvetime ;
    		    d+=diff;


        }


    	long unsigned int avgtime=t/length;
    	long unsigned int avgdiff=d/length;
    	long unsigned int adj=(T*1000/avgtime);
    	long unsigned int nextDiffZ = (avgdiff*adj)/1000;
    	//printf("avgdiff:%f, avgtime:%f   adj:%f   nextdiff:%lu\n",avgdiff,avgtime,adj,nextDiffZ);

        if (nextDiffZ <= 1) {
          nextDiffZ = 1;
        }


        return nextDiffZ;
      }else if(height < 24859){

        size_t c_difficultyWindow = 24 * 60 * 60 / 180;
        size_t c_difficultyCut = 60;

        assert(c_difficultyWindow >= 2);

        if (timestamps.size() > c_difficultyWindow) {
          timestamps.resize(c_difficultyWindow);
          cumulative_difficulties.resize(c_difficultyWindow);
        }

        size_t length = timestamps.size();
        assert(length == cumulative_difficulties.size());
        assert(length <= c_difficultyWindow);
        if (length <= 1) {
          return 1;
        }

        sort(timestamps.begin(), timestamps.end());

        size_t cutBegin, cutEnd;
        assert(2 * c_difficultyCut <= c_difficultyWindow - 2);
        if (length <= c_difficultyWindow - 2 * c_difficultyCut) {
          cutBegin = 0;
          cutEnd = length;
        } else {
          cutBegin = (length - (c_difficultyWindow - 2 * c_difficultyCut) + 1) / 2;
          cutEnd = cutBegin + (c_difficultyWindow - 2 * c_difficultyCut);
        }

        assert(/*cut_begin >= 0 &&*/ cutBegin + 2 <= cutEnd && cutEnd <= length);
        uint64_t timeSpan = timestamps[cutEnd - 1] - timestamps[cutBegin];
        if (timeSpan == 0) {
          timeSpan = 1;
        }

        difficulty_type totalWork = cumulative_difficulties[cutEnd - 1] - cumulative_difficulties[cutBegin];
        assert(totalWork > 0);

        uint64_t low, high;
        low = mul128(totalWork, target_seconds, &high);
        if (high != 0 || std::numeric_limits<uint64_t>::max() - low < (timeSpan - 1)) {
          return 0;
        }
          uint64_t nextDiffZ = low / timeSpan;

          return nextDiffZ;
    }
      }
  }
