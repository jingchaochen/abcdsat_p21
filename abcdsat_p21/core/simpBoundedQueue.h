#ifndef BoundedQueue_h
#define BoundedQueue_h

#include "mtl/Vec.h"

//=================================================================================================

namespace abcdSAT {

    template<typename T>
    class MyQueue {
        int max_sz, q_sz;
        int ptr;
        int64_t sum;
        vec<T> q;
    public:
        MyQueue(int sz) : max_sz(sz), q_sz(0), ptr(0), sum(0) { assert(sz > 0); q.growTo(sz); }
        inline bool   full () const { return q_sz == max_sz; }
        inline T      avg  () const { assert(full()); return sum / max_sz; }
        inline void   clear()       { sum = 0; q_sz = 0; ptr = 0; }
        int maxSize        ()       { return max_sz;}
        void push(T e) {
            if (q_sz < max_sz) q_sz++;
            else sum -= q[ptr];
            sum += e;
            q[ptr++] = e;
            if (ptr == max_sz) ptr = 0;
        }
	void growTo(int size) {
		q.growTo(size); 
		max_sz=size; q_sz = 0; ptr = 0; sum=0;
		for(int i=0;i<size;i++) q[i]=0; 
	}

 };

}
//=================================================================================================

#endif
