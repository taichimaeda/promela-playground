#ifndef NUM_THREADS
#define NUM_THREADS 2 // default value if not set by -DNUMTHREADS
#endif

#define MAX_SPIN 4

#define MUTEX_LOCKED 1       // 1 << 0
#define MUTEX_WOKEN 2        // 1 << 1
#define MUTEX_STARVING 4     // 1 << 2
#define MUTEX_WAITER_SHIFT 3 // 3

#include "chan.pml"
#include "atomic.pml"

Chan mutex_chan;
byte mutex_state;

inline mutex_lock() {
  byte old;
  byte iter = 0;
continue:
  do
  :: atomic_swap(mutex_state, MUTEX_LOCKED, old);
     if
     :: old != 0 ->
        if
        :: iter < MAX_SPIN ->
           iter++;
           goto continue;
        :: else
        fi
        chan_wait(mutex_chan);
     :: else -> break;
     fi
  od
}

inline mutex_unlock() {
  atomic_store(mutex_state, 0);
  chan_wake(mutex_chan);
}

byte num_threads_in_cs;

active [NUM_THREADS] proctype Thread() {
  assert(_pid < NUM_THREADS);
  do 
  :: mutex_lock();
     num_threads_in_cs++;
     num_threads_in_cs--;
     mutex_unlock();
  :: break;
  od
}

// // mutual exclusion
// ltl safety {
//   [](num_threads_in_cs <= 1)
// }
