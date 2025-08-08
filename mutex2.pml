#ifndef NUM_THREADS
#define NUM_THREADS 2 // default value if not set by -DNUMTHREADS
#endif

#define MAX_SPIN 4

#define MUTEX_LOCKED 1       // 1 << 0
#define MUTEX_WOKEN 2        // 1 << 1
#define MUTEX_STARVING 4     // 1 << 2
#define MUTEX_WAITER_SHIFT 3 // 3

#include "sema2.pml"
#include "atomic.pml"

inline mutex_lock() {
  byte old;
  do
  :: atomic_swap(mutex.state, MUTEX_LOCKED, old);
     if
     :: old != 0 -> mutex_sema_acquire()
     :: else -> break
     fi
  od
}

inline mutex_unlock() {
  atomic_store(mutex.state, 0);
  mutex_sema_release()
}

byte num_threads_in_cs;

active [NUM_THREADS] proctype Thread() {
  assert(_pid < NUM_THREADS);
  do 
  :: mutex_lock();
     num_threads_in_cs++;
     num_threads_in_cs--;
     mutex_unlock();
  :: break
  od
}

// // mutual exclusion
// ltl safety {
//   [](num_threads_in_cs <= 1)
// }

// no starvation (does not hold)
// ltl liveness {
//   [](want_lock[0] -> <>have_lock[0]) && 
//   [](want_lock[1] -> <>have_lock[1])
// }
