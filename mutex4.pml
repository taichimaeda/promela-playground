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
  byte iter;
  byte old;
  byte new;
  bool swapped;

  atomic_compare_and_swap(mutex.state, 0, MUTEX_LOCKED, swapped)
  if
  :: swapped -> goto done
  :: else
  fi

  iter = 0;
  old = mutex.state;
continue:
  do
  :: if
     :: (old&MUTEX_LOCKED) != 0 && iter < MAX_SPIN ->
        iter++;
        old = mutex.state;
        goto continue;
     :: else
     fi
     new = old | MUTEX_LOCKED;
     if
     :: (old&MUTEX_LOCKED) != 0 ->
        new = new + (1 << MUTEX_WAITER_SHIFT);
     :: else
     fi
     atomic_compare_and_swap(mutex.state, old, new, swapped);
     if
     :: swapped ->
        if
        :: (old&MUTEX_LOCKED) == 0 -> break
        :: else
        fi
        mutex_sema_acquire();
        iter = 0
     :: else
     fi
     old = mutex.state
  od
done:
}

inline mutex_unlock() {
  byte old;
  byte new;
  bool swapped;

  atomic_add(mutex.state, -MUTEX_LOCKED, new);
  if
  :: new == 0; goto done
  :: else
  fi

  old = new;
  do
  :: if
     :: (old>>MUTEX_WAITER_SHIFT) == 0 || (old&MUTEX_LOCKED) == 0 ->
        goto done
     :: else
     fi
     new = old - (1<<MUTEX_WAITER_SHIFT);
     atomic_compare_and_swap(mutex.state, old, new, swapped);
     if
     :: swapped -> mutex_sema_release()
     :: else
     fi
     old = mutex.state
  od
done:
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
