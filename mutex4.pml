// from now on 2 is the practical limit for the number of threads
// there may be a critical bug that is leading to such state explosion
// that only occurs when there are 3 or more threads
#define NUM_THREADS 2
#define MAX_SPIN 4

#define MUTEX_LOCKED 1       // 1 << 0
#define MUTEX_WOKEN 2        // 1 << 1
#define MUTEX_STARVING 4     // 1 << 2
#define MUTEX_WAITER_SHIFT 3 // 3

// cannot set max to 1 this time
// assume there are N waiters and N new G's barge in to acquire and release the mutex
// then only 1 waiter will be waken up but waiters count now becomes zero
// which allows unlock to exit without waking up any other waiters
#define MAX_SEMA_VALUE (NUM_THREADS-1)
#include "sema2.pml"
#include "atomic.pml"

Sema mutex_sema;
byte mutex_state;

inline mutex_lock() {
  byte iter;
  byte old;
  byte new;
  bool swapped;

  atomic_compare_and_swap(mutex_state, 0, MUTEX_LOCKED, swapped)
  if
  :: swapped -> goto done;
  :: else
  fi

  iter = 0;
  old = mutex_state;
continue:
  do
  :: if
     :: (old&MUTEX_LOCKED) != 0 && iter < MAX_SPIN ->
        iter++;
        old = mutex_state;
        goto continue;
     :: else
     fi
     new = old | MUTEX_LOCKED;
     if
     :: (old&MUTEX_LOCKED) != 0 ->
        new = new + (1 << MUTEX_WAITER_SHIFT);
     :: else
     fi
     atomic_compare_and_swap(mutex_state, old, new, swapped);
     if
     :: swapped ->
        if
        :: (old&MUTEX_LOCKED) == 0 -> break;
        :: else
        fi
        sema_acquire(mutex_sema);
        iter = 0;
     :: else
     fi
     old = mutex_state;
  od
done:
}

inline mutex_unlock() {
  byte old;
  byte new;
  bool swapped;

  atomic_add(mutex_state, -MUTEX_LOCKED, new);
  if
  :: new == 0; goto done;
  :: else
  fi

  old = new;
  do
  :: if
     :: (old>>MUTEX_WAITER_SHIFT) == 0 || (old&MUTEX_LOCKED) != 0 ->
        goto done;
     :: else
     fi
     new = old - (1<<MUTEX_WAITER_SHIFT);
     atomic_compare_and_swap(mutex_state, old, new, swapped);
     if
     :: swapped -> sema_release(mutex_sema);
     :: else
     fi
     old = mutex_state;
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
  :: break;
  od
}

// simple checks for possible causes of state explosion other than thread interleaving
// when there are 3 or more threads
// ltl assert1 {
//   []((mutex_state>>MUTEX_WAITER_SHIFT) < NUM_THREADS)
// }
// ltl assert2 {
//   [](0 <= mutex_sema.value && mutex_sema.value < NUM_THREADS)
// }

// // mutual exclusion
// ltl safety {
//   [](num_threads_in_cs <= 1)
// }
