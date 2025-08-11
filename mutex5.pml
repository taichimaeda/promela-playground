#define NUM_THREADS 2
#define MAX_SPIN 4

#define MUTEX_LOCKED 1       // 1 << 0
#define MUTEX_WOKEN 2        // 1 << 1
#define MUTEX_STARVING 4     // 1 << 2
#define MUTEX_WAITER_SHIFT 3 // 3

#include "sema2.pml"
#include "atomic.pml"

Sema mutex_sema;
byte mutex_state;

inline mutex_lock() {
  byte iter;
  byte old;
  byte new;
  bool awoke;
  bool swapped;

  atomic_compare_and_swap(mutex_state, 0, MUTEX_LOCKED, swapped)
  if
  :: swapped -> goto done;
  :: else
  fi

  awoke = false;
  iter = 0;
  old = mutex_state;
continue:
  do
  :: if
     :: (old&MUTEX_LOCKED) != 0 && iter < MAX_SPIN ->
        if 
        :: !awoke && (old&MUTEX_WOKEN) == 0 && (old>>MUTEX_WAITER_SHIFT) != 0 ->
           atomic_compare_and_swap(mutex_state, old, (old|MUTEX_WOKEN), swapped);
           if
           :: swapped -> awoke = true;
           :: else
           fi
        :: else
        fi
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
     if
     :: awoke -> new = new & (~MUTEX_WOKEN); // ~ is bitwise not
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
        awoke = true;
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
     :: (old>>MUTEX_WAITER_SHIFT) == 0 || (old&(MUTEX_LOCKED|MUTEX_WOKEN)) != 0 ->
        goto done;
     :: else
     fi
     new = old - (1<<MUTEX_WAITER_SHIFT) | MUTEX_WOKEN;
     atomic_compare_and_swap(mutex_state, old, new, swapped);
     if
     // now we can use regular sema release
     // the woken bit does necessary bookkeeping to prevent duplicate sema release
     // sema value should always be 0 or 1 from now on
     :: swapped -> 
        sema_release(mutex_sema);
        assert(mutex_sema.value <= 1);
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

// // mutual exclusion
// ltl safety {
//   [](num_threads_in_cs <= 1)
// }
