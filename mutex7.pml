#ifndef NUM_THREADS
#define NUM_THREADS 2 // default value if not set by -DNUMTHREADS
#endif

#define MAX_SPIN 4
#define STARVATION_THRESHOLD 10 // can be any value more than 1

#define MUTEX_LOCKED 1       // 1 << 0
#define MUTEX_WOKEN 2        // 1 << 1
#define MUTEX_STARVING 4     // 1 << 2
#define MUTEX_WAITER_SHIFT 3 // 3

#include "sema3.pml"
#include "atomic.pml"

Sema mutex_sema;
byte mutex_state;

inline mutex_lock() {
  byte iter;
  byte old;
  byte new;
  bool starving;
  bool awoke;
  bool lifo;
  byte wait;
  bool swapped;
  byte delta;
  byte null; // used to ignore return values

  atomic_compare_and_swap(mutex_state, 0, MUTEX_LOCKED, swapped)
  if
  :: swapped -> goto done;
  :: else
  fi

  wait = 0;
  starving = false;
  awoke = false;
  iter = 0;
  old = mutex_state;
continue:
  do
  :: if
     :: (old&(MUTEX_LOCKED|MUTEX_STARVING)) == MUTEX_LOCKED && iter < MAX_SPIN ->
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
     new = old;
     if
     :: (old&MUTEX_STARVING) == 0 ->
        new = new | MUTEX_LOCKED;
     :: else
     fi
     if
     :: (old&(MUTEX_LOCKED|MUTEX_STARVING)) != 0 ->
        new = new + (1 << MUTEX_WAITER_SHIFT);
     :: else
     fi
     if
     :: starving && (old&MUTEX_LOCKED) != 0 ->
        new = new | MUTEX_STARVING;
     :: else
     fi
     if
     :: awoke -> new = new & (~MUTEX_WOKEN);
     :: else
     fi
     atomic_compare_and_swap(mutex_state, old, new, swapped);
     if
     :: swapped ->
        if
        :: (old&(MUTEX_LOCKED|MUTEX_STARVING)) == 0 -> break;
        :: else
        fi
        lifo = (wait != 0);
        if
        :: wait < STARVATION_THRESHOLD -> 
           // approximates wait duration and stops incrementing if already reaching threshold
           // to prevent state explosion 
           wait++; 
        :: else
        fi 
        sema_acquire(mutex_sema, lifo);
        starving = starving || (wait > STARVATION_THRESHOLD);
        old = mutex_state;
        if
        :: (old&MUTEX_STARVING) != 0 ->
           delta = MUTEX_LOCKED - (1<<MUTEX_WAITER_SHIFT);
           if
           :: !starving || (old>>MUTEX_WAITER_SHIFT) == 1 ->
              delta = delta - MUTEX_STARVING;
           :: else
           fi
           atomic_add(mutex_state, delta, null);
           break;
        :: else
        fi
        awoke = true;
        iter = 0;
     :: else ->
        old = mutex_state; 
     fi
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

  if
  :: (new&MUTEX_STARVING) == 0 ->
     old = new;
     do
     :: if
        :: (old>>MUTEX_WAITER_SHIFT) == 0 || (old&(MUTEX_LOCKED|MUTEX_WOKEN|MUTEX_STARVING)) != 0 ->
           goto done;
        :: else
        fi
        new = old - (1<<MUTEX_WAITER_SHIFT) | MUTEX_WOKEN;
        atomic_compare_and_swap(mutex_state, old, new, swapped);
        if
        :: swapped ->
           sema_release(mutex_sema);
           assert(mutex_sema.value <= 1);
        :: else
        fi
        old = mutex_state;
     od
  :: else -> 
     sema_release(mutex_sema);
     assert(mutex_sema.value <= 1);
  fi
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
