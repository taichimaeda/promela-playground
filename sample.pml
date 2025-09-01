#define NUM_THREADS 2

byte next_ticket = 0;
byte curr_ticket = 0;
byte my_ticket[NUM_THREADS];

inline mutex_lock() {
  assert(_pid < NUM_THREADS);
  d_step {
    my_ticket[_pid] = next_ticket;
    next_ticket++;
  }
  do
  :: curr_ticket == my_ticket[_pid] -> break;
  od
}

inline mutex_unlock() {
  d_step {
    curr_ticket++;
  }
}

byte num_threads_in_cs;
bool want_lock[NUM_THREADS];
bool have_lock[NUM_THREADS];

active [NUM_THREADS] proctype worker() {
  want_lock[_pid] = true;
  mutex_lock()
  want_lock[_pid] = false;
  have_lock[_pid] = true;
  num_threads_in_cs++;
  skip; // simulate work
  num_threads_in_cs--;
  have_lock[_pid] = false;
  mutex_unlock()
}

// mutual exclusion
ltl safety {
  [](num_threads_in_cs <= 1)
}

// no starvation
ltl liveness {
  [](want_lock[0] -> <>have_lock[0]) && 
  [](want_lock[1] -> <>have_lock[1])
}
