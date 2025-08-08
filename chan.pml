// rendezvous channel with FIFO wake up order
typedef Chan {
  bool waiting[NUM_THREADS];
  chan waiters = [NUM_THREADS] of { byte };
}

inline chan_wait(ch) {
  atomic {
    ch.waiters ! _pid;
    ch.waiting[_pid] = true;
    ch.waiting[_pid]; // wait until ready
  }
}

inline chan_wake(ch) {
  atomic {
    if
    :: ch.waiters ? [_] ->
       byte id;
       ch.waiters ? id;
       ch.waiting[id] = false;
    :: else
    fi
  }
}