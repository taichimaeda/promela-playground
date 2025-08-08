// rendezvous channel with FIFO wake up order
typedef Rchan {
  bool waiting[NUM_THREADS];
  chan waiters = [NUM_THREADS] of { byte };
}

inline rchan_wait(ch) {
  atomic {
    ch.waiters ! _pid;
    ch.waiting[_pid] = true;
    ch.waiting[_pid]; // wait until ready
  }
}

inline rchan_wake(ch) {
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