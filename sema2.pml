// semaphore with FIFO wake up order
typedef Sema {
#ifndef SEMA_INIT
#define SEMA_INIT 0
#endif
  byte value = SEMA_INIT;
  bool waiting[NUM_THREADS];
  chan waiters = [NUM_THREADS] of { byte };
  byte count;
}

inline sema_acquire(sema) {
  atomic {
    do
    :: sema.value == 0 ->
       sema.count++;
       sema.waiters ! _pid;
       sema.waiting[_pid] = true;
       !sema.waiting[_pid]; // wait until ready
    :: else -> break
    od
    assert(sema.value > 0);
    sema.value--;
  }
}

inline sema_release(sema) {
  atomic {
#ifndef MAX_SEMA_VALUE
  sema.value++;
#else
  if
  :: sema.value < MAX_SEMA_VALUE ->
     sema.value++;
  :: else
  fi
#endif
    if
    :: sema.count > 0 ->
       byte id;
       sema.waiters ? id;
       sema.waiting[id] = false;
       sema.count--;
    :: else
    fi
  }
}