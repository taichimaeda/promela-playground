// semaphore with random wake up order
typedef Sema {
  byte value = 1; // needs to be init with 1
}

typedef Mutex {
  Sema sema;
  byte state;
}

Mutex mutex;

inline mutex_sema_acquire() {
  atomic { mutex.sema.value > 0 -> mutex.sema.value--; } 
}

inline mutex_sema_release() {
  atomic { mutex.sema.value++ }
}

// semaphore with FIFO wake up order
typedef Sema {
  byte value = 1;
  bool waiting[NUM_THREADS];
  chan waiters = [NUM_THREADS] of { byte };
  byte count;
}

typedef Mutex {
  Sema sema;
  byte state;
}

Mutex mutex;

inline mutex_sema_acquire() {
  atomic {
    if
    :: mutex.sema.value > 0 -> mutex.sema.value--
    :: else ->
       mutex.sema.waiters ! _pid;
       mutex.sema.waiting[_pid] = true;
       mutex.sema.count++
    fi
  }
  !mutex.sema.waiting[_pid] // wait until ready
}

inline mutex_sema_release() {
  atomic {
    if
    :: mutex.sema.count == 0 -> mutex.sema.value++
    :: else -> 
       byte id;
       mutex.sema.waiters ? id;
       mutex.sema.waiting[id] = false;
       mutex.sema.count--
    fi
  }
}

// semaphore with LIFO enqueue support
typedef Sema {
  byte value = 1;
  bool waiting[NUM_THREADS];
  byte waiters[NUM_THREADS + 1];
  byte head;
  byte tail;
  byte count;
}

typedef Mutex {
  Sema sema;
  byte state;
}

Mutex mutex;

inline mutex_sema_acquire(lifo) {
  atomic {
    if
    :: mutex.sema.value > 0 -> mutex.sema.value--
    :: else ->
       if
       :: lifo -> 
          mutex.sema.head = (mutex.sema.head + NUM_THREADS - 1) % NUM_THREADS;
          mutex.sema.waiters[mutex.sema.head] = _pid
       :: else ->
          mutex.sema.waiters[mutex.sema.tail] = _pid;
          mutex.sema.tail = (mutex.sema.tail + 1) % NUM_THREADS
       fi
       mutex.sema.waiting[_pid] = true;
       mutex.sema.count++;
    fi
  }
  !mutex.sema.waiting[_pid] // wait until ready
}

inline mutex_sema_release() {
  atomic {
    if
    :: mutex.sema.count == 0 -> mutex.sema.value++
    :: else ->
       byte id = mutex.sema.waiters[mutex.sema.head];
       mutex.sema.head = (mutex.sema.head + 1) % NUM_THREADS;
       mutex.sema.waiting[id] = false;
       mutex.sema.count--;
    fi
  }
}