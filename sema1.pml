// semaphore with random wake up order
typedef Sema {
#ifndef SEMA_INIT
#define SEMA_INIT 0
#endif
  byte value = SEMA_INIT;
}

inline sema_acquire(sema) {
  atomic { sema.value > 0 -> sema.value--; } 
}

inline sema_release(sema) {
  atomic { sema.value++; }
}
