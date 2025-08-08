inline atomic_load(loc, ret) {
  d_step { ret = loc; }
}

inline atomic_store(loc, val) {
  d_step { loc = val; }
}

inline atomic_swap(loc, val, ret) {
  d_step { ret = loc; loc = val; }
}

inline atomic_compare_and_swap(loc, expected, desired, ret) {
  d_step { ret = (loc == expected); loc = (ret -> desired : loc); }
}

inline atomic_add(loc, val, ret) {
  d_step { loc = loc + val; ret = loc; }
}