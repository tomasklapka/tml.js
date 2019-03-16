#ifdef DEBUG
#  include "__debug.js"
#  define ID(x) const id = ++__counters.x
#  define DBG(x) x
#  ifdef TRACE
#    define TRC(x) __cout(x)
#  else
#    define TRC(x)
#  endif
#else
#  define ID(x)
#  define DBG(x)
#  define TRC(x)
#endif
