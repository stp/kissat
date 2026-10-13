extern "C" {
#include "kissat.h"
}

#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <new>
#include <unordered_set>

// Throw at each of the first allocation sites. An interrupted C solver is
// discarded through its allocation owner, including any unfinished scratch
// structures. A normally released solver must free every block itself.
struct memory {
  std::unordered_set<void *> blocks;
  unsigned calls = 0, fail_at;

  explicit memory (unsigned fail_at) : fail_at (fail_at) {}
  ~memory () {
    for (void *ptr : blocks)
      std::free (ptr);
  }
  void step () {
    if (calls++ == fail_at)
      throw std::bad_alloc ();
  }
  static void *allocate (void *state, size_t bytes) {
    memory &m = *static_cast<memory *> (state);
    m.step ();
    void *ptr = std::malloc (bytes);
    if (!ptr)
      throw std::bad_alloc ();
    try {
      m.blocks.insert (ptr);
    } catch (...) {
      std::free (ptr);
      throw;
    }
    return ptr;
  }
  static void *resize (void *state, void *ptr, size_t bytes) {
    if (!ptr)
      return allocate (state, bytes);
    memory &m = *static_cast<memory *> (state);
    m.step ();
    auto node = m.blocks.extract (ptr);
    assert (!node.empty ());
    void *res = std::realloc (ptr, bytes);
    if (!res) {
      m.blocks.insert (std::move (node));
      throw std::bad_alloc ();
    }
    node.value () = res;
    m.blocks.insert (std::move (node));
    return res;
  }
  static void deallocate (void *state, void *ptr) {
    memory &m = *static_cast<memory *> (state);
    if (m.blocks.erase (ptr) != 1)
      std::abort ();
    std::free (ptr);
  }
};

int main () {
  unsigned failures = 0;
  for (unsigned at = 0; at != 258; ++at) {
    memory owner (at == 257 ? ~0u : at);
    const kissat_allocator allocator = {
        &owner, memory::allocate, memory::resize, memory::deallocate};
    try {
      kissat *solver = kissat_init_with_allocator (&allocator);
      kissat_set_option (solver, "quiet", 1);
      kissat_set_option (solver, "incremental", 1);
      for (int i = 1; i != 201; ++i) {
        kissat_add (solver, i);
        kissat_add (solver, i + 1);
        kissat_add (solver, 0);
      }
      kissat_assume (solver, -1);
      if (kissat_solve (solver) != 10)
        return 1;
      kissat_add (solver, -2);
      kissat_add (solver, 0);
      kissat_solve (solver);
      kissat_release (solver);
      if (!owner.blocks.empty ())
        return 2;
    } catch (const std::bad_alloc &) {
      ++failures;
    }
  }
  if (failures < 100)
    return 3;
  std::printf ("PASS: %u allocation failures unwound through C frames\n",
               failures);
}
