[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

The Kissat SAT Solver
=====================

Kissat is a "keep it simple and clean bare metal SAT solver" written in C.
It is a port of CaDiCaL back to C with improved data structures, better
scheduling of inprocessing and optimized algorithms and implementation.

Coincidentally "kissat" also means "cats" in Finnish.

Run `./configure && make test` to configure, build and test in `build`.

This checkout extends 4.0.4 with incremental solving. Set the `incremental`
option to 1 before the first solve, then use `kissat_assume` for assumptions
that expire after each solve and `kissat_failed` to query a failed assumption
core. Clauses may be added between solves, including clauses over previously
eliminated variables. `kissat_protect` and `kissat_unprotect` keep selected
variables available across inprocessing. `KISSAT_HAS_INCREMENTAL` identifies
the extended API. The implementation adapts the restoration and assumption
approach in Kissat Extras to the current solver.

The `incrementalreuse` option keeps a shared assumption prefix (1) or an
unchanged solve's full trail (2); its default of 0 starts from the root.
Local search locks assumptions while walking. Search phases, learned clauses,
inprocessing limits, and the stable restart schedule survive repeated solves.
Statistics include `incremental_restorations`, `incremental_restored_literals`,
`incremental_reused_solves`, and `incremental_reused_levels`.

Factoring introduces external variable IDs. An incremental API client must
allocate fresh IDs beyond both its already declared IDs and
`kissat_maximum_variable`, or disable `factor` before the first solve.
STP's adapter handles this mapping. Build a library
for STP with `./configure -fPIC && make`. For exhaustive incremental checks,
build with `./configure -g -fPIC --shared` and run
`python3 test/incremental.py`. Incremental proof output is not supported.
`test/incremental-cadical.cpp` optionally checks larger incremental sessions
against a separately linked CaDiCaL library, including factoring and aggressive
inprocessing. Compile it with both libraries and their include directories.

This is [STP's fork](https://github.com/stp/kissat). The `master` and
`upstream` branches mirror unmodified upstream 4.0.4; `stp` carries the
incremental extension and a CMake library build. The implementation uses
[Kissat Extras](https://github.com/aytey/kissat_extras) as a reference.

The CMake build supports the same POSIX toolchains as upstream and installs
`libkissat.a` and `include/kissat/kissat.h`:

```
cmake -S . -B build-cmake -DCMAKE_BUILD_TYPE=Release
cmake --build build-cmake --parallel
cmake --install build-cmake --prefix /path/to/install
```

Use `-DKISSAT_BUILD_CLI=OFF` for a library-only build. To run the exhaustive
incremental API tests, add `-DBUILD_TESTING=ON`, build, then run
`ctest --test-dir build-cmake --output-on-failure`. Python 3 is required only
for these tests. Both the CMake tests and the original `make test` suite run
in Debug and Release CI jobs.

`kissat_init_with_allocator` accepts per-instance allocation callbacks.
STP uses these to report allocation failure as RESOURCE and reclaim every
owned block if an allocation interrupts the C solver. If a callback exits
nonlocally, discard that solver through the allocation owner; its partially
modified structures cannot be reused or walked by `kissat_release`.
The CMake build enables exception unwinding through the C frames. A C++
client using the configure/make build should add `-fexceptions` as well.

Binaries are provided with each major [release](https://github.com/arminbiere/kissat/releases/).

You can get more information about Kissat in the last solver description for the SAT Competition 2024:

<p>
<a href="https://cca.informatik.uni-freiburg.de/biere/index.html#publications">Armin Biere</a>,
<a href="/biere/index.html">Tobias Faller</a>,
Katalin Fazekas,
<a href="https://cca.informatik.uni-freiburg.de/fleury/index.html">Mathias Fleury</a>,
Nils Froleyks
and
<a href="https://cca.informatik.uni-freiburg.de/pollittf.html">Florian Pollitt</a>
<br>
<a href="https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-SAT-Competition-2024-solvers.pdf">CaDiCaL, Gimsatul, IsaSAT and Kissat Entering the SAT Competition 2024</a>
<br>
<i>Proc.&nbsp;SAT Competition 2024: Solver, Benchmark and Proof Checker Descriptions</i>
<br>
Marijn Heule, Markus Iser, Matti J&auml;rvisalo, Martin Suda (editors)
<br>
Department of Computer Science Report Series B
<br>
vol.&nbsp;B-2024-1,
pages 8-10,
University of Helsinki 2024
<br>
[ <a href="https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-SAT-Competition-2024-solvers.pdf">paper</a>
| <a href="https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-SAT-Competition-2024-solvers.bib">bibtex</a>
| <a href="https://github.com/arminbiere/cadical">cadical</a>
| <a href="https://github.com/arminbiere/kissat">kissat</a>
| <a href="https://github.com/arminbiere/gimsatul">gimsatul</a>
| <a href="https://cca.informatik.uni-freiburg.de/sat24medals">medals</a>
]
</p>

See [NEWS.md](NEWS.md) for feature updates.
