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

The optional `incrementallucky` search tries greedy SAT completions without
copying the formula. It is disabled by default (0). Mode 1 tries a forward
false-first walk, mode 2 tries four combinations of forward/reverse order and
false/true polarity, mode 3 only backtracks to the assumption prefix as a
diagnostic control, and mode 4 tries the four walks above the current search
trail. Every mode preserves the assumption prefix. A conflicting choice is
flipped once; an unsuccessful walk backtracks without learning conditional
root units, and ordinary CDCL search resumes. Only a complete propagated
assignment can supply a SAT answer. The header capability macro
`KISSAT_HAS_INCREMENTAL_GREEDY` identifies these options.

By default an attempt requires 100,000 original clauses and either 100 new
conflicts or 10,000 new decisions in that solve. The corresponding options
are `incrementalluckyminclauses`, `incrementalluckyinit` and
`incrementalluckydecisions`. Each solve makes at most one attempt, with a
250 ms soft allowance (`incrementalluckymilliseconds`) and termination
polling between propagation calls. Explicit conflict or decision limits
bypass the optional walk. After failure, another attempt requires at least
100,000 new original clauses and four times the previous attempt's clause
count; `incrementalluckygrowth=1` keeps only the absolute growth requirement.
`incrementalluckynewcontext=1` also permits retries after assumptions change.
`incrementalluckyminunassigned` can gate attempts on the remaining variables,
and `incrementalluckyphasecache=1` saves phases after a successful completion.
Statistics report attempts, conflicts, successful completions and timeouts.

Copies of one loaded solver, such as processes forked after the clauses were
added, can exchange learned clauses. `kissat_set_learn` passes every learned
clause up to a size limit, and every unit derived at the root, to a callback
in external literals; clauses over variables that factoring introduced stay
private. `kissat_set_import` polls a callback between propagation and the
next decision every given number of conflicts, with a per-poll budget for
clauses of two or more literals. An imported clause must be implied by the
added clauses. It becomes a redundant clause, after backtracking as far as
watching it requires; a clause over an eliminated, substituted, unused or
factoring variable is dropped rather than restored, and nothing is imported
while a proof is written. `kissat_get_import_statistics` counts polls,
imported clauses and units, drops, satisfied clauses and backtracks.
`kissat_diversify` changes only search state between solves: the seed, the
saved phases (all true, all false or pseudo-random) and, optionally, the
decision queue and score order. Search mode remains the `stable` option,
which the first search reads. `KISSAT_HAS_CLAUSE_EXCHANGE` identifies the
extension, and `test/exchange.cpp` checks answers and models while copies
exchange clauses under inprocessing, factoring and both incremental modes.

An external propagator can take part in the search through the IPASIR-UP
interface: `kissat_connect_external_propagator` takes CaDiCaL's callbacks as
C function pointers, and `kissat_add_observed_var` protects a variable and
has its assignments told. Notifications follow the trail, with root
assignments told at the root and assignments kept by chronological
backtracking told again. Propagated literals take their reason clause at
once; that clause, like every external clause, propagates, conflicts or
waits as the trail makes it, and conflicts are analyzed like learned ones.
A complete assignment is a model only when the propagator accepts it, so
lucky and greedy assignments are skipped while one is connected. Optional
callbacks decide literals and, as in STP's CaDiCaL fork, advise the
polarity of observed variables the ordinary heuristic picked; a lazy
propagator (`is_lazy`) only checks complete assignments. A proposed literal
that its reason does not imply, or a run of proposals that change nothing,
ends the round of propagation instead of repeating. Callbacks may call only
`kissat_is_decision` and `kissat_terminate`; the other calls abort.
`KISSAT_HAS_EXTERNAL_PROPAGATOR` identifies the interface, and debug
builds check the propagator's state after every notification.
`test/propagator.cpp` checks it against a propagator holding clauses the
solver never sees directly, varying what CryptoMiniSat's IPASIR-UP fuzzer
varies: lazy propagators, mangled and broken reasons, models rejected
without a clause, stopped searches, and variables observed late (fixed ones
included), unobserved and observed again after a reconnect.
`test/propagator-exchange.cpp` runs copies that exchange learned clauses
while each has such a propagator connected.

`kissat_simplify` runs what a solve runs before its first decision (the
preprocessing rounds, on the first solve) and stops there, returning 20
for an inconsistent formula, 10 when a lucky assignment satisfied it and 0
otherwise; `kissat_root_fixed` then says which literals are fixed at the
root, with 0 for a variable eliminated or substituted. STP derives facts
about a query's Boolean skeleton this way. `KISSAT_HAS_ROOT_SIMPLIFY`
identifies the extension, and `test/simplify.cpp` checks that every
reported literal is implied, that every literal unit propagation implies
is reported, and that a solve afterwards answers correctly.

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
