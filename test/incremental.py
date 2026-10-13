#!/usr/bin/env python3
"""Check incremental Kissat against exhaustive CNF models, with no oracle dependency."""
import argparse
import ctypes
import os
import random
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--library', default=str(Path(__file__).resolve().parents[1] / 'build/libkissat.so'))
    parser.add_argument('--cases', type=int, default=500)
    parser.add_argument('--seed', type=int, default=20261012)
    args = parser.parse_args()
    lib = ctypes.CDLL(args.library)
    lib.kissat_init.restype = ctypes.c_void_p
    for name in ['add', 'assume', 'value', 'failed', 'protect', 'unprotect', 'set_conflict_limit', 'set_decision_limit']:
        f = getattr(lib, 'kissat_' + name)
        f.argtypes = [ctypes.c_void_p, ctypes.c_int]
        f.restype = ctypes.c_int if name in ['value', 'failed'] else None
    for name in ['solve', 'release', 'inconsistent']:
        getattr(lib, 'kissat_' + name).argtypes = [ctypes.c_void_p]
    lib.kissat_set_option.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_int]
    rng = random.Random(args.seed)
    calls = 0

    def set_option(s, name, value):
        lib.kissat_set_option(s, name.encode(), value)

    def add(s, clause):
        for lit in clause:
            lib.kissat_add(s, lit)
        lib.kissat_add(s, 0)

    def truth(lit, model):
        return bool(model & (1 << (abs(lit) - 1))) == (lit > 0)

    def models(n, clauses):
        return [m for m in range(1 << n) if all(any(truth(l, m) for l in c) for c in clauses)]

    for case in range(args.cases):
        s = lib.kissat_init()
        set_option(s, 'incremental', 1)
        # Raw API callers must manage factor variable IDs or disable BVA.
        # STP separately tests its mapping with factoring enabled.
        set_option(s, 'factor', 0)
        set_option(s, 'quiet', 1)
        set_option(s, 'check', 2)
        set_option(s, 'stable', case % 3)
        # Exercise inprocessing and compaction, not just the plain CDCL path.
        for opt in ['reduceinit', 'probeinit', 'eliminateinit', 'rephaseinit']:
            set_option(s, opt, 10)
        for opt in os.environ.get('KISSAT_TEST_OPTIONS', '').split(','):
            if opt:
                key, val = opt.split('=')
                set_option(s, key, int(val))
        if case == int(os.environ.get('KISSAT_TRACE_CASE', '-1')):
            set_option(s, 'quiet', 0)
            set_option(s, 'log', 2)
        n = rng.randint(5, 8)
        planted = rng.randrange(1 << n)
        clauses = []
        for _ in range(n * 4):
            clause = [rng.choice([-1, 1]) * rng.randint(1, n) for _ in range(rng.randint(2, 4))]
            if not any(truth(l, planted) for l in clause):
                clause[0] = -clause[0]
            clauses.append(clause)
            add(s, clause)
        if case % 4 == 0:
            lib.kissat_protect(s, 1)
        possible = models(n, clauses)
        for step in range(32):
            if step % 5 == 0:
                if step == 15 and n < 10:
                    n += 1
                clause = [rng.choice([-1, 1]) * rng.randint(1, n) for _ in range(rng.randint(1, 4))]
                if not any(truth(l, planted) for l in clause):
                    clause[0] = -clause[0]
                clauses.append(clause)
                add(s, clause)
                possible = models(n, clauses)
            if case == int(os.environ.get('KISSAT_TRACE_CASE', '-1')):
                print('CASE', case, 'STEP', step, flush=True)
            assumptions = [rng.choice([-1, 1]) * rng.randint(1, n) for _ in range(rng.randint(0, 5))]
            if step % 7 == 0:
                assumptions = [1, -1, 1]
            for lit in assumptions:
                lib.kissat_assume(s, lit)
            expected = any(all(truth(l, m) for l in assumptions) for m in possible)
            result = lib.kissat_solve(s)
            calls += 1
            assert result == (10 if expected else 20), (case, step, clauses, assumptions, result)
            if result == 10:
                model = sum(1 << (v - 1) for v in range(1, n + 1) if lib.kissat_value(s, v) > 0)
                assert all(any(truth(l, model) for l in c) for c in clauses), (case, step, 'model', clauses, model)
                assert all(truth(l, model) for l in assumptions), (case, step, 'assumed model')
            else:
                core = [l for l in assumptions if lib.kissat_failed(s, l)]
                assert not any(all(truth(l, m) for l in core) for m in possible), (case, step, 'core', core)
            assert not lib.kissat_inconsistent(s), (case, step, 'assumption UNSAT poisoned base')
        if case % 4 == 0:
            lib.kissat_unprotect(s, 1)
        add(s, [1])
        add(s, [-1])
        assert lib.kissat_solve(s) == 20
        assert lib.kissat_solve(s) == 20
        add(s, [n + 1])
        assert lib.kissat_solve(s) == 20
        lib.kissat_release(s)

    # Assumptions and resource limits must reset even after an UNKNOWN.
    s = lib.kissat_init()
    for name, value in [('incremental', 1), ('quiet', 1), ('preprocess', 0), ('luckyearly', 0), ('luckylate', 0)]:
        set_option(s, name, value)
    add(s, [1, 2])
    add(s, [3, 4])
    lib.kissat_assume(s, -1)
    lib.kissat_set_decision_limit(s, 0)
    assert lib.kissat_solve(s) == 0
    lib.kissat_assume(s, 1)
    assert lib.kissat_solve(s) == 10
    assert lib.kissat_value(s, 1) > 0
    assert lib.kissat_solve(s) == 10
    lib.kissat_release(s)

    # UNKNOWN can occur before even the first assumption is processed. A
    # full-trail reuse request must still apply them on the next call.
    s = lib.kissat_init()
    for name, value in [('incremental', 1), ('incrementalreuse', 2), ('quiet', 1),
                        ('preprocess', 0), ('luckyearly', 0), ('luckylate', 0)]:
        set_option(s, name, value)
    add(s, [1, 2])
    lib.kissat_assume(s, -1)
    lib.kissat_assume(s, -2)
    lib.kissat_set_conflict_limit(s, 0)
    assert lib.kissat_solve(s) == 0
    lib.kissat_assume(s, -1)
    lib.kissat_assume(s, -2)
    assert lib.kissat_solve(s) == 20
    assert not lib.kissat_inconsistent(s)
    assert lib.kissat_solve(s) == 10
    lib.kissat_release(s)
    print(f'PASS: {args.cases} sessions, {calls} exhaustive differential solves; models, cores, limits, and repeated UNSAT')


if __name__ == '__main__':
    main()
