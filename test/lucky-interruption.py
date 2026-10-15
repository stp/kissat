#!/usr/bin/env python3
"""AUTHORS: Andrew Teylu

SPDX-License-Identifier: MIT

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.

Check cancellation during lucky assignments and reuse after interruption.
"""
import argparse
import ctypes

parser = argparse.ArgumentParser()
parser.add_argument('--library', required=True)
args = parser.parse_args()
lib = ctypes.CDLL(args.library)
lib.kissat_init.restype = ctypes.c_void_p
lib.kissat_add.argtypes = [ctypes.c_void_p, ctypes.c_int]
lib.kissat_set_option.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_int]
lib.kissat_solve.argtypes = [ctypes.c_void_p]
lib.kissat_value.argtypes = [ctypes.c_void_p, ctypes.c_int]
lib.kissat_release.argtypes = [ctypes.c_void_p]
lib.kissat_set_terminate.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p]
callback_type = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_void_p)


def run(stop_after):
    solver = lib.kissat_init()
    for name, value in [('incremental', 1), ('factor', 0), ('quiet', 1),
                        ('preprocess', 0), ('probe', 0),
                        ('luckyearly', 1), ('luckylate', 0)]:
        lib.kissat_set_option(solver, name.encode(), value)
    for var in range(1, 257, 2):
        for literal in (var, var + 1, 0):
            lib.kissat_add(solver, literal)
    calls = 0

    @callback_type
    def stop(_):
        nonlocal calls
        calls += 1
        return int(stop_after is not None and calls >= stop_after)

    lib.kissat_set_terminate(solver, None, ctypes.cast(stop, ctypes.c_void_p))
    result = lib.kissat_solve(solver)
    assert result == (10 if stop_after is None else 0), (stop_after, result, calls)
    assert calls > 0, 'the lucky pass never polled its termination callback'
    if stop_after is not None:
        lib.kissat_set_terminate(solver, None, None)
        assert lib.kissat_solve(solver) == 10
    for var in range(1, 257, 2):
        assert lib.kissat_value(solver, var) > 0 or lib.kissat_value(solver, var + 1) > 0
    lib.kissat_release(solver)
    return calls


polls = run(None)
for at in (1, polls // 4, polls // 2, polls * 3 // 4):
    run(max(at, 1))
print('lucky cancellation and resume: 5 cases passed; baseline polls:', polls)
