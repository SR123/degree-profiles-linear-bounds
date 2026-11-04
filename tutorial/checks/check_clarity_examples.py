"""Finite illustration checks for the clarity revision, not a proof checker."""
from itertools import permutations, combinations
from pathlib import Path
import json

def add(a, b, ca=1, cb=1):
    out = {}
    for poly, c in ((a, ca), (b, cb)):
        for m, v in poly.items():
            out[m] = out.get(m, 0) + c*v
    return {m:v for m,v in out.items() if v}

def mulvar(a, i):
    out = {}
    for m,v in a.items():
        exponent = list(m)
        exponent[i] += 1
        out[tuple(exponent)] = v
    return out

def rename(a):
    return {(m[2],m[1],m[0]):v for m,v in a.items()}

def degree(a):
    return max((sum(m) for m in a), default=0)

variables = [{tuple(int(i == j) for j in range(3)):1} for i in range(3)]
lines = list(variables)
lines.append(add(lines[0], lines[1]))
lines.append(add(lines[2], lines[1], -1, -1))
lines.append(mulvar(lines[3], 0))
lines.append(mulvar(lines[4], 2))
lines.append(add(lines[5], lines[6]))
assert [degree(f) for f in lines] == [1,1,1,1,1,2,2,2]
original_product = mulvar(lines[3], 0)
assert lines[-1] == add(original_product, rename(original_product), 1, -1)
separate = add(add(mulvar(variables[0], 0), mulvar(variables[2], 2)),
               mulvar(variables[2], 0), 1, -2)
for p in (2,3,5,7):
    reduce = lambda a: {m:v % p for m,v in a.items() if v % p}
    assert reduce(lines[-1]) != reduce(separate)

perms = list(permutations((1,2,3)))
def sign(g):
    inv = sum(g[i] > g[j] for i in range(len(g)) for j in range(i+1,len(g)))
    return (-1)**inv

def chains(columns, g):
    pairs = list(zip(columns, g))
    result = []
    for size in range(len(pairs)+1):
        for indices in combinations(range(len(pairs)),size):
            if all(pairs[indices[i]][1] < pairs[indices[i+1]][1]
                   for i in range(len(indices)-1)):
                result.append(tuple(pairs[i][0] for i in indices))
    length = max(map(len,result))
    longest = sorted(c for c in result if len(c) == length)
    return length, longest

coefficients = {(3,2,1):-1, (3,1,2):1, (2,3,1):1,
                (2,1,3):-1, (1,3,2):-1, (1,2,3):1}
assert all(coefficients[g] == sign(g) for g in perms)
assert sum(coefficients.values()) == 0
for incoming in (1,2,3):
    for outgoing in (1,2,3):
        assert sum(coefficients[g] for g in perms if g[incoming-1] == outgoing) == 0
cycle = {(1,2):1,(2,3):1,(3,1):1,(2,1):-1,(3,2):-1,(1,3):-1}
assert {(g[0],g[1]):coefficients[g] for g in perms} == cycle
assert [g for g in perms if chains((1,2,3),g)[0] == 1] == [(3,2,1)]
canonical = chains((1,2,3),(3,2,1))[1][0]
assert canonical == (1,)
assert {(2,2),(1,3)} == {(g_value,col) for col,g_value in zip((1,2,3),(3,2,1)) if col not in canonical}
# Every two-rook has one completion; extensions of a one-rook at a
# specified unused row/column have opposite completion signs.
rook_completions = {}
for g in perms:
    graph = tuple((g[col-1],col) for col in (1,2,3))
    for cells in combinations(graph,2):
        rook_completions.setdefault(frozenset(cells),[]).append(g)
assert len(rook_completions) == 18
assert all(len(gs) == 1 for gs in rook_completions.values())
F = {rook:sign(gs[0]) for rook,gs in rook_completions.items()}
for row in (1,2,3):
    for col in (1,2,3):
        for next_col in (c for c in (1,2,3) if c != col):
            line = [frozenset(((row,col),(r,next_col)))
                    for r in (1,2,3) if r != row]
            assert sum(F[rook] for rook in line) == 0
        for next_row in (r for r in (1,2,3) if r != row):
            line = [frozenset(((row,col),(next_row,c)))
                    for c in (1,2,3) if c != col]
            assert sum(F[rook] for rook in line) == 0

assert chains((1,2,3,4),(2,1,3,4)) == (3,[(1,3,4),(2,3,4)])
assert chains((1,3,4),(2,3,4)) == (3,[(1,3,4)])
assert chains((2,3,4),(1,3,4)) == (3,[(2,3,4)])
assert chains((3,4),(3,4))[0] == 2
report = {
    "scope":"Finite worked illustrations only; not general theorem verification",
    "literal_pc_lines":8, "maximum_degree":2,
    "joint_independent_actions_differ_mod_primes":[2,3,5,7],
    "signed_two_rook_coefficients":6,
    "zero_lower_tuple_actions":True,
    "unique_completion_and_line_signs":True,
    "both_corner_contractions":True,
    "status":"PASS"
}
Path(__file__).with_name('clarity_example_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print('PC multiplication, signed two-rook realization and corner-contraction illustrations pass')
