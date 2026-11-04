#!/usr/bin/env python3
"""Finite exact illustrations for the running ordering example.

Uses only the Python standard library. Run this file to reproduce the sibling
running_order_checks.json. These calculations check the listed finite cases;
they do not certify the general proof, the transfer theorem, or any Lean result.
"""

from collections import deque
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def positions(mask):
    return tuple(index + 1 for index in range(mask.bit_length())
                 if mask & (1 << index))


def pebble_checks(capacity):
    """Compare BFS with an independent recursive removal predicate."""
    length = 2 ** capacity + 1
    states = {
        sum(1 << (index - 1) for index in subset)
        for size in range(capacity + 1)
        for subset in combinations(range(1, length + 1), size)
    }

    @lru_cache(maxsize=None)
    def clearable(mask):
        if mask == 0:
            return True
        occupied = positions(mask)
        permitted_gap = 2 ** (capacity - len(occupied))
        left = 0
        for index in occupied:
            if index - left <= permitted_gap:
                if clearable(mask ^ (1 << (index - 1))):
                    return True
            left = index
        return False

    def neighbors(mask):
        for index in range(1, length + 1):
            predecessor_present = index == 1 or mask & (1 << (index - 2))
            if predecessor_present:
                following = mask ^ (1 << (index - 1))
                if following.bit_count() <= capacity:
                    yield following

    previous = {0: None}
    queue = deque([0])
    while queue:
        mask = queue.popleft()
        for following in neighbors(mask):
            if following not in previous:
                previous[following] = mask
                queue.append(following)
    reachable = set(previous)
    classified = {mask: clearable(mask) for mask in states}
    mismatches = [mask for mask in states
                  if classified[mask] != (mask in reachable)]
    require(not mismatches, f"capacity {capacity}: reachability mismatch")

    edges = {(mask, following) for mask in states for following in neighbors(mask)
             if mask < following}
    edge_mismatches = [(left, right) for left, right in edges
                       if classified[left] != classified[right]]
    require(not edge_mismatches, f"capacity {capacity}: toggle invariance failed")
    boundary = 2 ** capacity
    forbidden = {mask for mask in states if mask.bit_length() >= boundary}
    require(not (forbidden & reachable), f"capacity {capacity}: bound failed")
    maximum = max(mask.bit_length() for mask in reachable)
    require(maximum == boundary - 1, f"capacity {capacity}: sharp illustration failed")

    goal = next(mask for mask in previous if mask & (1 << (maximum - 1)))
    path = []
    while goal is not None:
        path.append(list(positions(goal)))
        goal = previous[goal]
    path.reverse()
    require(max(map(len, path)) <= capacity, "witness exceeds capacity")
    for before, after in zip(path, path[1:]):
        old = sum(1 << (index - 1) for index in before)
        new = sum(1 << (index - 1) for index in after)
        require(new in set(neighbors(old)), "illegal witness move")

    return {
        "capacity": capacity,
        "path_length": length,
        "all_subsets_checked": len(states),
        "undirected_legal_toggle_edges": len(edges),
        "reachable_subsets": len(reachable),
        "clearable_subsets": sum(classified.values()),
        "reachability_clearability_mismatches": len(mismatches),
        "clearability_toggle_mismatches": len(edge_mismatches),
        "maximum_reachable_position": maximum,
        "proposed_bound": boundary - 1,
        "subsets_with_a_position_at_least_2_pow_capacity": len(forbidden),
        "such_subsets_reachable": len(forbidden & reachable),
        "legal_path_to_maximum": path,
        "passed": True,
    }


# Exact integer polynomials in x1,x2,x3, represented by exponent tuples.
VARIABLE_COUNT = 3
ZERO_EXPONENT = (0,) * VARIABLE_COUNT


def cleaned(poly):
    return {exponent: coefficient for exponent, coefficient in poly.items()
            if coefficient != 0}


def constant(value):
    return {ZERO_EXPONENT: value} if value else {}


def variable(index):
    exponent = [0] * VARIABLE_COUNT
    exponent[index] = 1
    return {tuple(exponent): 1}


def add(left, right):
    result = dict(left)
    for exponent, coefficient in right.items():
        result[exponent] = result.get(exponent, 0) + coefficient
    return cleaned(result)


def scale(poly, coefficient):
    return cleaned({exponent: coefficient * value for exponent, value in poly.items()})


def subtract(left, right):
    return add(left, scale(right, -1))


def multiply(left, right):
    result = {}
    for left_exponent, left_coefficient in left.items():
        for right_exponent, right_coefficient in right.items():
            exponent = tuple(a + b for a, b in zip(left_exponent, right_exponent))
            result[exponent] = result.get(exponent, 0) + left_coefficient * right_coefficient
    return cleaned(result)


def degree(poly):
    return max((sum(exponent) for exponent in poly), default=-1)


def evaluate(poly, assignment):
    return sum(coefficient * product_of_powers(exponent, assignment)
               for exponent, coefficient in poly.items())


def product_of_powers(exponent, assignment):
    value = 1
    for power, coordinate in zip(exponent, assignment):
        value *= coordinate ** power
    return value


ONE = constant(1)
X = tuple(variable(index) for index in range(VARIABLE_COUNT))
BOOLEAN_AXIOMS = tuple(subtract(multiply(x, x), x) for x in X)


def boolean_reduce(poly):
    """Return multilinear remainder and explicit Boolean-ideal multipliers."""
    remainder = {}
    multipliers = [{} for _ in X]
    for exponent, coefficient in poly.items():
        current = list(exponent)
        for index in range(VARIABLE_COUNT):
            while current[index] >= 2:
                multiplier = list(current)
                multiplier[index] -= 2
                multipliers[index] = add(
                    multipliers[index], {tuple(multiplier): coefficient})
                current[index] -= 1
        remainder = add(remainder, {tuple(current): coefficient})
    reconstructed = dict(remainder)
    certificate_degree = 0
    for multiplier, axiom in zip(multipliers, BOOLEAN_AXIOMS):
        reconstructed = add(reconstructed, multiply(multiplier, axiom))
        if multiplier:
            certificate_degree = max(certificate_degree, degree(multiplier) + 2)
    require(reconstructed == poly, "integer Boolean-reduction identity failed")
    require(certificate_degree <= max(0, degree(poly)), "Boolean reduction raises degree")
    return remainder, multipliers, certificate_degree


def order_entry(i, j):
    if i == j:
        return {}
    if i < j:
        return subtract(ONE, multiply(X[i], subtract(ONE, X[j])))
    return multiply(subtract(ONE, X[i]), X[j])


def relative_pattern(indices):
    ranks = {value: index + 1 for index, value in enumerate(sorted(set(indices)))}
    return "".join(str(ranks[value]) for value in indices)


def order_substitution_checks():
    entries = {(i, j): order_entry(i, j) for i, j in product(range(3), repeat=2)}
    require(all(degree(poly) <= 2 for poly in entries.values()), "substitution exceeds degree two")
    families = {
        "irreflexivity": (1, [(str(i + 1), entries[i, i]) for i in range(3)]),
        "Boolean": (2, [(f"{i + 1},{j + 1}", subtract(multiply(entries[i, j], entries[i, j]), entries[i, j]))
                         for i, j in product(range(3), repeat=2)]),
        "asymmetry": (2, [(f"{i + 1},{j + 1}", multiply(entries[i, j], entries[j, i]))
                           for i, j in product(range(3), repeat=2)]),
        "totality": (1, [(f"{i + 1},{j + 1}", subtract(add(entries[i, j], entries[j, i]), ONE))
                         for i, j in product(range(3), repeat=2) if i != j]),
        "transitivity": (3, [(f"{i + 1},{j + 1},{k + 1}", multiply(
            multiply(entries[i, j], entries[j, k]), subtract(ONE, entries[i, k])))
                              for i, j, k in product(range(3), repeat=3)]),
    }
    result = {}
    for name, (original_degree, cases) in families.items():
        raw_maximum = 0
        certificate_maximum = 0
        for identifier, poly in cases:
            remainder, _, certificate_degree = boolean_reduce(poly)
            require(not remainder, f"{name} case {identifier}: nonzero multilinear remainder")
            require(all(evaluate(poly, bits) == 0 for bits in product((0, 1), repeat=3)),
                    f"{name} case {identifier}: Boolean evaluation failed")
            require(certificate_degree <= 2 * original_degree,
                    f"{name} case {identifier}: substitution degree bound failed")
            raw_maximum = max(raw_maximum, degree(poly))
            certificate_maximum = max(certificate_maximum, certificate_degree)
        result[name] = {
            "cases": len(cases),
            "Boolean_assignments_per_case": 8,
            "maximum_substituted_polynomial_degree": raw_maximum,
            "maximum_Boolean_certificate_degree": certificate_maximum,
            "allowed_certificate_degree": 2 * original_degree,
            "all_multilinear_remainders_zero": True,
            "all_explicit_integer_reduction_identities_match": True,
        }
    result["relative_triple_patterns"] = sorted({
        relative_pattern(indices) for indices in product(range(3), repeat=3)})
    result["passed"] = True
    return result


def predecessor_and_guard_checks():
    # Zero-based cyclic predecessor: 1 -> 3, 2 -> 1, 3 -> 2.
    predecessor = {0: 2, 1: 0, 2: 1}
    f = {(i, j): int(predecessor[i] == j) for i, j in product(range(3), repeat=2)}
    require(all(value * value == value for value in f.values()), "non-Boolean predecessor")
    require(all(f[i, i] == 0 for i in range(3)), "predecessor diagonal is nonzero")
    require(all(sum(f[i, j] for j in range(3)) == 1 for i in range(3)), "predecessor totality failed")
    functionality_cases = [(i, j, k) for i, j, k in product(range(3), repeat=3) if j != k]
    require(all(f[i, j] * f[i, k] == 0 for i, j, k in functionality_cases),
            "predecessor functionality failed")

    start = subtract(X[0], ONE)
    end = X[-1]
    internal = tuple(multiply(X[i - 1], subtract(ONE, X[i])) for i in range(1, 3))
    wrap = add(subtract(ONE, X[0]), multiply(X[0], X[-1]))
    for i, j in product(range(3), repeat=2):
        actual = scale(subtract(ONE, order_entry(j, i)), f[i, j])
        expected = {} if f[i, j] == 0 else (wrap if i == 0 else internal[i - 1])
        require(actual == expected, f"guard {i + 1},{j + 1}: ordinary polynomial mismatch")
    require(wrap == add(scale(start, -1), multiply(X[0], end)),
            "wrap endpoint certificate failed")
    return {
        "rank": 3,
        "cyclic_predecessor": {str(i + 1): j + 1 for i, j in predecessor.items()},
        "Boolean_cases": 9,
        "diagonal_cases": 3,
        "totality_rows": 3,
        "functionality_cases": len(functionality_cases),
        "guard_cases": 9,
        "internal_guards_match_induction_axioms_as_integer_polynomials": True,
        "wrap_identity": "1-L31 = (1-x1)+x1*x3 = -(x1-1)+x1*x3",
        "wrap_NS_certificate_degree": 2,
        "passed": True,
    }


def format_poly(poly):
    if not poly:
        return "0"
    parts = []
    for exponent, coefficient in sorted(poly.items(), key=lambda item: (sum(item[0]), item[0]), reverse=True):
        factors = [f"x{index + 1}" + (f"^{power}" if power > 1 else "")
                   for index, power in enumerate(exponent) if power]
        monomial = "*".join(factors)
        magnitude = abs(coefficient)
        term = (f"{magnitude}*" if magnitude != 1 and monomial else "") + monomial
        if not monomial:
            term = str(magnitude)
        parts.append(("-" if coefficient < 0 else "+") + term)
    text = " ".join(parts)
    return text[1:] if text.startswith("+") else text


def induction_pc_checks():
    axioms = {"start": subtract(X[0], ONE), "end": X[-1]}
    axioms.update({f"edge_{i + 1}": multiply(X[i], subtract(ONE, X[i + 1]))
                   for i in range(2)})
    lines = []

    def append(poly, rule, **data):
        lines.append({"poly": poly, "rule": rule, **data})
        return len(lines) - 1

    current = append(axioms["start"], "axiom", name="start")
    for i in range(2):
        edge = append(axioms[f"edge_{i + 1}"], "axiom", name=f"edge_{i + 1}")
        multiplied = append(multiply(X[i + 1], lines[current]["poly"]), "multiply_variable",
                            source=current, variable=i + 1)
        difference = append(add(lines[edge]["poly"], lines[multiplied]["poly"]),
                            "linear_combination", sources=[edge, multiplied], coefficients=[1, 1])
        complement = append(subtract(lines[difference]["poly"], lines[current]["poly"]),
                            "linear_combination", sources=[difference, current], coefficients=[1, -1])
        current = append(scale(lines[complement]["poly"], -1), "linear_combination",
                         sources=[complement, complement], coefficients=[-1, 0])
    end = append(axioms["end"], "axiom", name="end")
    append(subtract(lines[end]["poly"], lines[current]["poly"]), "linear_combination",
           sources=[end, current], coefficients=[1, -1])

    # Verify each stored line independently from its references and rule.
    serialized = []
    for index, line in enumerate(lines):
        rule = line["rule"]
        if rule == "axiom":
            expected = axioms[line["name"]]
        elif rule == "multiply_variable":
            require(0 <= line["source"] < index, "PC reference is not earlier")
            source = lines[line["source"]]["poly"]
            require(degree(source) <= 1, "PC multiplication starts above degree one")
            expected = multiply(variable(line["variable"]), source)
        else:
            require(rule == "linear_combination", "unknown PC rule")
            require(all(0 <= source < index for source in line["sources"]), "PC reference is not earlier")
            expected = {}
            for source, coefficient in zip(line["sources"], line["coefficients"]):
                expected = add(expected, scale(lines[source]["poly"], coefficient))
        require(expected == line["poly"], f"PC line {index}: rule identity failed")
        require(degree(expected) <= 2, f"PC line {index}: degree budget exceeded")
        item = {key: value for key, value in line.items() if key != "poly"}
        item.update({"line": index, "polynomial": format_poly(expected), "degree": degree(expected),
                     "integer_terms": [{"coefficient": value, "exponents": list(exponent)}
                                       for exponent, value in sorted(expected.items())]})
        if "variable" in item:
            item["variable"] += 1
        serialized.append(item)
    require(lines[-1]["poly"] == ONE, "PC derivation does not end in one")
    return {"rank": 3, "degree_budget": 2, "number_of_lines": len(lines),
            "all_references_and_rules_checked": True, "final_polynomial": "1",
            "lines": serialized, "passed": True}


def main():
    script = Path(__file__).resolve()
    report = {
        "schema_version": 1,
        "script": script.name,
        "script_sha256": sha256(script.read_bytes()).hexdigest(),
        "arithmetic": "Exact Python integers; no numerical approximation or dependencies.",
        "scope": "Finite illustrations only. No general-proof certification, transfer-theorem verification, or Lean claim.",
        "clearability_definition": "Recursively remove a position a when its gap from the nearest currently occupied position to its left (or 0) is at most 2^(D-|S|), and the remaining subset is clearable; the empty subset is clearable.",
    }
    try:
        report["pebble_checks"] = [pebble_checks(capacity) for capacity in range(1, 5)]
        report["order_substitution"] = order_substitution_checks()
        report["predecessor_and_guards"] = predecessor_and_guard_checks()
        report["ordinary_pc_induction"] = induction_pc_checks()
        report["all_passed"] = True
    except Exception as error:
        report["all_passed"] = False
        report["failure"] = f"{type(error).__name__}: {error}"
    output = script.with_name("running_order_checks.json")
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"{'PASS' if report['all_passed'] else 'FAIL'}: {output}")
    if not report["all_passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
