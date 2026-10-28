"""Counting functions between small finite sets.

A function f: A -> B picks one output in B for every input in A. If A has m
elements and B has n, we can list every function as a tuple
(f(a_1), ..., f(a_m)) using ``itertools.product``. We count how many are
injective (one-to-one), surjective (onto) and bijective, and compare the
counts with the standard formulas:

    all functions   n^m
    injective       n (n-1) ... (n-m+1)          (the falling factorial)
    surjective      sum_k (-1)^k C(n,k) (n-k)^m  (inclusion-exclusion)
    bijective       m! when m = n, otherwise 0

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from itertools import product
from math import comb, factorial
import textwrap

EXPERIMENT = {
    "id": "counting_functions",
    "title": "Counting functions, injections and surjections",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["functions"],
    "summary": (
        "Lists every function between sets of sizes 1 to 4, counts the injective, "
        "surjective and bijective ones exactly, and compares the counts with n^m, "
        "the falling factorial and the inclusion-exclusion formula. Agreement for "
        "these sizes is proved by enumeration; that the formulas hold for all "
        "sizes is a theorem the enumeration does not establish."
    ),
    "packages": [],
}


def all_functions(domain, codomain):
    """Return every function domain -> codomain as a dict {input: output}.

    There are len(codomain) ** len(domain) of them; for an empty domain there is
    exactly one (the empty function).
    """
    domain, codomain = list(domain), list(codomain)
    return [dict(zip(domain, outputs)) for outputs in product(codomain, repeat=len(domain))]


def is_injective(f):
    """True when different inputs always give different outputs."""
    outputs = list(f.values())
    return len(set(outputs)) == len(outputs)


def is_surjective(f, codomain):
    """True when every element of the codomain is an output of f."""
    return set(f.values()) == set(codomain)


def is_bijective(f, codomain):
    """True when f is both injective and surjective."""
    return is_injective(f) and is_surjective(f, codomain)


def count_by_enumeration(m, n):
    """Enumerate all functions {0..m-1} -> {0..n-1}; return a dict of counts."""
    domain, codomain = range(m), range(n)
    functions = all_functions(domain, codomain)
    return {
        "all": len(functions),
        "injective": sum(is_injective(f) for f in functions),
        "surjective": sum(is_surjective(f, codomain) for f in functions),
        "bijective": sum(is_bijective(f, codomain) for f in functions),
    }


def falling_factorial(n, k):
    """n (n-1) ... (n-k+1), the number of ways to choose k distinct items in order.

    Equals 1 when k = 0 and 0 when k > n.
    """
    if n < 0 or k < 0:
        raise ValueError("n and k must be non-negative")
    result = 1
    for i in range(k):
        result *= n - i
    return result


def surjection_formula(m, n):
    """Number of surjections from an m-set onto an n-set, by inclusion-exclusion.

    sum over k = 0..n of (-1)^k C(n, k) (n - k)^m, using Python's 0 ** 0 == 1.
    """
    if m < 0 or n < 0:
        raise ValueError("m and n must be non-negative")
    return sum((-1) ** k * comb(n, k) * (n - k) ** m for k in range(n + 1))


def formula_counts(m, n):
    """The counts predicted by the formulas, in the same shape as :func:`count_by_enumeration`."""
    return {
        "all": n ** m,
        "injective": falling_factorial(n, m),
        "surjective": surjection_formula(m, n),
        "bijective": factorial(m) if m == n else 0,
    }


def main():
    sizes = [(m, n) for m in range(1, 5) for n in range(1, 5)]
    print("Every function A -> B, |A| = m and |B| = n, listed with itertools.product.")
    print("Each cell shows: counted by enumeration / predicted by the formula.")
    print()
    print(f"{'m':>2} {'n':>2} | {'all  (n^m)':>11} | {'injective':>9} | {'surjective':>10} | {'bijective':>9}")
    print("-" * 57)
    agree = 0
    listed = 0
    for m, n in sizes:
        counted, predicted = count_by_enumeration(m, n), formula_counts(m, n)
        listed += counted["all"]
        agree += counted == predicted
        cells = [f"{counted[k]}/{predicted[k]}" for k in ("all", "injective", "surjective", "bijective")]
        print(f"{m:>2} {n:>2} | {cells[0]:>11} | {cells[1]:>9} | {cells[2]:>10} | {cells[3]:>9}")
    print()
    print(f"Listed {listed} functions; enumeration and formulas agree for {agree} of {len(sizes)} size pairs.")
    empty = [count_by_enumeration(0, n)["all"] for n in range(5)]
    print("Edge cases: from the empty set to a set of size 0, 1, 2, 3, 4 there are")
    print(f"{empty} functions (exactly one: the empty function);")
    print(f"from a 2-element set to the empty set there are {count_by_enumeration(2, 0)['all']}.")
    print()
    print(textwrap.fill(
        f"Epistemic status: exhaustive enumeration proves these counts for the "
        f"{len(sizes)} size pairs shown, and the formulas match them exactly. That the "
        "formulas hold for every m and n is a theorem proved by counting "
        "arguments; this table is consistent with it but does not prove it.",
        width=78,
    ))


if __name__ == "__main__":
    main()
