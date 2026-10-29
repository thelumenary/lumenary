"""Linear search versus binary search: counting comparisons.

Binary search on a sorted list probes the middle entry and throws away half
of what is left. We count probes exactly: for every list size n up to 200
and every possible target (present or absent) the largest number of probes
is found by running the search, and compared with floor(log2 n) + 1. Then we
race the two searches on huge sorted lists (stored as a rule a[i] = 2i, so
nothing is allocated) and show why a faster computer does not rescue a slow
algorithm. Exhaustive-finite for the sizes tested; the lesson proves the
bound for every n.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import math
import textwrap

EXPERIMENT = {
    "id": "algorithms_and_efficiency_search_race",
    "title": "Linear and binary search: counting the comparisons",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["algorithms-and-efficiency"],
    "summary": (
        "Runs binary search for every target in sorted lists of every size "
        "n = 1..200 and finds the worst case is exactly floor(log2 n) + 1 "
        "probes; then counts probes for lists of up to 10^12 entries, against "
        "n comparisons for linear search. Exhaustive for n <= 200; the general "
        "bound is proved in the lesson."
    ),
    "packages": [],
}


def linear_search(key, n, target):
    """Scan a[0], a[1], ...; return (index or None, comparisons made).

    ``key(i)`` gives the entry a[i] of a list of length ``n``.
    """
    for i in range(n):
        if key(i) == target:
            return i, i + 1
    return None, n


def binary_search(key, n, target):
    """Search a sorted list a[0] <= ... <= a[n-1]; return (index or None, probes).

    Invariant: if the target is in the list, its index is in lo..hi.
    Each probe compares the target with the middle entry a[mid].
    """
    lo, hi = 0, n - 1
    probes = 0
    while lo <= hi:
        mid = (lo + hi) // 2
        probes += 1
        value = key(mid)
        if value == target:
            return mid, probes
        if value < target:
            lo = mid + 1
        else:
            hi = mid - 1
    return None, probes


def evens(i):
    """The sorted list 0, 2, 4, ... given as a rule."""
    return 2 * i


def worst_binary_probes(n):
    """Largest number of probes over every target -1, 0, 1, ..., 2n - 1."""
    return max(binary_search(evens, n, t)[1] for t in range(-1, 2 * n))


def log2_floor(n):
    """floor(log2 n) for n >= 1, computed exactly with integers."""
    return n.bit_length() - 1


def main():
    agree = all(worst_binary_probes(n) == log2_floor(n) + 1
                for n in range(1, 201))
    print("Binary search, every target, every size n = 1..200:")
    print(f"  worst case = floor(log2 n) + 1 probes for every n: {agree}")
    for n in (7, 8, 100, 128):
        print(f"  n = {n:>3}: worst {worst_binary_probes(n)} probes")
    print()
    print(f"{'list size n':>18}  {'linear (worst)':>18}  {'binary (worst)':>14}")
    for k in (1, 2, 3, 6, 9, 12):
        n = 10 ** k
        probes = binary_search(evens, n, 2 * n)[1]  # target beyond the end
        if n <= 1000:
            lin = f"{linear_search(evens, n, -1)[1]:,}"  # absent: run it
        else:
            lin = f"{n:,}*"
        print(f"{n:>18,}  {lin:>18}  {probes:>14}")
    print("* not run: an absent target forces linear search to check all n")
    print()
    speedup = 1000
    print(f"A computer {speedup} times faster, in the same time, handles:")
    print(f"  linear-time algorithm:    {speedup} times as much data")
    print(f"  quadratic-time algorithm: {math.sqrt(speedup):.1f} times as much data")
    print(f"  2^n-time algorithm:       only {math.log2(speedup):.1f} more items")
    print()
    print(textwrap.fill(
        "Epistemic status: exhaustive-finite and exact. The worst case of "
        "binary search was found by running every target for every n up to "
        "200; the large-n rows are exact counts from real runs. That the worst "
        "case is floor(log2 n) + 1 for every n is the lesson's theorem, proved "
        "by halving (and formalised in Lean); the runs only illustrate it.",
        width=78,
    ))


if __name__ == "__main__":
    main()
