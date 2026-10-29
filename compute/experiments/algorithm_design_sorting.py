"""How many comparisons does sorting need? Mergesort against the lower bound.

We count the comparisons made by mergesort and by insertion sort. For small n
we try every one of the n! orderings, so the worst case is computed exactly
and can be compared with the decision-tree lower bound ceil(log2 n!) and with
the recurrence C(n) = C(floor(n/2)) + C(ceil(n/2)) + n - 1 for mergesort. For
larger n we sort seeded random permutations and compare the average counts
with n log2 n and with n^2/4, the average for insertion sort.
"""

import itertools
import math
import random

EXPERIMENT = {
    "id": "algorithm_design_sorting",
    "title": "Comparisons in mergesort, insertion sort and the lower bound",
    "evidence": ["exhaustive-finite", "experimental"],
    "lessons": ["algorithm-design"],
    "summary": (
        "Counts the comparisons made by mergesort and insertion sort. For "
        "n <= 7 it tries all n! inputs, so the worst cases are exact and can be "
        "compared with the lower bound ceil(log2 n!) and the recurrence for "
        "mergesort; for n up to 1024 it averages over seeded random inputs and "
        "compares with n log2 n and n^2/4."
    ),
    "packages": [],
}


def merge_sort(items):
    """Return (sorted list, number of comparisons) for mergesort."""
    if len(items) <= 1:
        return list(items), 0
    mid = len(items) // 2
    left, c1 = merge_sort(items[:mid])
    right, c2 = merge_sort(items[mid:])
    out, i, j, count = [], 0, 0, c1 + c2
    while i < len(left) and j < len(right):
        count += 1
        if left[i] <= right[j]:
            out.append(left[i])
            i += 1
        else:
            out.append(right[j])
            j += 1
    out.extend(left[i:])
    out.extend(right[j:])
    return out, count


def insertion_sort(items):
    """Return (sorted list, number of comparisons) for insertion sort."""
    out, count = list(items), 0
    for k in range(1, len(out)):
        x, j = out[k], k - 1
        while j >= 0:
            count += 1
            if out[j] <= x:
                break
            out[j + 1] = out[j]
            j -= 1
        out[j + 1] = x
    return out, count


def merge_recurrence(n):
    """Worst-case mergesort comparisons from C(n) = C(n//2) + C(n - n//2) + n - 1."""
    if n <= 1:
        return 0
    return merge_recurrence(n // 2) + merge_recurrence(n - n // 2) + n - 1


def lower_bound(n):
    """The decision-tree bound: any comparison sort needs ceil(log2 n!) in the worst case."""
    return math.ceil(math.log2(math.factorial(n))) if n > 1 else 0


def worst_case(sort, n):
    """Largest comparison count of `sort` over all n! orderings of range(n)."""
    return max(sort(list(p))[1] for p in itertools.permutations(range(n)))


def average_case(sort, n, trials, rng):
    """Mean comparison count over `trials` random permutations."""
    total = 0
    for _ in range(trials):
        items = list(range(n))
        rng.shuffle(items)
        result, count = sort(items)
        if result != sorted(items):
            raise AssertionError("sort failed")
        total += count
    return total / trials


def main():
    print("Worst cases over all n! inputs (exact):")
    print(" n   n!   lower bound  mergesort  recurrence  insertion  n(n-1)/2")
    for n in range(1, 8):
        print(f"{n:2d} {math.factorial(n):5d} {lower_bound(n):12d}"
              f" {worst_case(merge_sort, n):10d} {merge_recurrence(n):11d}"
              f" {worst_case(insertion_sort, n):10d} {n * (n - 1) // 2:9d}")
    print()
    rng = random.Random(2024)
    print("Averages over seeded random inputs (experimental):")
    print("    n   mergesort  n log2 n   insertion    n^2/4")
    for n, trials in [(16, 200), (128, 20), (1024, 2)]:
        m = average_case(merge_sort, n, trials, rng)
        s = average_case(insertion_sort, n, trials, rng)
        print(f"{n:5d} {m:11.1f} {n * math.log2(n):9.0f} {s:11.1f}"
              f" {n * n / 4:8.0f}")
    print()
    print("Epistemic status: the first table is exact for n <= 7 (every input")
    print("tried); mergesort's worst case matches its recurrence and stays")
    print("within one or two comparisons of the lower bound, which is a")
    print("theorem for every n. The averages are experiments on a few seeded")
    print("random inputs: evidence about typical behaviour, not a proof.")


if __name__ == "__main__":
    main()
