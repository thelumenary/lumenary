"""How many comparisons does sorting take? Insertion sort, merge sort, and a floor.

We count the comparisons made by insertion sort and merge sort. On every
ordering of n = 1..7 items we find each method's worst case exactly and set
it beside the lower bound ceil(log2 n!) that no comparison sort can beat.
Then we sort seeded random lists of 100 and 1000 numbers and compare the
counts with n(n - 1)/4 (insertion sort's average) and log2 n!.
Exhaustive-finite for n <= 7, a seeded experiment for the large lists.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from itertools import permutations
import math
import random
import textwrap

EXPERIMENT = {
    "id": "algorithms_and_efficiency_sorting_counts",
    "title": "Counting comparisons in insertion sort and merge sort",
    "evidence": ["exhaustive-finite", "experimental"],
    "lessons": ["algorithms-and-efficiency"],
    "summary": (
        "Counts comparisons made by insertion sort and merge sort on all "
        "orderings of up to 7 items (exact worst cases) and on seeded random "
        "lists of 100 and 1000 numbers, beside the lower bound log2(n!) for "
        "any comparison sort. Exhaustive for n <= 7; the random runs are one "
        "seeded sample each, not averages over all inputs."
    ),
    "packages": [],
}


def insertion_sort(items):
    """Return (sorted copy, number of comparisons) using insertion sort.

    Invariant: before step i, the first i entries are sorted.
    """
    a = list(items)
    comparisons = 0
    for i in range(1, len(a)):
        x = a[i]
        j = i - 1
        while j >= 0:
            comparisons += 1
            if a[j] <= x:
                break
            a[j + 1] = a[j]
            j -= 1
        a[j + 1] = x
    return a, comparisons


def merge_sort(items):
    """Return (sorted copy, number of comparisons) using merge sort."""
    a = list(items)
    if len(a) <= 1:
        return a, 0
    mid = len(a) // 2
    left, c1 = merge_sort(a[:mid])
    right, c2 = merge_sort(a[mid:])
    merged, comparisons = [], c1 + c2
    i = j = 0
    while i < len(left) and j < len(right):
        comparisons += 1
        if left[i] <= right[j]:
            merged.append(left[i])
            i += 1
        else:
            merged.append(right[j])
            j += 1
    merged.extend(left[i:])
    merged.extend(right[j:])
    return merged, comparisons


def lower_bound(n):
    """ceil(log2 n!): the fewest worst-case comparisons any method can need."""
    return (math.factorial(n) - 1).bit_length()


def worst_case(sort, n):
    """Largest comparison count of ``sort`` over all n! orderings of 0..n-1."""
    return max(sort(p)[1] for p in permutations(range(n)))


def main():
    print(" n   n!   insertion   merge   lower bound ceil(log2 n!)")
    for n in range(1, 8):
        ins, mer = worst_case(insertion_sort, n), worst_case(merge_sort, n)
        print(f"{n:>2} {math.factorial(n):>4}   {ins:>9}   {mer:>5}   {lower_bound(n):>5}")
    print("Insertion sort's worst case is n(n - 1)/2 (a reversed list).")
    print()
    rng = random.Random(2024)
    print("Seeded random lists (one run each):")
    print("    n   insertion   n(n-1)/4    merge   log2(n!)")
    for n in (100, 1000):
        data = [rng.random() for _ in range(n)]
        s1, ins = insertion_sort(data)
        s2, mer = merge_sort(data)
        assert s1 == s2 == sorted(data)
        bound = math.lgamma(n + 1) / math.log(2)
        print(f"{n:>5}   {ins:>9,}   {n * (n - 1) / 4:>8,.0f}   {mer:>6,}"
              f"   {bound:>8,.0f}")
    print()
    print(textwrap.fill(
        "Epistemic status: the table for n <= 7 is exhaustive and exact - every "
        "ordering was sorted. The random rows are a seeded experiment: one "
        "input each, so they show typical behaviour, not a theorem. The lower "
        "bound log2(n!) is the lesson's decision-tree theorem; insertion "
        "sort's n(n - 1)/2 worst case and merge sort's n log2 n growth are "
        "proved or sketched there.",
        width=78,
    ))


if __name__ == "__main__":
    main()
