"""Integer partitions: generating functions, Euler's theorem and Glaisher's map.

We expand the generating functions

    prod 1/(1 - x^k)          (all partitions, p(n)),
    prod 1/(1 - x^(2k-1))     (partitions into odd parts),
    prod (1 + x^k)            (partitions into distinct parts)

as exact integer power series up to x^60, and compare the last two, as
Euler's theorem predicts. For n = 8 we also list Glaisher's bijection, which
merges equal odd parts into distinct parts, and check that it is a bijection.
Finally we compare p(n) with the Hardy-Ramanujan asymptotic formula and test
Ramanujan's congruence p(5m + 4) = 0 (mod 5) on a range.

All counts are exact. Agreement up to x^60 is evidence; Euler's theorem is
proved for all n in the lesson (and in Mathlib).
"""

import math

EXPERIMENT = {
    "id": "enumerative_combinatorics_partitions",
    "title": "Partitions: generating functions, Euler's theorem, Glaisher's map",
    "evidence": ["exact", "exhaustive-finite", "numerical"],
    "lessons": ["enumerative-combinatorics"],
    "summary": (
        "Expands the generating functions for all partitions, odd-part partitions and "
        "distinct-part partitions exactly up to x^60, checks Euler's theorem there, "
        "runs Glaisher's bijection on all partitions of 8, compares p(n) with the "
        "Hardy-Ramanujan formula, and tests Ramanujan's congruence mod 5 for n < 300. "
        "Finite checks only."
    ),
    "packages": [],
}


def times_geometric(series, step):
    """Multiply a truncated power series by 1/(1 - x^step), in place.

    If b = a / (1 - x^step) then b = a + x^step * b, so b[i] = a[i] + b[i - step].
    """
    for i in range(step, len(series)):
        series[i] += series[i - step]
    return series


def times_one_plus(series, step):
    """Multiply a truncated power series by (1 + x^step), in place."""
    for i in range(len(series) - 1, step - 1, -1):
        series[i] += series[i - step]
    return series


def partition_counts(n_max):
    """p(0), ..., p(n_max): coefficients of the product of 1/(1 - x^k)."""
    series = [1] + [0] * n_max
    for k in range(1, n_max + 1):
        times_geometric(series, k)
    return series


def odd_part_counts(n_max):
    """Coefficients of the product of 1/(1 - x^k) over odd k."""
    series = [1] + [0] * n_max
    for k in range(1, n_max + 1, 2):
        times_geometric(series, k)
    return series


def distinct_part_counts(n_max):
    """Coefficients of the product of (1 + x^k)."""
    series = [1] + [0] * n_max
    for k in range(1, n_max + 1):
        times_one_plus(series, k)
    return series


def partitions(n, largest=None):
    """All partitions of n as non-increasing tuples."""
    if largest is None:
        largest = n
    if n == 0:
        return [()]
    out = []
    for first in range(min(n, largest), 0, -1):
        out += [(first,) + rest for rest in partitions(n - first, first)]
    return out


def glaisher(odd_partition):
    """Merge equal odd parts: m copies of k become k * 2^i for the bits of m."""
    parts = []
    for k in set(odd_partition):
        m = odd_partition.count(k)
        i = 0
        while m:
            if m & 1:
                parts.append(k * 2 ** i)
            m >>= 1
            i += 1
    return tuple(sorted(parts, reverse=True))


def hardy_ramanujan(n):
    """The leading asymptotic exp(pi sqrt(2n/3)) / (4 n sqrt 3)."""
    return math.exp(math.pi * math.sqrt(2 * n / 3)) / (4 * n * math.sqrt(3))


def main():
    n_max = 60
    odd = odd_part_counts(n_max)
    distinct = distinct_part_counts(n_max)
    print("Generating functions expanded exactly up to x^60:")
    print(f"  odd-part counts:      {odd[:13]} ...")
    print(f"  distinct-part counts: {distinct[:13]} ...")
    print(f"  equal for every n <= {n_max}: {odd == distinct}")
    print()
    eights = partitions(8)
    odds8 = [q for q in eights if all(part % 2 for part in q)]
    images = [glaisher(q) for q in odds8]
    print(f"Glaisher's map on the {len(odds8)} odd-part partitions of 8:")
    for q, image in zip(odds8, images):
        print(f"  {'+'.join(map(str, q)):<17} -> {'+'.join(map(str, image))}")
    distinct8 = {q for q in eights if len(set(q)) == len(q)}
    print(f"  images distinct and exactly the distinct-part partitions: "
          f"{len(set(images)) == len(images) and set(images) == distinct8}")
    print()
    p = partition_counts(300)
    print("p(n) versus Hardy-Ramanujan exp(pi sqrt(2n/3))/(4n sqrt 3):")
    for n in (10, 50, 100, 300):
        print(f"  n = {n:>3}: p(n) = {p[n]:<19} ratio = "
              f"{p[n] / hardy_ramanujan(n):.4f}")
    bad = [n for n in range(4, 300, 5) if p[n] % 5]
    print(f"Ramanujan: p(5m + 4) divisible by 5 for all 5m + 4 < 300: {not bad}")
    print()
    print("Epistemic status: exact integer computation, exhaustive for n <= 60 "
          "(Euler)\nand n < 300 (Ramanujan), and for n = 8 (Glaisher). These "
          "are finite checks\nof theorems proved in general; the asymptotic "
          "ratios are numerical and only\nillustrate that the relative error "
          "tends to 0, slowly.")


if __name__ == "__main__":
    main()
