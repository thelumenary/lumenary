"""Progressions in dense sets and in the primes; sums versus products.

1. Roth numbers: r3(N), the size of the largest subset of {0, ..., N-1} with no
   three-term arithmetic progression, computed exactly by backtracking for
   N <= 40. Roth's theorem says r3(N)/N -> 0, but the decay is extremely slow.
   We compare with the "base-3 digits 0 and 1" sets, which are 3AP-free.
2. Green-Tao: the primes contain arbitrarily long (finite) progressions. We
   find, for k = 3, ..., 7, the k-term progression of primes with the smallest
   last term.
3. Sum-product: for A = {1, ..., n}, |A + A| is small and |A . A| is large;
   for a geometric progression it is the other way round. Erdos and
   Szemeredi conjectured that one of the two is always nearly |A|^2.
"""

import math

EXPERIMENT = {
    "id": "additive_extremal_combinatorics_progressions",
    "title": "Roth numbers, prime progressions and the sum-product phenomenon",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["additive-extremal-combinatorics"],
    "summary": (
        "Computes the Roth numbers r3(N) for N <= 40 exactly by exhaustive "
        "backtracking, compares them with base-3 digit sets, finds the k-term "
        "progressions of primes with the smallest last term for k <= 7, and "
        "measures |A + A| and |A . A| for arithmetic and geometric progressions. "
        "Exact finite computations: they illustrate, but cannot test, asymptotic "
        "theorems such as Roth's and Green-Tao's."
    ),
    "packages": [],
}


def roth_number(N, smaller=()):
    """r3(N): the largest size of a subset of {0, ..., N-1} with no 3-term AP.

    `smaller` may list the known values r3(0), r3(1), ..., r3(N - 1). They speed
    up the exhaustive search: the elements still to be chosen lie in an interval
    of length L and form a 3AP-free set, so there are at most r3(L) of them."""
    table = list(smaller)

    def room(length):
        if length < len(table):
            return table[length]
        return length if not table else table[-1] + length - len(table) + 1

    best = table[-1] if table else 0  # a set for N - 1 also works for N
    chosen, member = [], [False] * N

    def ends_progression(x):
        # x is larger than every chosen element: it ends an AP a, b, x iff
        # a = 2b - x was chosen for some chosen b
        for b in chosen:
            a = 2 * b - x
            if a >= 0 and member[a]:
                return True
        return False

    def extend(x, size):
        nonlocal best
        if size + room(N - x) <= best:
            return  # cannot beat the best set known so far
        if x == N:
            best = size
            return
        if not ends_progression(x):
            chosen.append(x)
            member[x] = True
            extend(x + 1, size + 1)
            chosen.pop()
            member[x] = False
        extend(x + 1, size)

    extend(0, 0)
    return best


def roth_numbers(n_max):
    """[r3(1), ..., r3(n_max)], each search using all the smaller values."""
    table = [0]
    for N in range(1, n_max + 1):
        table.append(roth_number(N, table))
    return table[1:]


def has_three_ap(A):
    """True if the set A contains a, b, c with a < b < c and a + c = 2b."""
    s = sorted(set(A))
    members = set(s)
    return any((a + c) % 2 == 0 and (a + c) // 2 in members
               for i, a in enumerate(s) for c in s[i + 2:])


def base3_set(N):
    """Numbers below N whose base-3 digits are all 0 or 1 (a 3AP-free set)."""
    def ok(n):
        while n:
            if n % 3 == 2:
                return False
            n //= 3
        return True
    return [n for n in range(N) if ok(n)]


def prime_sieve(n):
    """sieve[i] is 1 exactly when i < n is prime."""
    sieve = bytearray([1]) * max(n, 2)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, n, i)))
    return sieve


def smallest_prime_progression(k, limit=2000):
    """The k-term AP of primes with the smallest last term below limit, or None."""
    sieve = prime_sieve(limit)
    for last in range(2, limit):
        if not sieve[last]:
            continue
        for d in range(1, (last - 2) // (k - 1) + 1):
            if all(sieve[last - i * d] for i in range(1, k)):
                return [last - i * d for i in range(k - 1, -1, -1)]
    return None


def sum_and_product_sizes(A):
    """(|A + A|, |A . A|) for a finite set of integers A."""
    return (len({a + b for a in A for b in A}),
            len({a * b for a in A for b in A}))


def main():
    values = roth_numbers(40)
    print("1. Roth numbers r3(N), N = 1..40 (exact, exhaustive):")
    print("   " + " ".join(str(v) for v in values[:20]))
    print("   " + " ".join(str(v) for v in values[20:]))
    for N in (10, 20, 40):
        b = base3_set(N)
        print(f"   N = {N}: r3/N = {values[N - 1] / N:.2f}; base-3 set has "
              f"{len(b)} elements, 3AP-free: {not has_three_ap(b)}")
    print("   base-3 sets have about N^0.63 elements; Behrend (1946) does")
    print("   better: N exp(-c sqrt(log N)), still o(N) as Roth requires.")
    print()
    print("2. Progressions of k primes with the smallest last term:")
    for k in range(3, 8):
        ap = smallest_prime_progression(k)
        print(f"   k = {k}: {', '.join(map(str, ap))} (difference {ap[1] - ap[0]})")
    print()
    print("3. Sums versus products, |A| = 20:")
    n = 20
    for name, A in [("{1, ..., 20}", list(range(1, n + 1))),
                    ("{1, 2, 4, ..., 2^19}", [2 ** i for i in range(n)])]:
        s, p = sum_and_product_sizes(A)
        print(f"   A = {name:20s}  |A + A| = {s:3d}   |A . A| = {p:3d}")
    print(f"   (|A|^2 = {n * n}; max(|A+A|, |A.A|) is large in both cases)")
    print()
    print("Epistemic status: exact, exhaustive computations for the sizes shown.")
    print("Roth's theorem (r3(N)/N -> 0) and Green-Tao are theorems about")
    print("N -> infinity; finite tables cannot confirm or refute them, and the")
    print("sum-product conjecture remains open despite such examples.")


if __name__ == "__main__":
    main()
