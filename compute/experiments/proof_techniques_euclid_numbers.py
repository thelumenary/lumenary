"""Euclid's numbers, and evidence versus proof for induction formulas.

Euclid's proof that there are infinitely many primes multiplies the primes of
a finite list and adds 1. The result N need not be prime itself - but every
prime factor of N is missing from the list. Here we factor N for the lists of
the first k primes, k = 1, ..., 9, and check that each factor is new.

Then we test two formulas proved by induction in the lesson,
1 + 2 + ... + n = n(n + 1)/2 and 1 + 3 + ... + (2n - 1) = n^2, for every n up
to 10 000, and a false claim whose inductive step works but whose base case
fails: "n^2 + n + 1 is even".

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from math import prod

EXPERIMENT = {
    "id": "proof_techniques_euclid_numbers",
    "title": "Euclid's numbers and induction formulas, checked",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["proof-techniques"],
    "summary": (
        "Factors 2*3*5*...*p + 1 for the first nine primes (30031 = 59 * 509 is "
        "not prime, but every factor is a new prime), and checks Gauss's sum "
        "formula and the sum of odd numbers for every n up to 10000, plus a fake "
        "theorem that fails at every n. Finite checks support the induction proofs "
        "in the lesson; they do not replace them."
    ),
    "packages": [],
}


def first_primes(k):
    """The first k primes."""
    primes = []
    n = 2
    while len(primes) < k:
        if all(n % p for p in primes if p * p <= n):
            primes.append(n)
        n += 1
    return primes


def factorize(n):
    """Prime factorisation of n >= 2 by trial division, as a sorted list."""
    if n < 2:
        raise ValueError("n must be at least 2")
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors


def euclid_number(primes):
    """The product of the given primes, plus one."""
    return prod(primes) + 1


def first_failure(claim, upto):
    """The least n in 0..upto with claim(n) false, or None."""
    for n in range(upto + 1):
        if not claim(n):
            return n
    return None


def step_difference(n):
    """(n+1)^2 + (n+1) + 1 minus n^2 + n + 1: always 2(n + 1), an even number,
    which is why "n^2 + n + 1 even" would pass from n to n + 1."""
    return ((n + 1) ** 2 + (n + 1) + 1) - (n * n + n + 1)


def running_check(term, closed_form, upto):
    """Check sum_{i < n} term(i) == closed_form(n) for n = 0..upto,
    accumulating the sum; return the first n where it fails, or None."""
    total = 0
    for n in range(upto + 1):
        if total != closed_form(n):
            return n
        total += term(n)
    return None


def main():
    print(" k  2*3*...*p_k + 1   factorisation           all factors new?")
    for k in range(1, 10):
        ps = first_primes(k)
        n = euclid_number(ps)
        fs = factorize(n)
        shown = " * ".join(map(str, fs)) if len(fs) > 1 else "prime"
        new = all(f not in ps for f in fs)
        print(f"{k:2d}  {n:15d}   {shown:22}  {'yes' if new else 'NO'}")
    print()
    upto = 10_000
    g = running_check(lambda i: i, lambda n: n * (n - 1) // 2, upto)
    o = running_check(lambda i: 2 * i + 1, lambda n: n * n, upto)
    print(f"Gauss: 0+1+...+(n-1) = n(n-1)/2, n <= {upto}: "
          f"{'no failure' if g is None else g}")
    print(f"Odd numbers: 1+3+...+(2n-1) = n^2, n <= {upto}: "
          f"{'no failure' if o is None else o}")
    step = all(step_difference(n) == 2 * (n + 1) for n in range(upto + 1))
    base = first_failure(lambda n: (n * n + n + 1) % 2 == 0, upto)
    print("'n^2+n+1 is even': consecutive values differ by 2(n+1) for all")
    print(f"  n <= {upto}: {step}. So the inductive step works - yet the claim")
    print(f"  fails at n = {base}, the base case, and in fact at every n.")
    print()
    print("Epistemic status: exact arithmetic. The factorisations are complete")
    print("and show that Euclid's numbers need not be prime. The formula checks")
    print("cover n <= 10000 only - finite evidence. The induction proofs in the")
    print("lesson cover every n; the last line shows why a base case is needed.")


if __name__ == "__main__":
    main()
