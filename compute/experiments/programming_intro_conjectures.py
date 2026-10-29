"""Testing conjectures with loops: confirmations, a famous failure, and a bug.

Loops make it easy to test a statement on thousands of cases. The experiment
checks two true formulas for n = 1..1000, then tests a conjecture Christian
Goldbach sent to Leonhard Euler in 1752 - every odd composite number is a
prime plus twice a square - and finds where it fails. Finally, a program
with an off-by-one bug runs without any error and prints a wrong answer.
Experimental evidence and counterexamples, not proofs.
"""

EXPERIMENT = {
    "id": "programming_intro_conjectures",
    "title": "Testing conjectures with loops, and a bug that runs fine",
    "evidence": ["experimental", "counterexample", "exact"],
    "lessons": ["programming-intro"],
    "summary": (
        "Checks 1 + ... + n = n(n + 1)/2 and 1 + 3 + ... + (2n - 1) = n^2 for "
        "n = 1..1000 with loops (evidence only; the lesson proves both). Tests "
        "Goldbach's 1752 conjecture that every odd composite number is a prime "
        "plus twice a square and finds the counterexamples 5777 and 5993 below "
        "10000. Shows an off-by-one bug that runs without error but sums only "
        "to n - 1."
    ),
    "packages": [],
}


def sum_loop(n):
    """1 + 2 + ... + n with a loop and a running total."""
    total = 0
    for i in range(1, n + 1):
        total = total + i
    return total


def sum_loop_buggy(n):
    """Meant to compute 1 + ... + n, but range(1, n) stops at n - 1."""
    total = 0
    for i in range(1, n):
        total = total + i
    return total


def sum_of_odds(n):
    """1 + 3 + 5 + ... + (2n - 1)."""
    return sum(2 * k - 1 for k in range(1, n + 1))


def prime_sieve(limit):
    """is_prime[k] for 0 <= k <= limit (Sieve of Eratosthenes)."""
    is_prime = [False, False] + [True] * (limit - 1)
    for p in range(2, int(limit ** 0.5) + 1):
        if is_prime[p]:
            for multiple in range(p * p, limit + 1, p):
                is_prime[multiple] = False
    return is_prime


def prime_plus_twice_square(n, is_prime):
    """A pair (p, k) with n = p + 2*k*k and p prime, or None."""
    k = 0
    while 2 * k * k <= n:
        if is_prime[n - 2 * k * k]:
            return (n - 2 * k * k, k)
        k += 1
    return None


def goldbach_other_counterexamples(limit):
    """Odd composite numbers up to limit that are NOT a prime plus 2k^2."""
    is_prime = prime_sieve(limit)
    return [n for n in range(9, limit + 1, 2)
            if not is_prime[n] and prime_plus_twice_square(n, is_prime) is None]


def main():
    print("1. Testing two formulas for n = 1, 2, ..., 1000")
    ok1 = all(sum_loop(n) == n * (n + 1) // 2 for n in range(1, 1001))
    ok2 = all(sum_of_odds(n) == n * n for n in range(1, 1001))
    print("   1 + 2 + ... + n == n(n + 1)/2 every time:", ok1)
    print("   1 + 3 + ... + (2n - 1) == n^2 every time:", ok2)
    print()
    print("2. Goldbach (1752): every odd composite = prime + 2 * square?")
    is_prime = prime_sieve(10000)
    for n in [9, 15, 21, 25, 27, 33]:
        p, k = prime_plus_twice_square(n, is_prime)
        print(f"   {n} = {p} + 2 * {k}^2")
    bad = goldbach_other_counterexamples(10000)
    print(f"   odd composites up to 10000 that fail: {bad}")
    print(f"   5777 = 53 * 109 is composite: {53 * 109 == 5777}")
    print()
    print("3. A program can run without errors and still be wrong")
    print(f"   sum_loop(100) = {sum_loop(100)},"
          f" sum_loop_buggy(100) = {sum_loop_buggy(100)}")
    print("   The bug: range(1, n) stops at n - 1. No error message appears.")
    print()
    print("Epistemic status: part 1 is experimental evidence for 1000 cases;")
    print("the lesson proves both formulas for every n. Part 2 checks every odd")
    print("composite up to 10000: the counterexamples refute Goldbach's claim")
    print("for good, but the search says nothing about numbers beyond 10000.")


if __name__ == "__main__":
    main()
