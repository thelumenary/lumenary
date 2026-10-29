"""Euclid's algorithm: the steps, Bezout's coefficients, and how fast it is.

1. The extended Euclidean algorithm on (1071, 462): each division step
   a = q*b + r, and the integers x, y with 1071x + 462y = gcd(1071, 462).
2. Lame's theorem (1844): the number of division steps is at most five times
   the number of decimal digits of the smaller number. We find the slowest
   pair below each power of 10 by exhaustive search and compare: consecutive
   Fibonacci numbers are the worst cases.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

EXPERIMENT = {
    "id": "divisibility_gcd_euclid",
    "title": "Euclid's algorithm: steps, Bezout and Lame's bound",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["divisibility-gcd"],
    "summary": (
        "Traces the extended Euclidean algorithm on 1071 and 462 (gcd 21 = "
        "1071*(-3) + 462*7), then counts division steps for every pair a > b with "
        "b below 10, 100 and 1000 (a below 1000 in the last range), finding that "
        "consecutive Fibonacci numbers are slowest and that Lame's bound of five "
        "steps per digit holds there. Exhaustive in those ranges only."
    ),
    "packages": [],
}


def euclid_steps(a, b):
    """The division steps (a, q, b, r) with a = q*b + r of Euclid's algorithm."""
    if a < 0 or b < 0:
        raise ValueError("a and b must be non-negative")
    steps = []
    while b:
        q, r = divmod(a, b)
        steps.append((a, q, b, r))
        a, b = b, r
    return steps


def extended_gcd(a, b):
    """Return (g, x, y) with a*x + b*y = g = gcd(a, b), by back-substitution
    through Euclid's algorithm (iterative version)."""
    x0, y0, x1, y1 = 1, 0, 0, 1
    while b:
        q, r = divmod(a, b)
        a, b = b, r
        x0, x1 = x1, x0 - q * x1
        y0, y1 = y1, y0 - q * y1
    return a, x0, y0


def fibonacci(k):
    """F_0 = 0, F_1 = 1, F_(k+1) = F_k + F_(k-1)."""
    a, b = 0, 1
    for _ in range(k):
        a, b = b, a + b
    return a


def slowest_pair(b_limit, a_limit):
    """Among 1 <= b < a < a_limit with b < b_limit, a pair with the most
    division steps (the first found), and that number of steps."""
    best, best_pair = -1, None
    for b in range(1, b_limit):
        for a in range(b + 1, a_limit):
            n = len(euclid_steps(a, b))
            if n > best:
                best, best_pair = n, (a, b)
    return best_pair, best


def main():
    print("1. Euclid's algorithm on 1071 and 462:")
    for a, q, b, r in euclid_steps(1071, 462):
        print(f"   {a:5d} = {q} * {b:4d} + {r}")
    g, x, y = extended_gcd(1071, 462)
    print(f"   gcd = {g} = 1071 * ({x}) + 462 * {y}"
          f"   [check: {1071 * x + 462 * y}]")
    print()
    print("2. Slowest pairs (exhaustive search) and Lame's bound:")
    print("   b <    a <    slowest pair (a, b)   steps   5 x digits of b")
    for b_limit, a_limit in [(10, 60), (100, 300), (1000, 1000)]:
        (a, b), n = slowest_pair(b_limit, a_limit)
        print(f"   {b_limit:4d}   {a_limit:4d}   {str((a, b)):19}   {n:5d}"
              f"   {5 * len(str(b)):15d}")
    fib = [fibonacci(k) for k in range(8, 18)]
    print("   Fibonacci numbers:", ", ".join(map(str, fib)))
    print("   steps for (F_(k+1), F_k), k = 2..16:", " ".join(
        str(len(euclid_steps(fibonacci(k + 1), fibonacci(k)))) for k in range(2, 17)))
    print()
    print("Epistemic status: exact integer arithmetic; part 2 is an exhaustive")
    print("search over the stated finite ranges. It agrees with Lame's theorem")
    print("but proves it only there; the general proof compares the remainders")
    print("with Fibonacci numbers.")


if __name__ == "__main__":
    main()
