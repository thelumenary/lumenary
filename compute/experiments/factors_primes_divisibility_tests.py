"""Divisibility tests: which shortcuts work, and which only look as if they do.

The last digit decides divisibility by 2, 5 and 10; the digit sum decides
divisibility by 3 and 9. We test each rule against honest division for every
number below 100,000, then try the same shortcuts where they do not belong
(digit sum for 7, last digit for 4) and report the first counterexample.
"""

EXPERIMENT = {
    "id": "factors_primes_divisibility_tests",
    "title": "Divisibility tests, checked and broken",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["factors-primes"],
    "summary": (
        "Checks the last-digit tests for 2, 5 and 10, the digit-sum tests for 3 and 9 "
        "and the alternating-sum test for 11 on every number below 100,000, and finds the "
        "smallest counterexamples to two false shortcuts: a digit-sum test for 7 and a "
        "last-digit test for 4. Complete for these numbers; the lesson gives the proofs."
    ),
    "packages": [],
}

LIMIT = 100_000


def digits(n):
    """Decimal digits of n >= 0, ones digit first."""
    if n < 0:
        raise ValueError("n must be a whole number")
    out = [n % 10]
    while n >= 10:
        n //= 10
        out.append(n % 10)
    return out


def digit_sum(n):
    """Sum of the decimal digits of n."""
    return sum(digits(n))


def alternating_sum(n):
    """Ones digit minus tens digit plus hundreds digit minus ..."""
    return sum(d if k % 2 == 0 else -d for k, d in enumerate(digits(n)))


def first_failure(test, d, limit=LIMIT):
    """Smallest n < limit where test(n) disagrees with 'd divides n', or None."""
    for n in range(limit):
        if test(n) != (n % d == 0):
            return n
    return None


#: (description, divisor, shortcut test). The two marked "a guess" are not real tests.
RULES = [
    ("last digit for 2", 2, lambda n: (n % 10) % 2 == 0),
    ("last digit for 5", 5, lambda n: (n % 10) in (0, 5)),
    ("last digit for 10", 10, lambda n: n % 10 == 0),
    ("digit sum for 3", 3, lambda n: digit_sum(n) % 3 == 0),
    ("digit sum for 9", 9, lambda n: digit_sum(n) % 9 == 0),
    ("alternating sum for 11", 11, lambda n: alternating_sum(n) % 11 == 0),
    ("digit sum for 7 (a guess)", 7, lambda n: digit_sum(n) % 7 == 0),
    ("last digit for 4 (a guess)", 4, lambda n: (n % 10) % 4 == 0),
    ("last two digits for 4", 4, lambda n: (n % 100) % 4 == 0),
]


def main():
    print(f"Each shortcut against honest division, for every n below {LIMIT:,}:")
    for name, d, test in RULES:
        n = first_failure(test, d)
        if n is None:
            verdict = "agrees every time"
        else:
            says = "yes" if test(n) else "no"
            verdict = f"FAILS first at n = {n}: says {says}, but {n} % {d} = {n % d}"
        print(f"  {name:<26} {verdict}")
    print()
    print("Why the digit sum works for 9: 10 = 9 + 1, 100 = 99 + 1, ...")
    n = 572
    print(f"  {n} = 5 x 99 + 7 x 9 + ({' + '.join(map(str, digits(n)[::-1]))})"
          f" = 9 x {(5 * 99 + 7 * 9) // 9} + {digit_sum(n)}")
    print(f"  so {n} and {digit_sum(n)} leave the same remainder on division by"
          f" 9: {n % 9} and {digit_sum(n) % 9}")
    print()
    print("Epistemic status: every number below 100,000 was checked, so the real")
    print("tests are certain for those numbers and the counterexamples are")
    print("genuine; that the real tests work for all numbers is the lesson's")
    print("place-value argument, not this search.")


if __name__ == "__main__":
    main()
