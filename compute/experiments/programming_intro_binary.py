"""Binary numbers by repeated division, and why 0.1 + 0.2 != 0.3.

The experiment converts a number to binary by dividing by 2 again and again
and reading the remainders, compares the result with Python's bin() for
every number below 1024, and checks that the 1024 binary strings without
leading zeros of length at most 10 name each of 0..1023 exactly once. Then
it shows that a computer stores 0.1 as a nearby binary fraction, so
0.1 + 0.2 == 0.3 is False, while exact fractions get it right. Exact and
exhaustive-finite evidence.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "programming_intro_binary",
    "title": "Binary by repeated division, and why 0.1 + 0.2 != 0.3",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["programming-intro"],
    "summary": (
        "Converts 45 to binary by repeated division by 2, compares the method "
        "with Python's bin() for every number below 1024, and checks that the "
        "binary strings without leading zeros of length at most 10 name each of "
        "0..1023 exactly once. Then reveals the exact binary fraction stored for "
        "0.1, explains why 0.1 + 0.2 == 0.3 is False, and redoes the sum with "
        "exact fractions. Exhaustive below 1024 only."
    ),
    "packages": [],
}


def division_steps(n):
    """The steps n = 2*q + r of repeated division, as (n, q, r) triples."""
    steps = []
    while n > 0:
        steps.append((n, n // 2, n % 2))
        n = n // 2
    return steps


def to_binary(n):
    """Binary digits of n as a string, most significant first ('0' for 0)."""
    if n == 0:
        return "0"
    digits = ""
    while n > 0:
        digits = str(n % 2) + digits
        n = n // 2
    return digits


def from_binary(digits):
    """The value of a string of binary digits."""
    value = 0
    for d in digits:
        value = 2 * value + int(d)
    return value


def strings_without_leading_zeros(max_length):
    """'0' and every binary string of length <= max_length starting with 1."""
    found = ["0"]
    for length in range(1, max_length + 1):
        for k in range(2 ** (length - 1), 2 ** length):
            found.append(format(k, "b"))
    return found


def binary_fraction_digits(x, count):
    """The first `count` binary digits after the point of 0 <= x < 1."""
    digits = ""
    for _ in range(count):
        x = 2 * x
        digit = int(x)
        digits += str(digit)
        x -= digit
    return digits


def main():
    print("1. 45 in binary, by repeated division by 2")
    for n, q, r in division_steps(45):
        print(f"   {n:>2} = 2 * {q:>2} + {r}")
    print(f"   remainders, read upwards: {to_binary(45)}"
          f"  (check: {from_binary(to_binary(45))})")
    print()
    print("2. Every number below 1024")
    same = all(to_binary(n) == format(n, "b") for n in range(1024))
    back = all(from_binary(to_binary(n)) == n for n in range(1024))
    names = strings_without_leading_zeros(10)
    values = sorted(from_binary(s) for s in names)
    print("   repeated division agrees with Python's bin():", same)
    print("   converting back gives the number again:     ", back)
    print(f"   {len(names)} strings without leading zeros name each of 0..1023"
          f" once: {values == list(range(1024))}")
    print()
    print("3. Decimals that are not exact in binary")
    print("   0.1 + 0.2 =", 0.1 + 0.2, "  so 0.1 + 0.2 == 0.3 is", 0.1 + 0.2 == 0.3)
    print("   1/10 in binary: 0." + binary_fraction_digits(Fraction(1, 10), 24)
          + "...")
    print("   the stored value of 0.1 is exactly", Fraction(0.1))
    tenths = sum([0.1] * 10)
    print("   adding 0.1 ten times gives", tenths)
    exact = Fraction(1, 10) + Fraction(2, 10) == Fraction(3, 10)
    print("   with exact fractions, 1/10 + 2/10 == 3/10 is", exact)
    print()
    print("Epistemic status: parts 1 and 2 are exact and exhaustive for the")
    print("numbers below 1024; the lesson proves existence and uniqueness of")
    print("binary representations for every whole number. Part 3 shows the")
    print("actual stored values: floating-point numbers are approximations.")


if __name__ == "__main__":
    main()
