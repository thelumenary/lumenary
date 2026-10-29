"""Repeating patterns: last digits of powers, weekdays and calendar cycles.

Remainders of powers must eventually repeat, because there are only n
possible remainders. The experiment finds the repeating cycle of base^k mod n
for some bases (for n = 10 these are last digits), uses a cycle to get the
last digit of a huge power without computing the power, and checks the answer
against Python's exact pow. It then steps two calendar cycles forward day by
day until they line up again (the Chinese 10-stem and 12-branch cycle, and the
Maya 260-day and 365-day counts) and compares with the least common multiple.
All arithmetic is exact; each check covers only the cases printed.
"""

import math

EXPERIMENT = {
    "id": "modular_arithmetic_cycles",
    "title": "Cycles of remainders: powers and calendars",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["modular-arithmetic"],
    "summary": (
        "Finds the repeating cycles of 2^k, 3^k and 7^k modulo 10 and of 2^k "
        "modulo 7, predicts the last digit of 7^2026 from its cycle and checks "
        "it with exact arithmetic, and steps calendar cycles day by day until "
        "they realign (60 for 10 stems and 12 branches, 18980 days for the Maya "
        "260- and 365-day counts), matching the least common multiple."
    ),
    "packages": [],
}


def power_cycle(base, n):
    """Return (start, cycle) for the remainders base^k mod n, k = 0, 1, 2, ...

    ``start`` is the first k where the repeating part begins and ``cycle``
    lists one full period of remainders.
    """
    if n < 1:
        raise ValueError("n must be positive")
    seen = {}
    values = []
    r = 1 % n
    k = 0
    while r not in seen:
        seen[r] = k
        values.append(r)
        r = r * base % n
        k += 1
    start = seen[r]
    return start, values[start:]


def remainder_from_cycle(base, exponent, n):
    """base^exponent mod n read off the cycle (no huge power is computed)."""
    start, cycle = power_cycle(base, n)
    if exponent < start:
        return pow(base, exponent, n)
    return cycle[(exponent - start) % len(cycle)]


def realign(p, q):
    """Step a p-cycle and a q-cycle together; first day > 0 both are at 0."""
    day, a, b = 0, 0, 0
    while True:
        day, a, b = day + 1, (a + 1) % p, (b + 1) % q
        if a == 0 and b == 0:
            return day


WEEKDAYS = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday",
            "Saturday", "Sunday"]


def weekday_after(start, days):
    """Name of the weekday ``days`` days after the weekday named ``start``."""
    return WEEKDAYS[(WEEKDAYS.index(start) + days) % 7]


def main():
    print("Cycles of remainders of powers (k = 0, 1, 2, ...):")
    for base, n in [(2, 10), (3, 10), (7, 10), (2, 7), (4, 12)]:
        start, cycle = power_cycle(base, n)
        print(f"  {base}^k mod {n:<2}: starts repeating at k = {start}, "
              f"cycle {cycle}")
    predicted = remainder_from_cycle(7, 2026, 10)
    exact = pow(7, 2026) % 10
    digits = len(str(pow(7, 2026)))
    print(f"Last digit of 7^2026 from the cycle: {predicted}; exact: {exact}")
    print(f"  (7^2026 has {digits} digits; the cycle needed only 4 numbers)")
    print()
    print("Weekdays: 1 January 2026 was a Thursday.")
    for days in (7, 100, 365):
        print(f"  {days:>3} days later: {weekday_after('Thursday', days)}")
    print()
    print("Two cycles running side by side, stepped one at a time:")
    for p, q, name in [(10, 12, "Chinese stems and branches (years)"),
                       (260, 365, "Maya tzolk'in and haab' (days)")]:
        print(f"  {name}:")
        print(f"    {p} and {q} realign after {realign(p, q)} steps;"
              f" lcm({p}, {q}) = {math.lcm(p, q)}")
    print()
    print("Epistemic status: exact computations, each checked only for the")
    print("cases printed. That powers must repeat is a proof (there are only n")
    print("remainders); that a cycle of length 4 continues forever for 7^k mod 10")
    print("is proved in the lesson from 7^4 = 2401 and the product rule.")


if __name__ == "__main__":
    main()
