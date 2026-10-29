"""Adding fractions: the right rule, a tempting wrong rule, and computer decimals.

Python's fractions.Fraction does exact arithmetic with fractions. We use it to
compare the rule a/b + c/d = (ad + cb)/(bd) with the tempting wrong rule
"add the tops and add the bottoms", (a + c)/(b + d), on every pair of
fractions between 0 and 1 with denominators up to 12; to check the
cross-multiplication test ad = cb against exact equality; and to see why a
computer's ordinary decimals (floats) can disagree with exact fractions.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "fractions_adding_rules",
    "title": "Adding fractions: right rule, wrong rule, exact answers",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["fractions"],
    "summary": (
        "Using exact fractions, checks the rule a/b + c/d = (ad + cb)/(bd) on all "
        "6,084 pairs of fractions in (0, 1] with denominators up to 12; the wrong rule "
        "(a + c)/(b + d) never gives the sum and always lands between the two "
        "fractions. Confirms the cross-multiplication test on 90,000 pairs and shows "
        "0.1 + 0.2 != 0.3 in floating point. Complete for these cases only."
    ),
    "packages": [],
}


def add_rule(a, b, c, d):
    """Numerator and denominator of a/b + c/d by the common-denominator rule."""
    return a * d + c * b, b * d


def wrong_rule(a, b, c, d):
    """The tempting mistake: add the numerators and add the denominators."""
    return a + c, b + d


def equivalent(a, b, c, d):
    """Cross-multiplication test: a/b and c/d are the same number."""
    return a * d == c * b


def fractions_in_unit_interval(max_den):
    """All pairs (a, b) with 1 <= a <= b <= max_den: fractions in (0, 1]."""
    return [(a, b) for b in range(1, max_den + 1) for a in range(1, b + 1)]


def compare_rules(max_den):
    """Return (pairs, right rule correct, wrong rule correct, wrong in between)."""
    fracs = fractions_in_unit_interval(max_den)
    right = wrong = between = 0
    for a, b in fracs:
        for c, d in fracs:
            exact = Fraction(a, b) + Fraction(c, d)
            right += Fraction(*add_rule(a, b, c, d)) == exact
            mediant = Fraction(*wrong_rule(a, b, c, d))
            wrong += mediant == exact
            low, high = sorted([Fraction(a, b), Fraction(c, d)])
            between += low <= mediant <= high
    return len(fracs) ** 2, right, wrong, between


def cross_test_agrees(max_num, max_den):
    """Return (pairs, agreements, equal pairs) for the cross-multiplication test."""
    fracs = [(a, b) for a in range(max_num + 1) for b in range(1, max_den + 1)]
    exact = {f: Fraction(*f) for f in fracs}
    pairs = agree = equal = 0
    for a, b in fracs:
        for c, d in fracs:
            pairs += 1
            same = exact[(a, b)] == exact[(c, d)]
            agree += equivalent(a, b, c, d) == same
            equal += same
    return pairs, agree, equal


def main():
    num, den = add_rule(1, 2, 1, 3)
    wn, wd = wrong_rule(1, 2, 1, 3)
    print(f"1/2 + 1/3 by the common-denominator rule: {num}/{den}")
    print(f"1/2 + 1/3 by 'add tops, add bottoms': {wn}/{wd}"
          f" = {float(Fraction(wn, wd))}, but 1/2 = 0.5")
    print("  The wrong answer is smaller than one of the parts!")
    print()
    pairs, right, wrong, between = compare_rules(12)
    print(f"All {pairs:,} pairs of fractions in (0, 1], denominators up to 12:")
    print(f"  right rule equals the exact sum:   {right:,} of {pairs:,}")
    print(f"  wrong rule equals the exact sum:   {wrong:,} of {pairs:,}")
    print(f"  wrong rule lands between the two:  {between:,} of {pairs:,}")
    pairs, agree, equal = cross_test_agrees(24, 12)
    print(f"Cross-multiplication test versus exact equality, {pairs:,} pairs:")
    print(f"  they agree {agree:,} times ({equal:,} pairs are equal numbers)")
    print()
    print(f"Floats:    0.1 + 0.2 == 0.3 is {0.1 + 0.2 == 0.3};"
          f" 0.1 + 0.2 = {0.1 + 0.2!r}")
    exact = Fraction(1, 10) + Fraction(2, 10) == Fraction(3, 10)
    print(f"Fractions: 1/10 + 2/10 == 3/10 is {exact}")
    print()
    print("Epistemic status: the checks are complete for the fractions listed,")
    print("so they prove nothing about larger denominators; the lesson's argument")
    print("(same-sized pieces, then count) covers every fraction. The float")
    print("result is a real counterexample: binary floats cannot store 0.1 exactly.")


if __name__ == "__main__":
    main()
