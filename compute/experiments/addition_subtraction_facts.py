"""Addition facts, take-away, and tens-and-ones, checked case by case.

Children learn the addition facts up to 10 + 10, the turn-around rule
a + b = b + a, that taking away undoes adding, and the written methods for
adding and subtracting two-digit numbers with tens and ones. A computer can
check all of these for every case in a finite range: all 121 facts
a + b with a, b from 0 to 10, every number from 0 to 99, all 10,000 pairs
of such numbers, and every two-digit addition and subtraction whose answer
stays between 0 and 99.

These are exhaustive checks of finitely many cases. They show the rules hold
in this range; why they hold for all numbers is a proof (see the lesson).

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap

EXPERIMENT = {
    "id": "addition_subtraction_facts",
    "title": "Addition facts, take-away and place value, case by case",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["addition-subtraction"],
    "summary": (
        "Checks the turn-around rule and 'taking away undoes adding' on all 121 "
        "facts up to 10 + 10, shows that subtraction does not turn around, "
        "checks that every number below 100 has one tens-and-ones form and that "
        "comparing tens then ones orders all 10,000 pairs correctly, and runs "
        "the column methods with regrouping on every sum and difference up to "
        "99. Exhaustive in this range only; the lesson gives the reasons."
    ),
    "packages": [],
}


def facts(limit=10):
    """All addition facts (a, b, a + b) with 0 <= a, b <= limit."""
    return [(a, b, a + b) for a in range(limit + 1) for b in range(limit + 1)]


def facts_to_learn(limit=10):
    """Facts left to learn when a + b and b + a count as one fact."""
    return sorted({(min(a, b), max(a, b)) for a, b, _ in facts(limit)})


def take_away(a, b):
    """a - b as a counting number, or None when b > a (no answer)."""
    return a - b if b <= a else None


def tens_ones(n):
    """Split 0 <= n <= 99 into (tens, ones)."""
    if not 0 <= n <= 99:
        raise ValueError("expected a number from 0 to 99")
    return divmod(n, 10)


def less_by_place_value(a, b):
    """Decide a < b by comparing tens first, then ones."""
    (ta, oa), (tb, ob) = tens_ones(a), tens_ones(b)
    return ta < tb or (ta == tb and oa < ob)


def column_add(a, b):
    """Add two numbers up to 99 by columns; return (sum, regrouped?)."""
    (ta, oa), (tb, ob) = tens_ones(a), tens_ones(b)
    ones = oa + ob
    carry = 1 if ones >= 10 else 0
    tens = ta + tb + carry
    if tens > 9:
        raise ValueError("the sum is 100 or more")
    return 10 * tens + (ones - 10 * carry), bool(carry)


def column_subtract(a, b):
    """Subtract b <= a <= 99 by columns; return (difference, regrouped?)."""
    if b > a:
        raise ValueError("cannot take a bigger number from a smaller one")
    (ta, oa), (tb, ob) = tens_ones(a), tens_ones(b)
    borrow = 1 if oa < ob else 0
    ones = oa + 10 * borrow - ob
    tens = ta - borrow - tb
    return 10 * tens + ones, bool(borrow)


def main():
    table = facts()
    learn = facts_to_learn()
    turn = sum(a + b == b + a for a, b, _ in table)
    undo = sum(take_away(s, b) == a for a, b, s in table)
    print(f"1. Addition facts from 0 + 0 to 10 + 10: {len(table)} facts")
    print(f"   a + b = b + a holds in {turn} of {len(table)}")
    print(f"   using the turn-around rule, only {len(learn)} facts to learn")
    print(f"   (a + b) - b = a holds in {undo} of {len(table)}")
    pairs = [(a, b) for a in range(11) for b in range(11)]
    both = [(a, b) for a, b in pairs
            if take_away(a, b) is not None and take_away(b, a) is not None]
    print(f"2. Does subtraction turn around? 5 - 3 = {take_away(5, 3)},")
    print("   but 3 - 5 has no answer among the counting numbers")
    print(f"   pairs from 0..10 where a - b and b - a both exist: {len(both)}")
    print("   (only a = b, and then both are 0)")
    forms = sorted(10 * t + o for t in range(10) for o in range(10))
    print("3. Tens and ones: 52 =", tens_ones(52)[0], "tens and",
          tens_ones(52)[1], "ones")
    print(f"   every number 0-99 has exactly one form: {forms == list(range(100))}")
    agree = sum(less_by_place_value(a, b) == (a < b)
                for a in range(100) for b in range(100))
    print(f"   'tens first, then ones' agrees with a < b in {agree:,} of 10,000")
    sums = [(a, b) for a in range(100) for b in range(100 - a)]
    add_ok = sum(column_add(a, b)[0] == a + b for a, b in sums)
    add_re = sum(column_add(a, b)[1] for a, b in sums)
    diffs = [(a, b) for a in range(100) for b in range(a + 1)]
    sub_ok = sum(column_subtract(a, b)[0] == a - b for a, b in diffs)
    sub_re = sum(column_subtract(a, b)[1] for a, b in diffs)
    print("4. Column methods (answers from 0 to 99):")
    print(f"   38 + 25 -> {column_add(38, 25)}   52 - 27 -> "
          f"{column_subtract(52, 27)}   (answer, regrouped?)")
    print(f"   addition: {add_ok:,} of {len(sums):,} correct, "
          f"{add_re:,} needed a regroup")
    print(f"   subtraction: {sub_ok:,} of {len(diffs):,} correct, "
          f"{sub_re:,} needed a regroup")
    print("   (the same count: each take-away undoes one of the additions)")
    print()
    print(textwrap.fill(
        "Epistemic status: exact, exhaustive checks of finitely many cases "
        "(121 facts, 100 numbers, 10,000 comparisons, 5,050 sums and 5,050 "
        "differences). They show the rules work in this range and nothing "
        "beyond it; the proofs in the lesson explain why they hold for all "
        "whole numbers.",
        width=78,
    ))


if __name__ == "__main__":
    main()
