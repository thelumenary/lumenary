"""For all and there exists, on finite sets: Python's all() and any().

On a finite set, "for every x, P(x)" is a long AND and "there is an x with
P(x)" is a long OR - exactly Python's all() and any(). The experiment checks
the negation rules for every predicate on every universe with at most five
elements, shows vacuous truth (all([]) is True), and shows that the order of
mixed quantifiers changes the answer. It also shows why a finite check cannot
settle a statement about all of N: cutting N off at 9 makes "for every x
there is a bigger y" false. Exhaustive-finite evidence only.
"""

import itertools

EXPERIMENT = {
    "id": "quantifiers_all_any",
    "title": "For all and there exists, as all() and any()",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["quantifiers"],
    "summary": (
        "Evaluates quantified statements on finite sets with all() and any(), "
        "checks both negation rules for all 63 predicates on universes with at "
        "most five elements, shows that all() of nothing is True (vacuous "
        "truth), and compares 'for all x there is y' with 'there is y for all "
        "x'. Finite checks only: they illustrate the rules the lesson proves, "
        "and show how cutting N off at a finite size changes answers."
    ),
    "packages": [],
}


def forall(universe, pred):
    """'For every x in universe, pred(x)' on a finite universe."""
    return all(pred(x) for x in universe)


def exists(universe, pred):
    """'There is an x in universe with pred(x)' on a finite universe."""
    return any(pred(x) for x in universe)


def forall_exists(xs, ys, rel):
    """'For every x there is a y with rel(x, y)' (y may depend on x)."""
    return all(any(rel(x, y) for y in ys) for x in xs)


def exists_forall(xs, ys, rel):
    """'There is a y with rel(x, y) for every x' (one y for all x)."""
    return any(all(rel(x, y) for x in xs) for y in ys)


def predicates(universe):
    """Every predicate on a finite universe, as a set of the true elements."""
    items = list(universe)
    for r in range(len(items) + 1):
        for chosen in itertools.combinations(items, r):
            yield frozenset(chosen)


def negation_rules_hold(universe):
    """Count predicates for which both negation rules agree, and the total."""
    agree = total = 0
    for truth in predicates(universe):
        p = truth.__contains__
        rule1 = (not forall(universe, p)) == exists(universe, lambda x: not p(x))
        rule2 = (not exists(universe, p)) == forall(universe, lambda x: not p(x))
        agree += rule1 and rule2
        total += 1
    return agree, total


def main():
    nums = range(100)
    print("1. Quantifiers over the finite set {0, ..., 99}")
    print("   every n has n*n % 4 in {0, 1}:   ",
          forall(nums, lambda n: n * n % 4 in (0, 1)))
    print("   some n has n*n % 4 == 2:         ",
          exists(nums, lambda n: n * n % 4 == 2))
    print()
    print("2. Negation rules, every predicate on universes of size 0..5")
    agree = total = 0
    for size in range(6):
        a, t = negation_rules_hold(range(size))
        agree, total = agree + a, total + t
    print(f"   not-all == some-not and not-some == all-not: {agree}/{total}")
    print()
    print("3. Vacuous truth: statements about the elements of the empty set")
    print("   all([]) =", all([]), "  any([]) =", any([]))
    print("   every element of {} is even:", forall([], lambda n: n % 2 == 0))
    print("   every element of {} is odd: ", forall([], lambda n: n % 2 == 1))
    print()
    print("4. The order of quantifiers")
    zs = range(-5, 6)
    add0 = lambda x, y: x + y == 0  # noqa: E731
    print("   on {-5..5}, for all x some y has x + y = 0:",
          forall_exists(zs, zs, add0))
    print("   on {-5..5}, some y has x + y = 0 for all x:",
          exists_forall(zs, zs, add0))
    cut = range(10)
    bigger = lambda x, y: y > x  # noqa: E731
    print("   on {0..9}, for all x some y > x:", forall_exists(cut, cut, bigger))
    print("   on {0..9}, some y >= every x:   ",
          exists_forall(cut, cut, lambda x, y: y >= x))
    print("   In N the answers flip: every x has a bigger y, and no y is >=")
    print("   every x. A finite piece of N has a largest element; N has not.")
    print()
    print("Epistemic status: exact, exhaustive checks on finite sets. Part 2")
    print("checks the negation rules for the 63 predicates on universes of up")
    print("to 5 elements; the lesson proves them for every set. Part 4 shows a")
    print("finite check of a statement about all of N can give the wrong answer.")


if __name__ == "__main__":
    main()
