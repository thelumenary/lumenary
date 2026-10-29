"""Famous dice and coin questions, settled by listing every outcome.

When all outcomes are equally likely, P(A) = |A| / |S|. This experiment
lists sample spaces with itertools.product and counts exactly with Fraction:
the sums of two dice; Galileo's question about three dice (why does 10 come
up more often than 9?); d'Alembert's mistake about two coins; and the
Chevalier de Mere's two bets. Where listing is impossible (36**24 outcomes)
it uses the complement rule P(not A) = 1 - P(A) instead, and says so.
"""

from collections import Counter
from fractions import Fraction
from itertools import product

EXPERIMENT = {
    "id": "probability_intro_exact_counts",
    "title": "Galileo, d'Alembert and de Mere: dice questions settled by counting",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["probability-intro"],
    "summary": (
        "Lists every outcome of rolling two and three dice, tossing two coins "
        "and rolling one die four times, and counts favourable outcomes "
        "exactly with fractions: the triangular distribution of two-dice sums, "
        "Galileo's 25 versus 27 ways for sums 9 and 10, d'Alembert's 3/4, and "
        "de Mere's 671/1296. His 24-roll bet is too large to list and uses the "
        "complement rule. Exact under the assumption of fair, independent dice."
    ),
    "packages": [],
}

DIE = range(1, 7)


def sum_counts(dice):
    """Counter: sum -> number of ordered outcomes, for `dice` fair dice."""
    return Counter(sum(roll) for roll in product(DIE, repeat=dice))


def partitions(total, parts=3):
    """Unordered ways to write total as a sum of `parts` numbers from 1-6."""
    return sorted({tuple(sorted(roll)) for roll in product(DIE, repeat=parts)
                   if sum(roll) == total})


def probability(event, outcomes):
    """Exact P(event) when every outcome in the list is equally likely."""
    outcomes = list(outcomes)
    return Fraction(sum(1 for o in outcomes if event(o)), len(outcomes))


def at_least_one_six(rolls):
    """P(at least one 6 in `rolls` rolls), by listing all 6**rolls outcomes."""
    return probability(lambda r: 6 in r, product(DIE, repeat=rolls))


def at_least_one_double_six(throws):
    """P(at least one double six in `throws` throws of two dice).

    Uses the complement rule: no double six in one throw has probability
    35/36, and independent throws multiply.
    """
    return 1 - Fraction(35, 36) ** throws


def main():
    two = sum_counts(2)
    print("Two dice: ordered outcomes giving each sum (out of 36)")
    print("  sum: " + " ".join(f"{s:2d}" for s in range(2, 13)))
    print("  ways:" + " ".join(f"{two[s]:2d}" for s in range(2, 13)))
    print()
    three = sum_counts(3)
    print("Galileo: three dice, 216 equally likely ordered outcomes")
    for total in (9, 10):
        p = Fraction(three[total], 216)
        print(f"  sum {total:2d}: {len(partitions(total))} partitions, "
              f"{three[total]} outcomes, P = {p} = {float(p):.4f}")
    print()
    coins = list(product("HT", repeat=2))
    p = probability(lambda c: "H" in c, coins)
    print("d'Alembert: two coins, outcomes " + " ".join("".join(c)
                                                       for c in coins))
    print(f"  P(at least one head) = {p}, not 2/3: of his three cases")
    print("  H, TH, TT, the first (H) covers two outcomes, HH and HT.")
    print()
    four = at_least_one_six(4)
    print("de Mere's bets:")
    print(f"  at least one 6 in 4 rolls: listing 1296 outcomes gives {four}"
          f" = {float(four):.4f}")
    print(f"  complement rule 1 - (5/6)^4 = {1 - Fraction(5, 6) ** 4}"
          " (the same)")
    p24 = at_least_one_double_six(24)
    print(f"  at least one double 6 in 24 throws: 1 - (35/36)^24 = "
          f"{float(p24):.4f}")
    print("  (36^24 outcomes are far too many to list: complement rule only)")
    print()
    print("Epistemic status: exact counts over complete lists of outcomes,")
    print("assuming fair dice and coins with independent throws. Whether real")
    print("dice behave like this is a question about the world, tested by")
    print("experiment (see the simulation), not settled by counting.")


if __name__ == "__main__":
    main()
