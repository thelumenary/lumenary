"""Ehrenfeucht-Fraisse games on finite linear orders, solved exhaustively.

Two players play k rounds on the linear orders {0 < 1 < ... < m-1} and
{0 < 1 < ... < n-1}. In each round Spoiler picks an element of either order and
Duplicator answers with an element of the other; Duplicator wins if the chosen
pairs always form a partial isomorphism (same order and equality pattern). By
the Ehrenfeucht-Fraisse theorem, Duplicator has a winning strategy for k rounds
exactly when the two orders satisfy the same sentences of quantifier rank <= k.
The program solves every game in a finite range by brute-force search and
compares the result with the classical rule: Duplicator wins iff m = n or
both m, n >= 2^k - 1. Evidence: exact and exhaustive over the range searched.
"""

from functools import lru_cache

EXPERIMENT = {
    "id": "model_theory_ef_games",
    "title": "Ehrenfeucht-Fraisse games on finite linear orders",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["model-theory"],
    "summary": (
        "Solves the k-round Ehrenfeucht-Fraisse game on finite linear orders of "
        "sizes m and n by exhaustive game-tree search (k <= 3, sizes up to 10) and "
        "checks the rule 'Duplicator wins iff m = n or m, n >= 2^k - 1'. By the "
        "Ehrenfeucht-Fraisse theorem this certifies which pairs agree on all "
        "sentences of quantifier rank <= k, but only for the sizes searched."
    ),
    "packages": [],
}


def sign(x):
    """Return -1, 0 or 1 according to the sign of x."""
    return (x > 0) - (x < 0)


def consistent(pairs, new):
    """True if adding the pair ``new`` keeps ``pairs`` a partial isomorphism."""
    a, b = new
    return all(sign(a - c) == sign(b - d) for c, d in pairs)


def duplicator_wins(m, n, k):
    """Solve the k-round EF game on linear orders of sizes m and n exactly."""
    if min(m, n, k) < 0:
        raise ValueError("sizes and rounds must be non-negative")

    @lru_cache(maxsize=None)
    def win(rounds, pairs):
        if rounds == 0:
            return True
        for side, size, other in ((0, m, n), (1, n, m)):
            for x in range(size):
                answers = ((x, y) if side == 0 else (y, x) for y in range(other))
                if not any(consistent(pairs, p)
                           and win(rounds - 1, tuple(sorted(pairs + (p,))))
                           for p in answers):
                    return False
        return True

    return win(k, ())


def predicted(m, n, k):
    """The classical rule for linear orders: m = n, or both are >= 2^k - 1."""
    return m == n or (m >= 2 ** k - 1 and n >= 2 ** k - 1)


def check_range(k, sizes):
    """Compare the search with the rule on all pairs m <= n from ``sizes``."""
    pairs = [(m, n) for m in sizes for n in sizes if m <= n]
    wrong = [(m, n) for m, n in pairs
             if duplicator_wins(m, n, k) != predicted(m, n, k)]
    return len(pairs), wrong


def smallest_equivalent_pair(k, limit):
    """Least m with sizes m and m + 1 indistinguishable in k rounds."""
    for m in range(1, limit):
        if duplicator_wins(m, m + 1, k):
            return m
    return None


def main():
    print("k-round EF games on linear orders of sizes m <= n (D = Duplicator)")
    for k, sizes in [(1, range(1, 9)), (2, range(1, 9)), (3, range(1, 11))]:
        total, wrong = check_range(k, list(sizes))
        least = smallest_equivalent_pair(k, 10)
        print(f"k = {k}: {total} games solved, sizes {sizes.start}..{sizes.stop - 1}; "
              f"disagreements with the 2^k - 1 rule: {len(wrong)}")
        print(f"       least m such that m, m + 1 are k-equivalent: {least} "
              f"(rule predicts {2 ** k - 1})")
    print("Row k = 2 (sizes 1..6), entry for (m, n):")
    for m in range(1, 7):
        row = " ".join("D" if duplicator_wins(m, n, 2) else "." for n in range(1, 7))
        print(f"   m = {m}: {row}")
    print("So 'the order has an even number of elements' is not expressible by")
    print("one first-order sentence: a sentence of rank k cannot tell 2^k - 1")
    print("elements from 2^k (one even, one odd size).")
    print()
    print("Epistemic status: exact, exhaustive game-tree search for the listed")
    print("sizes and k <= 3. It confirms the 2^k - 1 rule there and nowhere else;")
    print("the rule for all m, n, k and the link between games and sentences")
    print("(the Ehrenfeucht-Fraisse theorem) are theorems, cited in the lesson.")


if __name__ == "__main__":
    main()
