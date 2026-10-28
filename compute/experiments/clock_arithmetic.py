"""Clock arithmetic: tables mod k and which residues can be undone.

On a k-hour clock we only keep remainders 0, 1, ..., k-1. We print the
addition and multiplication tables mod 6, find which residues have a
multiplicative inverse (some b with a * b = 1 mod k) by searching, and compare
the answer with the rule "gcd(a, k) = 1" for every modulus k from 2 to 30.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from math import gcd
import textwrap

EXPERIMENT = {
    "id": "clock_arithmetic",
    "title": "Clock arithmetic: which residues have inverses?",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["clock-arithmetic"],
    "summary": (
        "Prints the addition and multiplication tables mod 6, finds by search "
        "which residues have multiplicative inverses mod 6 and mod 7, and checks for every k from "
        "2 to 30 that these are exactly the a with gcd(a, k) = 1. The table proves "
        "the pattern only for k <= 30; for every k it is a theorem (from Bezout's "
        "identity) proved elsewhere."
    ),
    "packages": [],
}


def add_table(k):
    """The addition table mod k as a list of rows: row a, column b holds (a + b) % k."""
    if k < 1:
        raise ValueError("the modulus k must be at least 1")
    return [[(a + b) % k for b in range(k)] for a in range(k)]


def mul_table(k):
    """The multiplication table mod k: row a, column b holds (a * b) % k."""
    if k < 1:
        raise ValueError("the modulus k must be at least 1")
    return [[(a * b) % k for b in range(k)] for a in range(k)]


def inverse_by_search(a, k):
    """Return the b in 0..k-1 with a * b = 1 (mod k), found by trying every b; None if none.

    Note that mod 1 every number is 0 and 0 * 0 = 0 = 1 (mod 1), so 0 counts as invertible.
    """
    if k < 1:
        raise ValueError("the modulus k must be at least 1")
    for b in range(k):
        if (a * b) % k == 1 % k:
            return b
    return None


def invertible_residues(k):
    """The residues a in 0..k-1 that have an inverse mod k, found by search."""
    return [a for a in range(k) if inverse_by_search(a, k) is not None]


def coprime_residues(k):
    """The residues a in 0..k-1 with gcd(a, k) = 1."""
    return [a for a in range(k) if gcd(a, k) == 1]


def inverse_by_pow(a, k):
    """Inverse via Python's pow(a, -1, k) (the extended Euclidean algorithm), or None."""
    try:
        return pow(a, -1, k)
    except ValueError:
        return None


def compare_up_to(k_max, k_min=2):
    """For k = k_min..k_max compare search, gcd rule and pow(a, -1, k).

    Returns a list of moduli where the three methods disagree (empty if they always agree).
    """
    disagreements = []
    for k in range(k_min, k_max + 1):
        searched = invertible_residues(k)
        by_pow = [a for a in range(k) if inverse_by_pow(a, k) is not None]
        same_inverses = all(inverse_by_search(a, k) == inverse_by_pow(a, k) for a in searched)
        if not (searched == coprime_residues(k) == by_pow and same_inverses):
            disagreements.append(k)
    return disagreements


def format_side_by_side(k):
    """Return the lines of the + and x tables mod k printed next to each other."""
    head = " ".join(f"{b:>2}" for b in range(k))
    lines = [f" + |{head}      x |{head}", "---+" + "-" * (3 * k) + "    ---+" + "-" * (3 * k)]
    for a, (add_row, mul_row) in enumerate(zip(add_table(k), mul_table(k))):
        add_s = " ".join(f"{v:>2}" for v in add_row)
        mul_s = " ".join(f"{v:>2}" for v in mul_row)
        lines.append(f"{a:>2} |{add_s}     {a:>2} |{mul_s}")
    return lines


def main():
    print("Addition and multiplication on a 6-hour clock (mod 6):")
    for line in format_side_by_side(6):
        print("  " + line)
    print()
    for k in (6, 7):
        units = invertible_residues(k)
        pairs = " ".join(f"{a}*{inverse_by_search(a, k)}" for a in units if a <= inverse_by_search(a, k))
        print(f"Mod {k}: invertible residues {str(units):<20} inverse pairs: {pairs}")
    print("Mod 6, the residue 2 has no inverse: row 2 of the x table never contains a 1.")
    print()
    k_max = 30
    bad = compare_up_to(k_max)
    print(f"For every k = 2..{k_max}, compare three answers to 'which a have inverses?':")
    print("  search every b,  the rule gcd(a, k) = 1,  and pow(a, -1, k)")
    print(f"  moduli where they disagree: {bad if bad else 'none'}")
    counts = " ".join(str(len(coprime_residues(k))) for k in range(2, 17))
    print(f"  how many residues are invertible, k = 2..16: {counts}")
    print()
    print(textwrap.fill(
        f"Epistemic status: every residue for every k up to {k_max} was checked, so "
        "the gcd rule is verified for those moduli only. That it holds for every "
        "k is a theorem (it follows from Bezout's identity) proved elsewhere, not "
        "by this table.",
        width=78,
    ))


if __name__ == "__main__":
    main()
