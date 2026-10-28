"""Cantor's diagonal trick, run on a finite list.

An infinite binary sequence is a rule giving a digit 0 or 1 at every position
n = 0, 1, 2, ... Here each sequence is a Python function of n. Given a list of
sequences s_0, s_1, s_2, ..., Cantor builds a new sequence d by flipping the
diagonal: d(n) = 1 - s_n(n). Then d differs from s_n at position n, so d is
not anywhere in the list.

We run the mechanism on a finite list of 8 sequences. The finite run only
illustrates the trick; the proof that no list of infinite sequences can be
complete is the general argument, which a computer cannot run to the end.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from itertools import product
from math import isqrt
import textwrap

EXPERIMENT = {
    "id": "cantor_diagonal",
    "title": "Cantor's diagonal trick on a finite list",
    "evidence": ["exact"],
    "lessons": ["how-many-infinities"],
    "summary": (
        "Builds the diagonal-flipped sequence for a fixed list of 8 infinite binary "
        "sequences and checks exactly that it differs from every listed sequence. "
        "The finite run illustrates the mechanism only; the proof that the infinite "
        "binary sequences cannot be listed is Cantor's general argument."
    ),
    "packages": [],
}


def _is_prime(n):
    """Trial-division primality test (n >= 0)."""
    if n < 2:
        return False
    return all(n % d for d in range(2, isqrt(n) + 1))


def _sqrt2_digit(n):
    """Digit n (counting from 0) after the binary point of sqrt(2) = 1.0110101..."""
    return isqrt(2 << (2 * (n + 1))) & 1


#: A fixed, deterministic list of infinite binary sequences: (name, rule).
SEQUENCES = [
    ("all zeros", lambda n: 0),
    ("all ones", lambda n: 1),
    ("alternating", lambda n: n % 2),
    ("1 at squares", lambda n: int(isqrt(n) ** 2 == n)),
    ("1 at primes", lambda n: int(_is_prime(n))),
    ("Thue-Morse", lambda n: bin(n).count("1") % 2),
    ("1 at multiples of 3", lambda n: int(n % 3 == 0)),
    ("binary digits of sqrt 2", _sqrt2_digit),
]


def prefix(seq, length):
    """The first ``length`` digits of a sequence, as a list."""
    return [seq(n) for n in range(length)]


def diagonal_flip(seqs):
    """Return Cantor's diagonal sequence d with d(n) = 1 - seqs[n](n).

    ``seqs`` is a list of sequences (functions of n). For a finite list, d(n) is
    only defined for n < len(seqs); in the infinite argument the list never
    runs out, so d is defined everywhere.
    """
    seqs = list(seqs)

    def d(n):
        if not 0 <= n < len(seqs):
            raise IndexError("the diagonal is only defined at positions 0..len(list)-1")
        return 1 - seqs[n](n)

    return d


def differs_from_every_row(seqs, d):
    """True when d(i) != seqs[i](i) for every i - so d equals none of the listed sequences."""
    return all(d(i) != s(i) for i, s in enumerate(seqs))


def first_difference(a, b, length):
    """The first position n < length where sequences a and b differ, or None."""
    for n in range(length):
        if a(n) != b(n):
            return n
    return None


def diagonal_flip_rows(rows):
    """Diagonal trick on finite rows of digits: return [1 - rows[i][i] for each i].

    Raises ValueError when some row is shorter than the number of rows - the
    trick needs one position per row.
    """
    if any(len(row) < len(rows) for row in rows):
        raise ValueError("every row needs at least as many digits as there are rows")
    return [1 - row[i] for i, row in enumerate(rows)]


def show_row(digits, mark=None):
    """Digits separated by spaces, with the digit at position ``mark`` in [brackets]."""
    return "".join(f"[{x}]" if i == mark else f" {x} " for i, x in enumerate(digits))


def main():
    seqs = [rule for _, rule in SEQUENCES]
    width = 12
    print(f"A list of {len(seqs)} infinite binary sequences (first {width} digits shown).")
    print("The digit in [brackets] is row n, position n - the diagonal.")
    print()
    for i, (name, rule) in enumerate(SEQUENCES):
        print(f"  s{i} {name:<24}{show_row(prefix(rule, width), mark=i)} ...")
    d = diagonal_flip(seqs)
    diag = [d(n) for n in range(len(seqs))]
    print(f"  d  {'flip each [digit]':<24}{show_row(diag)}   (positions 0..{len(seqs) - 1})")
    print()
    print(f"d differs from s_n at position n, for every n in the list: {differs_from_every_row(seqs, d)}")
    firsts = [first_difference(d, s, len(seqs)) for s in seqs]
    print(f"First position where d and s0, s1, ... differ: {firsts}")
    print("(d may differ earlier than the diagonal; the diagonal guarantees a difference.)")
    reordered = list(reversed(seqs))
    d2 = diagonal_flip(reordered)
    print(f"Reverse the order of the list: new d = "
          f"{''.join(str(d2(n)) for n in range(len(seqs)))}, "
          f"still in no row: {differs_from_every_row(reordered, d2)}")
    print()
    rows = [list(bits) for bits in product((0, 1), repeat=3)]
    flipped = diagonal_flip_rows(rows[:3])
    where = rows.index(flipped)
    print("Finite caution: all 2^3 = 8 binary strings of length 3 CAN be listed.")
    print(f"Flipping the diagonal of the first 3 rows gives {''.join(map(str, flipped))}"
          f" - row {where} of that list:")
    print("the trick only beats one row per position, so it needs infinite sequences.")
    print()
    print(textwrap.fill(
        "Epistemic status: these checks are exact, but they only illustrate the "
        "mechanism on 8 sequences. The proof that no infinite list s0, s1, s2, ... "
        "contains every infinite binary sequence is Cantor's general argument, "
        "which applies to every such list at once; no program can check them all.",
        width=78,
    ))


if __name__ == "__main__":
    main()
