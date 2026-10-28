"""Searching for inverses among the integers, and among the rationals.

For each integer n we search a window of integers m for an *additive inverse*
(n + m = 0) and a *multiplicative inverse* (n * m = 1). Additive inverses are
always found; multiplicative ones only for n = 1 and n = -1. Then we move to
the rational numbers, using ``fractions.Fraction`` for exact arithmetic, where
every non-zero number has a multiplicative inverse.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from fractions import Fraction
import textwrap

EXPERIMENT = {
    "id": "integer_inverses",
    "title": "Hunting for inverses in the integers and the rationals",
    "evidence": ["experimental", "exact"],
    "lessons": ["integers", "inverses-and-structure"],
    "summary": (
        "Searches a finite window of integers for additive and multiplicative "
        "inverses (every additive inverse is found; multiplicative ones only for "
        "1 and -1), then checks exactly with fractions that every non-zero "
        "rational has an inverse. A finite search is experimental evidence; the "
        "short size argument printed at the end is what proves that no other "
        "integer has a multiplicative inverse."
    ),
    "packages": [],
}


def window(radius):
    """Return the integers -radius..radius (inclusive) as a range."""
    if radius < 0:
        raise ValueError("radius must be non-negative")
    return range(-radius, radius + 1)


def find_additive_inverse(n, candidates):
    """Return the first m in ``candidates`` with n + m == 0, or None if none is found."""
    for m in candidates:
        if n + m == 0:
            return m
    return None


def find_multiplicative_inverse(n, candidates):
    """Return the first m in ``candidates`` with n * m == 1, or None if none is found.

    ``None`` only means "not found among the candidates": on its own a search
    cannot prove that no inverse exists further away.
    """
    for m in candidates:
        if n * m == 1:
            return m
    return None


def rational_inverse(q):
    """Return the exact multiplicative inverse 1/q of a rational q, or None when q == 0."""
    q = Fraction(q)
    if q == 0:
        return None
    return 1 / q


def search_summary(n_radius, m_radius):
    """Search every n in -n_radius..n_radius over candidates m in -m_radius..m_radius.

    Returns ``(additive_found, multiplicative_found)``: the lists of n for which
    an additive / multiplicative inverse was found.
    """
    candidates = window(m_radius)
    additive = [n for n in window(n_radius) if find_additive_inverse(n, candidates) is not None]
    multiplicative = [n for n in window(n_radius) if find_multiplicative_inverse(n, candidates) is not None]
    return additive, multiplicative


def main():
    candidates = window(50)
    print("For each n, search m in -50..50 for n + m = 0 and for n * m = 1.")
    print("Then, in the rationals Q, compute 1/n exactly with fractions.Fraction.")
    print()
    print(f"{'n':>4} | {'n + m = 0':>9} | {'n * m = 1':>9} | {'1/n in Q':>8} | n * (1/n)")
    print("-" * 52)
    for n in window(6):
        add = find_additive_inverse(n, candidates)
        mul = find_multiplicative_inverse(n, candidates)
        inv = rational_inverse(n)
        mul_s = "none" if mul is None else str(mul)
        inv_s = "none" if inv is None else str(inv)
        check = "-" if inv is None else str(n * inv)
        print(f"{n:>4} | {add:>9} | {mul_s:>9} | {inv_s:>8} | {check}")
    print()
    radius = 30
    additive, multiplicative = search_summary(radius, radius)
    total = 2 * radius + 1
    print(f"Wider search, n and m both in -{radius}..{radius}:")
    print(f"  additive inverse found for {len(additive)} of {total} integers")
    print(f"  multiplicative inverse found for {len(multiplicative)} of {total}: n = {multiplicative}")
    q = Fraction(-7, 12)
    print(f"  in Q, e.g. q = {q}: 1/q = {rational_inverse(q)} and q * (1/q) = {q * rational_inverse(q)} exactly")
    print()
    print("Why the integer search can stop: if |n| >= 2 and m != 0 then |n * m| >= 2,")
    print("and if m = 0 then n * m = 0. So n * m = 1 is impossible however far we look.")
    print()
    print(textwrap.fill(
        "Epistemic status: the searches are experiments over finite windows (a "
        "failed search alone proves nothing about numbers outside the window); "
        "the rational arithmetic is exact. The two-line size argument above, "
        "not the search, proves that only 1 and -1 have integer inverses.",
        width=78,
    ))


if __name__ == "__main__":
    main()
