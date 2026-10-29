"""Stress-testing a published proof before (and after) formalising it.

Don Zagier's one-sentence proof (1990) that every prime p = 1 (mod 4) is a
sum of two squares uses an involution of the finite set
S = {(x, y, z) : x^2 + 4yz = p} with exactly one fixed point. Before
formalising such a proof it pays to test every claim it makes on many cases,
and to see which hypothesis each claim needs.

For every prime p = 1 (mod 4) below a bound we compute S, apply Zagier's map,
and check: no triple lies on a boundary between the three cases, the map sends
S into S and is an involution, it has exactly one fixed point (1, 1, k), |S|
is odd, and the swap (x, y, z) -> (x, z, y) has a fixed point giving
p = x^2 + (2y)^2. Then we run the same checks on numbers n = 1 (mod 4) that
are not prime, to see exactly where the argument breaks. Triples are taken
with positive coordinates; with 0 allowed, S is infinite when n is a square.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from math import isqrt
import textwrap

EXPERIMENT = {
    "id": "formalising_published_mathematics_zagier",
    "title": "Zagier's involution, tested claim by claim",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["formalising-published-mathematics"],
    "summary": (
        "Checks every claim of Zagier's one-sentence proof - no boundary cases, "
        "the map preserves S and is an involution, exactly one fixed point, |S| odd, "
        "the swap has a fixed point - for all primes p = 1 (mod 4) below 3000, and "
        "shows where the argument fails for composite n = 1 (mod 4). Exhaustive for "
        "these finitely many cases; the proof for all primes is in the lesson and "
        "in Lean."
    ),
    "packages": [],
}


def is_prime(n):
    """Trial-division primality test."""
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def zagier_set(n):
    """All (x, y, z) with x, y, z >= 1 and x^2 + 4yz = n, sorted."""
    triples = []
    for x in range(1, isqrt(n) + 1):
        rest = n - x * x
        if rest <= 0 or rest % 4:
            continue
        m = rest // 4
        triples.extend((x, y, m // y) for y in range(1, m + 1) if m % y == 0)
    return sorted(triples)


def on_boundary(t):
    """Is t on a boundary between Zagier's cases (x = y - z or x = 2y)?"""
    x, y, z = t
    return x == y - z or x == 2 * y


def zagier_map(t):
    """Zagier's piecewise map, with the paper's three cases."""
    x, y, z = t
    if x < y - z:
        return (x + 2 * z, z, y - x - z)
    if x < 2 * y:
        return (2 * y - x, y, x - y + z)
    return (x - 2 * y, x - y + z, y)


def swap(t):
    """The obvious involution (x, y, z) -> (x, z, y)."""
    x, y, z = t
    return (x, z, y)


def audit(n):
    """Check each claim of the proof for n; return a dict of findings."""
    s = zagier_set(n)
    members = set(s)
    images = [zagier_map(t) for t in s]
    fixed = [t for t, u in zip(s, images) if u == t]
    swap_fixed = [t for t in s if swap(t) == t]
    return {
        "size": len(s),
        "boundary": [t for t in s if on_boundary(t)],
        "maps_into": all(u in members for u in images),
        "involution": all(zagier_map(u) == t for t, u in zip(s, images)),
        "fixed": fixed,
        "swap_fixed": swap_fixed,
        "squares": [(x, 2 * y) for x, y, _ in swap_fixed],
    }


def claims_hold(n, report):
    """Do all claims of Zagier's sentence hold for n = 4k + 1?"""
    k = (n - 1) // 4
    return (not report["boundary"] and report["maps_into"]
            and report["involution"] and report["fixed"] == [(1, 1, k)]
            and report["size"] % 2 == 1 and len(report["swap_fixed"]) >= 1)


def main():
    bound = 3000
    primes = [p for p in range(5, bound, 4) if is_prime(p)]
    good = [p for p in primes if claims_hold(p, audit(p))]
    sizes = [audit(p)["size"] for p in primes]
    print(f"Primes p = 1 (mod 4) below {bound}: {len(primes)}")
    print(f"All claims of the sentence hold for {len(good)} of them")
    print(f"|S| ranges from {min(sizes)} to {max(sizes)}; always odd: "
          f"{all(m % 2 for m in sizes)}")
    for p in primes[:3] + [primes[-1]]:
        r = audit(p)
        a, b = r["squares"][0]
        print(f"   p = {p:>4}: |S| = {r['size']:>3}, fixed point {r['fixed'][0]},"
              f" p = {a}^2 + {b}^2")
    print()
    print("Composite n = 1 (mod 4): which claims fail?")
    print("   (fixed = fixed points of Zagier's map; boundary = triples on a")
    print("   boundary between its cases; leaves S = some image is not in S)")
    for n in [9, 21, 25, 45, 65, 85]:
        r = audit(n)
        notes = [f"|S| = {r['size']}", f"fixed {len(r['fixed'])}"]
        if r["boundary"]:
            notes.append(f"boundary {len(r['boundary'])}")
        if not r["maps_into"]:
            notes.append("leaves S")
        if not r["involution"]:
            notes.append("not an involution")
        found = "yes" if r["squares"] else "no"
        print(f"   n = {n}: {', '.join(notes)}; swap fixed point: {found}")
    print()
    print(textwrap.fill(
        "Epistemic status: exact, exhaustive checks for the finitely many "
        "primes below 3000. They are evidence that each claim of the sentence "
        "is right, and the composite cases show which hypothesis each claim "
        "uses (n not a square, n prime), but they prove nothing about larger "
        "primes. Note n = 65: the argument fails (two fixed points), yet 65 is "
        "a sum of two squares - a failed proof says nothing about the truth of "
        "its conclusion. The proof for every prime is in the lesson, and Lean "
        "checks it.",
        width=78,
    ))


if __name__ == "__main__":
    main()
