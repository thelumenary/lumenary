"""Reading a terse proof with a computer: Zagier's one-sentence proof.

Zagier (1990) proved that every prime p = 1 (mod 4) is a sum of two squares
in one sentence: an explicit involution of the finite set
S = {(x, y, z) in positive integers : x^2 + 4yz = p} has exactly one fixed
point, so |S| is odd, so the involution (x, y, z) -> (x, z, y) has a fixed
point too, giving p = x^2 + (2y)^2. The experiment checks every claim of the
sentence for all primes p = 1 (mod 4) below 3000 and then runs the same
machinery on numbers for which a hypothesis fails - p = 3 (mod 4), composite
numbers and squares - to see exactly where each hypothesis is used. This is
exhaustive-finite evidence that we have read the proof correctly; the proof
itself is the human argument (and the lesson's Lean formalisation).
"""

import math

EXPERIMENT = {
    "id": "reading_literature_zagier",
    "title": "Checking every claim of Zagier's one-sentence proof",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["reading-literature"],
    "summary": (
        "Builds the set S = {x^2 + 4yz = n} and Zagier's involution, and checks for "
        "every prime p = 1 mod 4 below 3000 that the map is an involution of S "
        "with exactly one fixed point, that |S| is odd and that the swap gives "
        "p = a^2 + b^2. Running the same code on composites, squares and primes "
        "3 mod 4 shows where each hypothesis of the theorem is used."
    ),
    "packages": [],
}


def zagier_set(n):
    """All (x, y, z) of positive integers with x^2 + 4yz = n."""
    out = []
    for x in range(1, math.isqrt(n) + 1):
        rest = n - x * x
        if rest <= 0 or rest % 4:
            continue
        m = rest // 4
        out.extend((x, y, m // y) for y in range(1, m + 1) if m % y == 0)
    return out


def zagier_map(t):
    """Zagier's map; None on the boundary x = y - z or x = 2y."""
    x, y, z = t
    if x < y - z:
        return (x + 2 * z, z, y - x - z)
    if y - z < x < 2 * y:
        return (2 * y - x, y, x - y + z)
    if x > 2 * y:
        return (x - 2 * y, x - y + z, y)
    return None


def analyse(n):
    """Facts about S for the number n (a dict)."""
    s = zagier_set(n)
    members = set(s)
    images = {t: zagier_map(t) for t in s}
    boundary = [t for t, u in images.items() if u is None]
    involution = not boundary and all(
        images[t] in members and images[images[t]] == t for t in s)
    fixed = sorted(t for t, u in images.items() if u == t)
    swap_fixed = sorted(t for t in s if t[1] == t[2])
    squares = sorted({tuple(sorted((x, 2 * y))) for x, y, _ in swap_fixed})
    return {"size": len(s), "boundary": len(boundary),
            "involution": involution, "fixed": fixed,
            "swap_fixed": swap_fixed, "squares": squares}


def is_prime(n):
    """Trial division (n is small here)."""
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


def check_primes(limit):
    """Check all claims of the proof for primes p = 1 (mod 4) below limit."""
    primes = [p for p in range(5, limit, 4) if is_prime(p)]
    bad = []
    for p in primes:
        a = analyse(p)
        ok = (a["involution"] and a["fixed"] == [(1, 1, (p - 1) // 4)]
              and a["size"] % 2 == 1 and a["squares"])
        if not ok:
            bad.append(p)
    return len(primes), bad


def main():
    count, bad = check_primes(3000)
    print(f"Primes p = 1 (mod 4) below 3000: {count}; claims failing for: "
          f"{bad if bad else 'none'}")
    print("(involution of S, unique fixed point (1, 1, (p-1)/4), |S| odd,")
    print(" and a fixed point of the swap giving p = a^2 + b^2)")
    print()
    print(f"{'n':>4} {'kind':<12}{'|S|':>4} {'bnd':>4}  {'Zagier fixed pts':<28}"
          f"{'n = a^2 + b^2'}")
    cases = [(13, "prime 1 mod 4"), (97, "prime 1 mod 4"),
             (19, "prime 3 mod 4"), (21, "3 * 7"), (45, "3^2 * 5"),
             (65, "5 * 13"), (9, "square"), (25, "square")]
    for n, kind in cases:
        a = analyse(n)
        fixed = ", ".join(f"({x},{y},{z})" for x, y, z in a["fixed"]) or "-"
        sq = ", ".join(f"{u}^2+{v}^2" for u, v in a["squares"]) or "-"
        print(f"{n:>4} {kind:<12}{a['size']:>4} {a['boundary']:>4}  "
              f"{fixed:<28}{sq}")
    print()
    print("bnd = points on Zagier's boundary, where his map is undefined.")
    print("p = 3 mod 4: S is empty (x^2 + 4yz is 1 mod 4). Composites: one fixed")
    print("point per factorisation n = x(x + 4z), so |S| may be even (21, 65)")
    print("or odd (45). Squares: boundary points appear and the map is not an")
    print("involution of S. Primality is what makes the fixed point unique.")
    print()
    print("Epistemic status: exhaustive-finite checks of each step of the proof")
    print("for all primes below 3000, plus counterexamples showing that the")
    print("hypotheses are used. This tests our reading of the proof; it does not")
    print("replace the proof, which is checked in full in the Lean module.")


if __name__ == "__main__":
    main()
