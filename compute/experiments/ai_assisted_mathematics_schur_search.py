"""Generate and verify: searching for Schur colourings, and checking them exactly.

A k-colouring of {1, ..., n} is a Schur colouring if no colour class contains
x, y and x + y (x = y allowed). The Schur number S(k) is the largest n that has
one. This experiment plays both roles of an AI-assisted search loop:

1. an untrusted *generator*: seeded randomised local search (min-conflicts)
   proposes colourings;
2. an exact *verifier*: a short checker accepts or rejects each proposal.

It also shows the difference between a construction (a certificate, checked in
microseconds) and an optimality claim (no colouring of {1, ..., n + 1} exists),
which here needs an exhaustive search; and it turns each Schur colouring into
an edge colouring of the complete graph K_(n+1) with no monochromatic
triangle, the link to the multicolour Ramsey numbers of Erdos problem #183.
"""

import itertools
import random

EXPERIMENT = {
    "id": "ai_assisted_mathematics_schur_search",
    "title": "Generate and verify: local search for Schur colourings",
    "evidence": ["exact", "exhaustive-finite", "experimental"],
    "lessons": ["ai-assisted-mathematics"],
    "summary": (
        "Seeded local search proposes colourings of {1, ..., n} with no "
        "monochromatic x + y = z; an exact checker verifies each one. "
        "Exhaustive backtracking confirms S(2) = 4 and S(3) = 13, and each "
        "colouring is lifted to a triangle-free edge colouring of K_(n+1). "
        "Verified colourings are proofs of lower bounds; the search failing "
        "to find a colouring proves nothing."
    ),
    "packages": [],
}


def monochromatic_triples(colouring):
    """All (x, y, x + y) with x <= y that are monochromatic.

    ``colouring[x]`` is the colour of x for 1 <= x <= n; index 0 is unused.
    """
    n = len(colouring) - 1
    return [
        (x, y, x + y)
        for x in range(1, n + 1)
        for y in range(x, n + 1 - x)
        if colouring[x] == colouring[y] == colouring[x + y]
    ]


def is_schur_colouring(colouring):
    """The verifier: True if no colour class contains x, y and x + y."""
    return not monochromatic_triples(colouring)


def triples_containing(z, n):
    """Each triple (x, y, x + y) with x <= y, x + y <= n that contains z, once."""
    as_sum = [(x, z - x, z) for x in range(1, z // 2 + 1)]
    as_summand = [(min(z, w), max(z, w), z + w) for w in range(1, n - z + 1)]
    return as_sum + as_summand


def conflicts_at(colouring, z, colour):
    """Monochromatic triples that would contain z if z had the given colour."""
    n = len(colouring) - 1
    saved, colouring[z] = colouring[z], colour
    count = sum(
        1
        for x, y, s in triples_containing(z, n)
        if colouring[x] == colouring[y] == colouring[s]
    )
    colouring[z] = saved
    return count


def local_search(n, k, rng, max_steps=20000, noise=0.1):
    """Min-conflicts search for a Schur k-colouring of {1, ..., n}.

    Returns (colouring, steps) on success and (None, max_steps) on failure.
    """
    colouring = [0] + [rng.randrange(k) for _ in range(n)]
    for step in range(max_steps):
        bad = monochromatic_triples(colouring)
        if not bad:
            return colouring, step
        z = rng.choice(rng.choice(bad))
        if rng.random() < noise:
            colouring[z] = rng.randrange(k)
            continue
        scores = [conflicts_at(colouring, z, c) for c in range(k)]
        best = min(scores)
        colouring[z] = rng.choice([c for c in range(k) if scores[c] == best])
    return None, max_steps


def exhaustive_schur(k, n):
    """All Schur k-colourings of {1, ..., n}, up to renaming the colours.

    Backtracking; a new colour may be used only after all smaller ones, which
    removes the k! renamings of each colouring.
    """
    found = []
    colouring = [0] * (n + 1)

    def extend(z, used):
        if z > n:
            found.append(colouring[:])
            return
        for c in range(min(used + 1, k)):
            ok = all(
                not (colouring[x] == c and colouring[z - x] == c)
                for x in range(1, z // 2 + 1)
            )
            if ok:
                colouring[z] = c
                extend(z + 1, max(used, c + 1))
        colouring[z] = 0

    extend(1, 0)
    return found


def schur_number(k):
    """S(k): the largest n with a Schur k-colouring, by exhaustive search."""
    n = 1
    while exhaustive_schur(k, n + 1):
        n += 1
    return n


def triangle_free_lift(colouring):
    """Colour edge {i, j} of K_(n+1) (vertices 0..n) by colouring[|i - j|].

    Returns the number of monochromatic triangles (0 for a Schur colouring).
    """
    n = len(colouring) - 1
    return sum(
        1
        for i, j, l in itertools.combinations(range(n + 1), 3)
        if colouring[j - i] == colouring[l - j] == colouring[l - i]
    )


def classes(colouring, k):
    """The colour classes of a colouring, as sorted lists."""
    return [[x for x in range(1, len(colouring)) if colouring[x] == c] for c in range(k)]


def main():
    rng = random.Random(2026)
    print("1. Generate: local search for a Schur 3-colouring of {1, ..., 13}")
    colouring, steps = local_search(13, 3, rng)
    print(f"   found after {steps} steps; colour classes:")
    for cls in classes(colouring, 3):
        print(f"     {cls}")
    print(f"   verify: monochromatic x + y = z triples: "
          f"{len(monochromatic_triples(colouring))}")
    print(f"   lift to K_14: monochromatic triangles: "
          f"{triangle_free_lift(colouring)}  => R(3;3) >= 15")
    print()
    print("2. Optimality needs a different argument: exhaustive search")
    for k in (2, 3):
        s = schur_number(k)
        count = len(exhaustive_schur(k, s))
        print(f"   k = {k}: colourings of {{1..{s}}} up to renaming: {count}; "
              f"of {{1..{s + 1}}}: 0")
        print(f"   so S({k}) = {s}")
    print()
    print("3. Four colours (S(4) = 44, Baumert 1965): how far does search get?")
    best = 0
    for n in range(30, 45):
        found, _ = local_search(n, 4, rng, max_steps=4000)
        if found is None or not is_schur_colouring(found):
            break
        best = n
    print(f"   verified 4-colourings found for every n up to {best}")
    print(f"   so S(4) >= {best} is proved; the failure at n = {best + 1}")
    print("   is not evidence against: colourings exist for every n up to 44.")
    print()
    print("Epistemic status: every colouring printed is checked exactly, so")
    print("the lower bounds S(3) >= 13, S(4) >= the value shown and R(3;3) >= 15")
    print("are proved (given a correct checker). The values S(2) = 4 and")
    print("S(3) = 13 come from exhaustive search: a proof by exhaustion if the")
    print("code is right. The local search is a heuristic: its successes are")
    print("certificates, its failures are not evidence of non-existence.")


if __name__ == "__main__":
    main()
