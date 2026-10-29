"""Lens spaces: when are L(p, q) and L(p, q') the same?

Every lens space L(p, q) has fundamental group Z/p and the same homology, so
algebraic topology's first tools cannot tell them apart. The classification
reduces the question to arithmetic modulo p:

* homeomorphic  <=> q' = +-q or q q' = +-1 (mod p)
  (Reidemeister 1935, piecewise-linear; Brody 1960, homeomorphism);
* homotopy equivalent <=> q q' = +-n^2 (mod p) for some n
  (J. H. C. Whitehead 1941).

We count the classes of both relations exhaustively for small p, find the
first pairs that are homotopy equivalent but not homeomorphic, and compute the
moduli |(z^k - 1)(z^(kr) - 1)|, z = exp(2 pi i / p), qr = 1 (mod p), which
appear in the Reidemeister torsion, the invariant that tells them apart.
"""

import cmath
import math

EXPERIMENT = {
    "id": "low_dimensional_topology_lens_spaces",
    "title": "Lens spaces: homeomorphism versus homotopy, by arithmetic",
    "evidence": ["exact", "exhaustive-finite", "numerical"],
    "lessons": ["low-dimensional-topology"],
    "summary": (
        "Applies the classification criteria for lens spaces L(p, q) (homeomorphic "
        "iff q' = +-q^(+-1) mod p; homotopy equivalent iff qq' = +-n^2 mod p) to "
        "every p up to 15, counting the classes and listing the pairs that are "
        "homotopy equivalent but not homeomorphic, and evaluates the torsion "
        "moduli that distinguish L(7, 1) from L(7, 2). Exact and exhaustive for "
        "the arithmetic; the topology is cited, not computed."
    ),
    "packages": [],
}


def units(p):
    """Residues 1 <= q < p coprime to p."""
    return [q for q in range(1, p) if math.gcd(q, p) == 1]


def inverse(q, p):
    """Inverse of q modulo p."""
    return pow(q, -1, p)


def homeomorphic(p, q, r):
    """Reidemeister-Brody criterion: r = +-q or r = +-q^(-1) (mod p)."""
    qi = inverse(q, p)
    return r % p in {q % p, -q % p, qi, -qi % p}


def homotopy_equivalent(p, q, r):
    """Whitehead's criterion: q r = +-n^2 (mod p) for some unit n."""
    squares = {n * n % p for n in units(p)}
    return q * r % p in squares or -q * r % p in squares


def classes(p, relation):
    """Partition the units mod p into classes of an equivalence relation."""
    out = []
    for q in units(p):
        for c in out:
            if relation(p, c[0], q):
                c.append(q)
                break
        else:
            out.append([q])
    return out


def torsion_moduli(p, q):
    """Sorted moduli |(z^k - 1)(z^(k r) - 1)| for k = 1..p-1, rounded."""
    r = inverse(q, p)
    z = [cmath.exp(2j * math.pi * k / p) for k in range(p)]
    vals = [abs((z[k] - 1) * (z[k * r % p] - 1)) for k in range(1, p)]
    return sorted(round(v, 6) for v in vals)


def main():
    print("Lens spaces L(p, q), 0 < q < p, gcd(p, q) = 1 (all have pi_1 = Z/p)")
    print("  p  units  homeomorphism classes  homotopy classes")
    surprises = []
    for p in range(2, 16):
        h = classes(p, homeomorphic)
        e = classes(p, homotopy_equivalent)
        print(f"{p:3d}  {len(units(p)):5d}  {len(h):21d}  {len(e):16d}")
        for q in units(p):
            for r in units(p):
                if q < r and homotopy_equivalent(p, q, r) and \
                        not homeomorphic(p, q, r):
                    surprises.append((p, q, r))
    print(f"{len(surprises)} pairs (p <= 15) are homotopy equivalent but not "
          "homeomorphic; the first:")
    print("  " + ", ".join(f"L({p},{q}) ~ L({p},{r})"
                           for p, q, r in surprises[:3]))
    print(f"L(5,1), L(5,2) homotopy equivalent? {homotopy_equivalent(5, 1, 2)}")
    print()
    print("Torsion moduli |(z^k - 1)(z^(kr) - 1)|, k = 1..6, for p = 7:")
    for q in (1, 2, 4):
        print(f"  L(7,{q}): " + " ".join(f"{v:.4f}" for v in torsion_moduli(7, q)))
    print("L(7,2) and L(7,4) agree (4 = 2^(-1) mod 7); L(7,1) differs.")
    print()
    print("Epistemic status: the class counts are exact and exhaustive for the")
    print("arithmetic criteria with p <= 15. That these criteria classify lens")
    print("spaces up to homeomorphism and homotopy equivalence is the theorem of")
    print("Reidemeister, Brody and Whitehead, cited and not verified here. The")
    print("torsion moduli are floating-point values, illustrating why the torsion")
    print("distinguishes L(7,1) from L(7,2); they are not a proof.")


if __name__ == "__main__":
    main()
