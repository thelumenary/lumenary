"""Hodge numbers of hypersurfaces by counting monomials.

For a smooth hypersurface X of degree d in complex projective space P^(n+1)
(so dim X = n), Griffiths' theorem identifies the primitive middle Hodge
numbers with graded pieces of the Jacobian ring C[x_0..x_(n+1)]/(dF/dx_i).
For the Fermat polynomial F = sum x_i^d the Jacobian ideal is (x_i^(d-1)),
so a basis is given by monomials with every exponent at most d - 2, and

    h^(n-q, q)_prim = #{monomials of degree (q+1)d - (n+2), exponents <= d-2}.

We count them exactly, assemble the Hodge diamond (the other entries come
from the Lefschetz hyperplane theorem), and check it against an independent
computation of the Euler characteristic from Chern classes:
chi(X) = d * [H^n] (1 + H)^(n+2) / (1 + d H).

Evidence: exact integer computation of numbers that theorems (Griffiths,
Lefschetz, Chern-Gauss-Bonnet) identify with Hodge numbers and Euler
characteristics. The agreement of the two formulas is a consistency check.
"""

from math import comb

EXPERIMENT = {
    "id": "complex_kahler_geometry_hodge_numbers",
    "title": "Hodge diamonds of hypersurfaces by counting monomials",
    "evidence": ["exact"],
    "lessons": ["complex-kahler-geometry"],
    "summary": (
        "Counts monomials in the Jacobian ring of a Fermat hypersurface to get "
        "its middle Hodge numbers (Griffiths' theorem), builds the Hodge "
        "diamond of curves, the quartic K3 surface and the quintic threefold "
        "(h^{2,1} = 101), and checks the Euler characteristic against the "
        "Chern-class formula and the Hodge symmetries. Exact arithmetic; the "
        "theorems that give these numbers their meaning are cited, not proved."
    ),
    "packages": [],
}


def bounded_compositions(total, parts, cap):
    """Number of (a_1..a_parts) with 0 <= a_i <= cap and sum total."""
    if total < 0:
        return 0
    ways = [1] + [0] * total
    for _ in range(parts):
        new = [0] * (total + 1)
        for s, w in enumerate(ways):
            if w:
                for a in range(min(cap, total - s) + 1):
                    new[s + a] += w
        ways = new
    return ways[total]


def primitive_middle(n, d):
    """[h^(n,0)_prim, h^(n-1,1)_prim, ..., h^(0,n)_prim] for degree d in P^(n+1)."""
    return [bounded_compositions((q + 1) * d - (n + 2), n + 2, d - 2)
            for q in range(n + 1)]


def hodge_diamond(n, d):
    """Dict (p, q) -> h^(p,q) for a smooth degree-d hypersurface of dim n."""
    h = {(p, q): 0 for p in range(n + 1) for q in range(n + 1)}
    for p in range(n + 1):
        if 2 * p != n:
            h[(p, p)] = 1  # Lefschetz: powers of the hyperplane class
    for q, value in enumerate(primitive_middle(n, d)):
        h[(n - q, q)] += value
    if n % 2 == 0:
        h[(n // 2, n // 2)] += 1  # the hyperplane class in the middle
    return h


def betti(h, n):
    """Betti numbers b_k = sum_{p+q=k} h^(p,q)."""
    return [sum(h[(p, k - p)] for p in range(n + 1) if 0 <= k - p <= n)
            for k in range(2 * n + 1)]


def euler_from_hodge(h):
    """chi = sum (-1)^(p+q) h^(p,q)."""
    return sum((-1) ** (p + q) * v for (p, q), v in h.items())


def euler_from_chern(n, d):
    """chi = d * coefficient of H^n in (1 + H)^(n+2) / (1 + dH)."""
    return d * sum(comb(n + 2, k) * (-d) ** (n - k) for k in range(n + 1))


def symmetric(h, n):
    """Hodge symmetry h^(p,q) = h^(q,p) and Serre duality h^(p,q) = h^(n-p,n-q)."""
    return all(h[(p, q)] == h[(q, p)] == h[(n - p, n - q)] for p, q in h)


def diamond_lines(h, n, width=5):
    """The Hodge diamond as centred text lines, h^(n,n) at the top."""
    lines = []
    for k in range(2 * n, -1, -1):
        row = [h[(p, k - p)] for p in range(n, -1, -1) if 0 <= k - p <= n]
        text = "".join(f"{v:^{width}}" for v in row)
        lines.append(text.center(width * (n + 1)).rstrip())
    return lines


CASES = [
    ("plane cubic (elliptic curve)", 1, 3),
    ("plane quartic curve", 1, 4),
    ("quartic surface (K3)", 2, 4),
    ("quintic surface", 2, 5),
    ("cubic threefold", 3, 3),
    ("quintic threefold (Calabi-Yau)", 3, 5),
]


def main():
    print(f"{'hypersurface':<31}{'n':>2}{'d':>3}  {'middle h^(n-q,q)':<17}"
          f"{'chi Hodge':>10}{'chi Chern':>10}")
    for name, n, d in CASES:
        h = hodge_diamond(n, d)
        middle = ",".join(str(h[(n - q, q)]) for q in range(n + 1))
        print(f"{name:<31}{n:>2}{d:>3}  {middle:<17}"
              f"{euler_from_hodge(h):>10}{euler_from_chern(n, d):>10}")
        assert symmetric(h, n)
        assert all(b % 2 == 0 for b in betti(h, n)[1::2])
    print("All diamonds satisfy h^(p,q) = h^(q,p) = h^(n-p,n-q), and every")
    print("odd Betti number is even.")
    for title, n, d in [("Quartic K3 surface:", 2, 4),
                        ("Quintic threefold:", 3, 5)]:
        h = hodge_diamond(n, d)
        print()
        print(f"{title} Betti numbers {betti(h, n)}")
        for line in diamond_lines(h, n):
            print("    " + line)
    print()
    print("Epistemic status: exact integer counts. That they are Hodge numbers")
    print("is Griffiths' theorem on the Jacobian ring and the Lefschetz")
    print("hyperplane theorem, cited not proved here; the match with the")
    print("Chern-class Euler characteristic is an independent consistency check.")


if __name__ == "__main__":
    main()
