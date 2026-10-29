"""The Schwarzschild metric is Ricci-flat, and r = 2M is not a singularity.

Using SymPy we compute, from the metric
ds^2 = -(1 - 2M/r) dt^2 + dr^2/(1 - 2M/r) + r^2 (dtheta^2 + sin^2 theta dphi^2),
its Christoffel symbols, the Riemann tensor, the Ricci tensor (which
vanishes: the metric solves Einstein's vacuum equations) and the Kretschmann
scalar R_abcd R^abcd = 48 M^2 / r^6. The scalar is finite at the Schwarzschild
radius r = 2M, where the metric components blow up, and infinite only at
r = 0: the first is a coordinate artefact, the second a true singularity.
"""

import sympy as sp

EXPERIMENT = {
    "id": "relativity_schwarzschild_curvature",
    "title": "Schwarzschild: Ricci-flat, with finite curvature at r = 2M",
    "evidence": ["symbolic"],
    "lessons": ["relativity"],
    "summary": (
        "Computes with SymPy the Christoffel symbols, Riemann tensor, Ricci "
        "tensor and Kretschmann scalar of the Schwarzschild metric. The Ricci "
        "tensor simplifies to zero (a vacuum solution of Einstein's equations) "
        "and the Kretschmann scalar to 48 M^2/r^6, finite at r = 2M. Symbolic "
        "computation, relying on SymPy's simplification."
    ),
    "packages": ["sympy"],
}

T, R, TH, PH, M = sp.symbols("t r theta phi M", positive=True)
COORDS = [T, R, TH, PH]


def schwarzschild_metric():
    """The diagonal Schwarzschild metric in coordinates (t, r, theta, phi)."""
    f = 1 - 2 * M / R
    return sp.diag(-f, 1 / f, R ** 2, R ** 2 * sp.sin(TH) ** 2)


def christoffel(g):
    """Gamma[a][b][c] = (1/2) g^ad (d_c g_db + d_b g_dc - d_d g_bc)."""
    ginv = g.inv()
    n = g.shape[0]
    return [[[sp.simplify(sum(ginv[a, d] * (sp.diff(g[d, b], COORDS[c])
                                             + sp.diff(g[d, c], COORDS[b])
                                             - sp.diff(g[b, c], COORDS[d]))
                              for d in range(n)) / 2)
              for c in range(n)] for b in range(n)] for a in range(n)]


def riemann(gam):
    """R^a_bcd for c < d, as a dictionary {(a, b, c, d): expression}."""
    n = len(gam)
    out = {}
    for a in range(n):
        for b in range(n):
            for c in range(n):
                for d in range(c + 1, n):
                    e = (sp.diff(gam[a][b][d], COORDS[c])
                         - sp.diff(gam[a][b][c], COORDS[d]))
                    e += sum(gam[a][c][k] * gam[k][b][d]
                             - gam[a][d][k] * gam[k][b][c] for k in range(n))
                    out[(a, b, c, d)] = sp.simplify(e)
    return out


def component(riem, a, b, c, d):
    """R^a_bcd for any c, d, using antisymmetry in the last two indices."""
    if c == d:
        return 0
    return riem[(a, b, c, d)] if c < d else -riem[(a, b, d, c)]


def ricci(riem, n=4):
    """R_bd = R^a_bad."""
    return sp.Matrix(n, n, lambda b, d: sp.simplify(
        sum(component(riem, a, b, a, d) for a in range(n))))


def kretschmann(g, riem):
    """R_abcd R^abcd for a diagonal metric."""
    ginv = g.inv()
    total = sum(2 * g[a, a] * ginv[b, b] * ginv[c, c] * ginv[d, d] * v ** 2
                for (a, b, c, d), v in riem.items())
    return sp.simplify(total)


def main():
    g = schwarzschild_metric()
    gam = christoffel(g)
    nonzero = sum(1 for a in range(4) for b in range(4) for c in range(4)
                  if gam[a][b][c] != 0)
    print("Schwarzschild metric diag(-(1-2M/r), 1/(1-2M/r), r^2, r^2 sin^2):")
    print(f"  non-zero Christoffel symbols: {nonzero} of 64")
    print("  Gamma^r_tt =", gam[1][0][0])
    print("  Gamma^t_tr =", gam[0][0][1])
    riem = riemann(gam)
    print("  R^t_rtr =", riem[(0, 1, 0, 1)])
    ric = ricci(riem)
    print("  Ricci tensor is the zero matrix:", ric == sp.zeros(4, 4))
    k = kretschmann(g, riem)
    print("  Kretschmann scalar R_abcd R^abcd =", k)
    print("  at r = 2M:", sp.simplify(k.subs(R, 2 * M)),
          "  (finite: no curvature singularity at the horizon)")
    print("  g_rr =", sp.together(g[1, 1]),
          "  (blows up at r = 2M: the coordinates fail there)")
    print("  as r -> 0:", sp.limit(k, R, 0), " (a genuine singularity)")
    print()
    print("Epistemic status: symbolic computation; it is as reliable as")
    print("SymPy's differentiation and simplification. The vanishing of the")
    print("Ricci tensor is the classical theorem (Schwarzschild 1916) and the")
    print("Kretschmann scalar is a standard textbook result.")


if __name__ == "__main__":
    main()
