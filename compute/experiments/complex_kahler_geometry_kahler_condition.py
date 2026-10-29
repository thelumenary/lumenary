"""Is a Hermitian metric Kahler? A symbolic check in coordinates.

A Hermitian metric on an open set of C^n is a positive definite Hermitian
matrix of functions g_{i jbar}; its fundamental form is
omega = (i/2) sum g_{i jbar} dz_i ^ dzbar_j, and omega is closed (the metric
is Kahler) exactly when d_k g_{i jbar} = d_i g_{k jbar} for all i, j, k
(together with the conjugate equations, which follow by symmetry).

We treat z and zbar as independent symbols, as in Wirtinger calculus, and
test three metrics on C^2: the flat metric, the Fubini-Study metric
g = d dbar log(1 + |z|^2) of the affine chart of CP^2 (Kahler, with Kahler
potential log(1 + |z|^2)), and the Hopf metric g = delta / |z|^2 on
C^2 minus 0, which is invariant under z -> 2z and so descends to the Hopf
surface S^1 x S^3, but is not Kahler. Finally SymPy integrates the
Fubini-Study area form of CP^1.

Evidence: symbolic computation with SymPy (exact, but relying on SymPy's
implementation of differentiation, simplification and integration).
"""

import sympy as sp

EXPERIMENT = {
    "id": "complex_kahler_geometry_kahler_condition",
    "title": "The Kahler condition in coordinates: Fubini-Study versus Hopf",
    "evidence": ["symbolic"],
    "lessons": ["complex-kahler-geometry"],
    "summary": (
        "Uses SymPy to test the Kahler condition d_k g_{i jbar} = d_i g_{k jbar} "
        "for three Hermitian metrics on C^2: flat, Fubini-Study (Kahler, with "
        "potential log(1 + |z|^2)) and the scale-invariant Hopf metric "
        "|dz|^2/|z|^2 (not Kahler). It also integrates the Fubini-Study area "
        "of CP^1, which is pi. Exact symbolic computation, trusted as far as "
        "SymPy's algebra is."
    ),
    "packages": ["sympy"],
}

Z = sp.symbols("z1 z2")
ZB = sp.symbols("zb1 zb2")


def from_potential(phi):
    """g_{i jbar} = d^2 phi / dz_i dzbar_j for a Kahler potential phi."""
    return sp.Matrix(2, 2, lambda i, j: sp.diff(phi, Z[i], ZB[j]))


def kahler_defects(g):
    """All nonzero d_k g_{i jbar} - d_i g_{k jbar}, simplified."""
    out = []
    for i in range(2):
        for j in range(2):
            for k in range(2):
                e = sp.simplify(sp.diff(g[i, j], Z[k]) - sp.diff(g[k, j], Z[i]))
                if e != 0:
                    out.append(((i + 1, j + 1, k + 1), e))
    return out


def is_hermitian_symbolically(g):
    """g_{j ibar} is the conjugate of g_{i jbar} (swapping z and zbar)."""
    swap = {**{Z[i]: ZB[i] for i in range(2)}, **{ZB[i]: Z[i] for i in range(2)}}
    return all(sp.simplify(g[j, i] - g[i, j].xreplace(swap)) == 0
               for i in range(2) for j in range(2))


def scale_invariant(g, factor=2):
    """Is g dz dzbar unchanged by z -> factor * z (g rescales by factor^-2)?"""
    sub = {**{Z[i]: factor * Z[i] for i in range(2)},
           **{ZB[i]: factor * ZB[i] for i in range(2)}}
    return all(sp.simplify(g[i, j].xreplace(sub) * factor ** 2 - g[i, j]) == 0
               for i in range(2) for j in range(2))


def fubini_study_area_cp1():
    """Integral over C of the Fubini-Study area density 1/(1 + r^2)^2."""
    r, t = sp.symbols("r t", positive=True)
    density = 1 / (1 + r ** 2) ** 2
    return sp.integrate(sp.integrate(density * r, (r, 0, sp.oo)), (t, 0, 2 * sp.pi))


def metrics():
    """The three test metrics on (an open subset of) C^2."""
    norm2 = Z[0] * ZB[0] + Z[1] * ZB[1]
    return [
        ("flat", sp.eye(2)),
        ("Fubini-Study", from_potential(sp.log(1 + norm2))),
        ("Hopf |dz|^2/|z|^2", sp.eye(2) / norm2),
    ]


def main():
    print(f"SymPy {sp.__version__}; z and zbar treated as independent symbols.")
    for name, g in metrics():
        defects = kahler_defects(g)
        print(f"{name}:")
        print(f"  Hermitian: {is_hermitian_symbolically(g)};"
              f" invariant under z -> 2z: {scale_invariant(g)}")
        if defects:
            (i, j, k), e = defects[0]
            print(f"  NOT Kahler: {len(defects)} nonzero defects, e.g.")
            print(f"  d_{k} g_{i}{j}bar - d_{i} g_{k}{j}bar = {e}")
        else:
            print("  Kahler: d_k g_(i jbar) = d_i g_(k jbar) for all i, j, k")
    fs = from_potential(sp.log(1 + Z[0] * ZB[0] + Z[1] * ZB[1]))
    print("Fubini-Study g_(1 1bar) =", sp.factor(fs[0, 0]))
    print("Fubini-Study area of CP^1 =", fubini_study_area_cp1())
    print()
    print("Epistemic status: exact symbolic computation, as reliable as")
    print("SymPy's differentiation, simplification and integration. A zero")
    print("defect is an identity of rational functions; it shows these")
    print("particular metrics are (or are not) Kahler, nothing more.")


if __name__ == "__main__":
    main()
