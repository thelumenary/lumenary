"""Gauss's Theorema Egregium checked symbolically, and Gauss-Bonnet numerically.

For a parametrised surface X(u, v) we compute, with SymPy, the first
fundamental form E, F, G and the (unnormalised) second fundamental form, and
from them the Gaussian curvature K = (LN - M^2) / (EG - F^2), which uses the
surface's shape in space. Separately we compute K from E, F, G alone by the
Brioschi formula, which only uses lengths measured on the surface. The
Theorema Egregium says the two always agree; here SymPy confirms it for five
surfaces. The catenoid and the helicoid have the same E, F, G, hence the same
K, although they look completely different in space. Finally we integrate
K dA numerically over an ellipsoid and compare with 2 pi chi = 4 pi.
Evidence: symbolic verification on examples, and a numerical integral.
"""

import math

import sympy

EXPERIMENT = {
    "id": "curves_surfaces_theorema_egregium",
    "title": "Theorema Egregium on examples, and Gauss-Bonnet for an ellipsoid",
    "evidence": ["symbolic", "numerical"],
    "lessons": ["curves-surfaces"],
    "summary": (
        "Computes with SymPy the fundamental forms and Gaussian curvature of a "
        "sphere, catenoid, helicoid, saddle and cylinder, both from the shape in "
        "space and from E, F, G alone (Brioschi's formula), and checks that they "
        "agree. It shows the catenoid and helicoid share E, F, G and K, and "
        "integrates K dA over an ellipsoid numerically, getting 4 pi. Symbolic "
        "and numerical evidence on examples only."
    ),
    "packages": ["sympy"],
}

U, V = sympy.symbols("u v", real=True)
R = sympy.symbols("R", positive=True)


def surfaces():
    """Name -> parametrisation X(u, v) as a SymPy column vector."""
    cos, sin, cosh, sinh = sympy.cos, sympy.sin, sympy.cosh, sympy.sinh
    return {
        "sphere (radius R)": sympy.Matrix([R * cos(V) * cos(U),
                                           R * cos(V) * sin(U), R * sin(V)]),
        "catenoid": sympy.Matrix([cosh(U) * cos(V), cosh(U) * sin(V), U]),
        "helicoid": sympy.Matrix([sinh(U) * cos(V), sinh(U) * sin(V), V]),
        "saddle z = uv": sympy.Matrix([U, V, U * V]),
        "cylinder": sympy.Matrix([cos(U), sin(U), V]),
    }


def first_form(X):
    """(E, F, G), simplified."""
    xu, xv = X.diff(U), X.diff(V)
    return tuple(sympy.simplify(e) for e in (xu.dot(xu), xu.dot(xv), xv.dot(xv)))


def extrinsic_curvature(X):
    """K = (LN - M^2) / (EG - F^2), using the normal vector Xu x Xv."""
    xu, xv = X.diff(U), X.diff(V)
    n = xu.cross(xv)
    l2, m2, n2 = (X.diff(U, 2).dot(n), xu.diff(V).dot(n), X.diff(V, 2).dot(n))
    w2 = n.dot(n)          # |Xu x Xv|^2 = EG - F^2
    return (l2 * n2 - m2 ** 2) / w2 ** 2


def brioschi(E, F, G):
    """Gaussian curvature from E, F, G and their derivatives only."""
    d = sympy.diff
    a = sympy.Matrix([
        [-d(E, V, 2) / 2 + d(F, U, V) - d(G, U, 2) / 2, d(E, U) / 2,
         d(F, U) - d(E, V) / 2],
        [d(F, V) - d(G, U) / 2, E, F],
        [d(G, V) / 2, F, G]])
    b = sympy.Matrix([
        [0, d(E, V) / 2, d(G, U) / 2],
        [d(E, V) / 2, E, F],
        [d(G, U) / 2, F, G]])
    return (a.det() - b.det()) / (E * G - F ** 2) ** 2


def ellipsoid_total_curvature(a, b, c, n=150):
    """Midpoint-rule integral of K dA over the ellipsoid with semi-axes a, b, c."""
    X = sympy.Matrix([a * sympy.cos(V) * sympy.cos(U),
                      b * sympy.cos(V) * sympy.sin(U), c * sympy.sin(V)])
    xu, xv = X.diff(U), X.diff(V)
    nrm = xu.cross(xv)
    num = (X.diff(U, 2).dot(nrm) * X.diff(V, 2).dot(nrm)
           - xu.diff(V).dot(nrm) ** 2)
    k_da = sympy.lambdify((U, V), num / nrm.dot(nrm) ** sympy.Rational(3, 2),
                          "math")
    du, dv = 2 * math.pi / n, math.pi / n
    return sum(k_da((i + 0.5) * du, -math.pi / 2 + (j + 0.5) * dv)
               for i in range(n) for j in range(n)) * du * dv


def main():
    print(f"Gaussian curvature two ways (SymPy {sympy.__version__})")
    rows = {}
    for name, X in surfaces().items():
        E, F, G = first_form(X)
        k_in = sympy.simplify(brioschi(E, F, G))
        agree = sympy.simplify(extrinsic_curvature(X) - k_in) == 0
        rows[name] = (E, F, G)
        print(f"  {name}:")
        print(f"    E = {E}, F = {F}, G = {G}")
        print(f"    K = {k_in}; from the shape in space too: {agree}")
    same = rows["catenoid"] == rows["helicoid"]
    print(f"  catenoid and helicoid have the same E, F, G: {same}")
    print()
    total = ellipsoid_total_curvature(2.0, 1.5, 1.0)
    print("Gauss-Bonnet for the ellipsoid with semi-axes 2, 1.5, 1:")
    print(f"  integral of K dA = {total / math.pi:.6f} pi  (2 pi chi = 4 pi)")
    print()
    print("Epistemic status: the agreements are symbolic verifications for")
    print("these five surfaces (as trustworthy as SymPy's simplifier); the")
    print("ellipsoid integral is numerical (150 x 150 midpoint rule). The")
    print("Theorema Egregium and the Gauss-Bonnet theorem are theorems (see the")
    print("lesson and do Carmo 1976), not consequences of this computation.")


if __name__ == "__main__":
    main()
