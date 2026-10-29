"""Curvature from the metric alone, and the Gauss-Bonnet theorem.

For a surface with metric g = E du^2 + 2F du dv + G dv^2, SymPy computes the
Christoffel symbols, the curvature tensor component R_1212 and the Gaussian
curvature K = R_1212 / det g, using nothing but derivatives of E, F, G: this
is Gauss's Theorema Egregium put to work. It treats the round sphere, the
hyperbolic upper half-plane, the Poincare disc and a torus of revolution, then
integrates K dA over the sphere and the torus and compares with 2*pi*chi.
Everything is exact symbolic computation for these specific metrics.
"""

import sympy

EXPERIMENT = {
    "id": "riemannian_geometry_curvature",
    "title": "Gaussian curvature from the metric, and Gauss-Bonnet",
    "evidence": ["symbolic", "exact"],
    "lessons": ["riemannian-geometry"],
    "summary": (
        "Computes with SymPy the Christoffel symbols and Gaussian curvature of a "
        "surface from its metric coefficients alone (the Theorema Egregium in "
        "action): round sphere K = 1, upper half-plane and Poincare disc K = -1, "
        "torus of revolution K = cos v / (r (R + r cos v)). Then integrates K dA "
        "over the sphere and the torus: 4 pi and 0, that is 2 pi chi."
    ),
    "packages": ["sympy"],
}

U, V = sympy.symbols("u v", real=True)


def christoffel(g):
    """Christoffel symbols Gamma[k][i][j] of a 2x2 metric matrix in (u, v)."""
    coords = (U, V)
    ginv = g.inv()
    gamma = [[[0, 0], [0, 0]] for _ in range(2)]
    for k in range(2):
        for i in range(2):
            for j in range(2):
                gamma[k][i][j] = sympy.simplify(sum(
                    ginv[k, m] * (sympy.diff(g[j, m], coords[i])
                                  + sympy.diff(g[i, m], coords[j])
                                  - sympy.diff(g[i, j], coords[m])) / 2
                    for m in range(2)))
    return gamma


def gaussian_curvature(g):
    """K = R_1212 / det g with R(d1, d2)d2 written via Christoffel symbols."""
    coords = (U, V)
    gam = christoffel(g)
    # R_1212 = <R(d_u, d_v) d_v, d_u> = sum over m of g_{um} R^m_{vuv}.
    def riem(m, i, j, k):
        """R^m_{ijk}: component of R(d_j, d_k) d_i on d_m."""
        val = sympy.diff(gam[m][k][i], coords[j]) - sympy.diff(gam[m][j][i], coords[k])
        val += sum(gam[m][j][p] * gam[p][k][i] - gam[m][k][p] * gam[p][j][i]
                   for p in range(2))
        return val
    r1212 = sum(g[0, m] * riem(m, 1, 0, 1) for m in range(2))
    return sympy.simplify(r1212 / g.det())


def integral_of_curvature(g, u_range, v_range):
    """The integral of K dA = K sqrt(det g) du dv over a coordinate rectangle."""
    density = sympy.simplify(gaussian_curvature(g) * sympy.sqrt(g.det()))
    return sympy.simplify(sympy.integrate(density, (U, *u_range), (V, *v_range)))


def main():
    big, small = sympy.Rational(2), sympy.Rational(1)
    sphere = sympy.Matrix([[1, 0], [0, sympy.sin(U) ** 2]])
    half_plane = sympy.Matrix([[1 / V**2, 0], [0, 1 / V**2]])
    disc_factor = 4 / (1 - U**2 - V**2) ** 2
    disc = sympy.Matrix([[disc_factor, 0], [0, disc_factor]])
    torus = sympy.Matrix([[(big + small * sympy.cos(V)) ** 2, 0], [0, small**2]])
    print("Gaussian curvature computed from the metric alone:")
    rows = [("round sphere  du^2 + sin(u)^2 dv^2", sphere),
            ("half-plane   (du^2 + dv^2)/v^2", half_plane),
            ("Poincare disc 4(du^2 + dv^2)/(1-u^2-v^2)^2", disc),
            ("torus (2 + cos v)^2 du^2 + dv^2", torus)]
    for name, g in rows:
        print(f"  {name:<44} K = {gaussian_curvature(g)}")
    gam = christoffel(half_plane)
    print("Half-plane Christoffel symbols (nonzero):")
    for k in range(2):
        for i in range(2):
            for j in range(i, 2):
                if gam[k][i][j] != 0:
                    print(f"  Gamma^{'uv'[k]}_{'uv'[i]}{'uv'[j]} = {gam[k][i][j]}")
    print()
    total_sphere = integral_of_curvature(sphere, (0, sympy.pi), (0, 2 * sympy.pi))
    total_torus = integral_of_curvature(torus, (0, 2 * sympy.pi),
                                        (0, 2 * sympy.pi))
    print(f"Integral of K dA over the sphere: {total_sphere}  (2 pi chi = 4 pi)")
    print(f"Integral of K dA over the torus:  {total_torus}  (2 pi chi = 0)")
    print()
    print("Epistemic status: exact symbolic computation for four explicit metrics")
    print("and two integrals. It illustrates the Theorema Egregium and checks the")
    print("Gauss-Bonnet theorem in two cases; the theorem itself is proved in the")
    print("lesson.")


if __name__ == "__main__":
    main()
