"""Two charts on the sphere, and the two transformation laws.

The 2-sphere is covered by the stereographic charts from the north and the
south pole. SymPy computes the transition map between them, its Jacobian
matrix J and its determinant, exactly. Then it takes a tangent vector and a
covector at one point, written in the first chart, and transforms them to the
second chart: vector components by J, covector components by the inverse
transpose of J. The pairing "covector applied to vector" comes out the same in
both charts, as it must; transforming the covector by J instead (the classic
mistake) gives a different number. This is exact symbolic computation for one
explicit chart change, not a proof of the general laws.
"""

import sympy

EXPERIMENT = {
    "id": "smooth_manifolds_transition_laws",
    "title": "Stereographic charts and the two transformation laws",
    "evidence": ["symbolic", "exact"],
    "lessons": ["smooth-manifolds"],
    "summary": (
        "Computes with SymPy the transition map between the two stereographic "
        "charts of the 2-sphere, its Jacobian and determinant, checks that it is "
        "smooth and its own inverse away from the origin, and shows exactly at "
        "one point that vectors transform by J and covectors by the inverse "
        "transpose of J, so that the pairing is chart-independent while the "
        "wrong rule is not."
    ),
    "packages": ["sympy"],
}

U, V = sympy.symbols("u v", real=True)


def north_inverse(u, v):
    """Inverse stereographic projection from the north pole: R^2 -> S^2."""
    r = u**2 + v**2
    return (2 * u / (r + 1), 2 * v / (r + 1), (r - 1) / (r + 1))


def south_chart(x, y, z):
    """Stereographic projection from the south pole: S^2 minus (0,0,-1) -> R^2."""
    return (x / (1 + z), y / (1 + z))


def transition():
    """The transition map south o north^-1, simplified, as a pair."""
    x, y, z = north_inverse(U, V)
    return tuple(sympy.simplify(c) for c in south_chart(x, y, z))


def jacobian(pair):
    """Jacobian matrix of a pair of expressions in (u, v)."""
    return sympy.Matrix(pair).jacobian([U, V])


def on_sphere(u, v):
    """x^2 + y^2 + z^2 - 1 for the image of (u, v): it should simplify to 0."""
    x, y, z = north_inverse(u, v)
    return sympy.simplify(x**2 + y**2 + z**2 - 1)


def transform(J, vector, covector):
    """New components: vectors by J, covectors by (J^-1)^T, and the wrong rule."""
    new_vector = J * vector
    new_covector = J.inv().T * covector
    wrong_covector = J * covector
    return new_vector, new_covector, wrong_covector


def pairing(covector, vector):
    """The number covector(vector) = sum of products of components."""
    return sympy.nsimplify((covector.T * vector)[0, 0])


def main():
    t = transition()
    J = jacobian(t)
    det = sympy.factor(J.det())
    print("Charts: north^-1(u, v) on the sphere?", on_sphere(U, V) == 0)
    print(f"Transition south o north^-1: {t}")
    print(f"Jacobian determinant: {det}")
    inv = sympy.simplify(jacobian(t).subs({U: t[0], V: t[1]}, simultaneous=True)
                         * J)
    print(f"J(T(p)) * J(p) = identity (T is its own inverse): {inv == sympy.eye(2)}")
    print()
    point = {U: 1, V: 2}
    Jp = J.subs(point)
    vector = sympy.Matrix([3, -1])
    covector = sympy.Matrix([2, 5])
    new_v, new_w, wrong_w = transform(Jp, vector, covector)
    print("At the point (u, v) = (1, 2) of the north chart:")
    print(f"  J = {Jp.tolist()}")
    print(f"  vector   {vector.T.tolist()[0]} -> {new_v.T.tolist()[0]} (by J)")
    print(f"  covector {covector.T.tolist()[0]} -> {new_w.T.tolist()[0]}"
          " (by inverse transpose)")
    print(f"  pairing in chart 1: {pairing(covector, vector)}")
    print(f"  pairing in chart 2: {pairing(new_w, new_v)}")
    print(f"  pairing if the covector is wrongly moved by J:"
          f" {pairing(wrong_w, new_v)}")
    print()
    print("The determinant is negative everywhere: these two charts reverse")
    print("orientation relative to each other. Composing one with (u, v) -> (u, -v)")
    print("gives an oriented atlas, so the sphere is orientable.")
    print()
    print("Epistemic status: exact symbolic computation (SymPy) for one chart")
    print("change and one point. It illustrates, but does not prove, the general")
    print("transformation laws, which follow from the chain rule.")


if __name__ == "__main__":
    main()
