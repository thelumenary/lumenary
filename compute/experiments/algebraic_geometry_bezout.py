"""Bezout's theorem by resultants: counting intersections of plane curves.

Two projective plane curves F = 0 and G = 0 of degrees d and e, with no common
component, meet in exactly d*e points of the complex projective plane,
counted with multiplicity. To see the count, we change coordinates so that
the point [0:0:1] lies on neither curve and eliminate z: the resultant
Res_z(F, G) is a binary form of degree d*e in x and y, and its roots are the
directions from [0:0:1] to the intersection points. Each irreducible factor of
degree m over Q stands for m conjugate points; its exponent is their
intersection multiplicity (tangency, points at infinity and complex points
all appear). We use two different coordinate changes and check that the
pattern of factors agrees - a consistency check of genericity. Exact symbolic
computation with SymPy; evidence for these examples, not a proof of Bezout.
"""

import sympy

EXPERIMENT = {
    "id": "algebraic_geometry_bezout",
    "title": "Bezout's theorem by resultants",
    "evidence": ["exact", "symbolic"],
    "lessons": ["algebraic-geometry"],
    "summary": (
        "For ten pairs of projective plane curves (lines, circles, a parabola, "
        "cuspidal and nodal cubics, an elliptic curve) computes the resultant "
        "after a generic change of coordinates, factors it over Q and reads off "
        "how many intersection points there are and with which multiplicities; "
        "the total is always d*e. Exact symbolic computation for these "
        "examples; the lesson explains and partly proves Bezout's theorem."
    ),
    "packages": ["sympy"],
}

X, Y, Z = sympy.symbols("x y z")

#: Two invertible linear changes of coordinates (old variables in terms of new).
CHANGES = (
    {X: X + 2 * Z, Y: X + Y + 5 * Z, Z: X - Y + 3 * Z},
    {X: 2 * X + Y + Z, Y: Y - 5 * Z, Z: X + 3 * Y + Z},
)

CIRCLE = X**2 + Y**2 - Z**2

#: (description, F, G): homogeneous polynomials in x, y, z.
EXAMPLES = [
    ("circle, line y = 0 (2 real points)", CIRCLE, Y),
    ("circle, tangent line y = 1", CIRCLE, Y - Z),
    ("circle, line x = 2 (2 complex points)", CIRCLE, X - 2 * Z),
    ("concentric circles (circular points)", CIRCLE, X**2 + Y**2 - 4 * Z**2),
    ("circles x^2+y^2=1, x^2+y^2=2x", CIRCLE, X**2 - 2 * X * Z + Y**2),
    ("parabola y = x^2, line at infinity", Y * Z - X**2, Z),
    ("cusp y^2 = x^3, its tangent y = 0", Y**2 * Z - X**3, Y),
    ("cusp y^2 = x^3, line x = 0", Y**2 * Z - X**3, X),
    ("node y^2 = x^2(x+1), line y = 2x", Y**2 * Z - X**2 * (X + Z), Y - 2 * X),
    ("elliptic y^2 = x^3-x, circle r = 2", Y**2 * Z - X**3 + X * Z**2,
     X**2 + Y**2 - 4 * Z**2),
]


def degree(f):
    """Total degree of a homogeneous polynomial in x, y, z."""
    return sympy.Poly(f, X, Y, Z).total_degree()


def change_coordinates(f, change):
    """Substitute the linear change of coordinates into f and expand."""
    return sympy.expand(f.subs(change, simultaneous=True))


def is_generic(f, g):
    """True if [0:0:1] lies on neither curve (so Res_z has full degree)."""
    point = {X: 0, Y: 0, Z: 1}
    return f.subs(point) != 0 and g.subs(point) != 0


def intersection_pattern(f, g, change):
    """Sorted (number of points, multiplicity) pairs read off Res_z(f, g)."""
    fc, gc = change_coordinates(f, change), change_coordinates(g, change)
    if not is_generic(fc, gc):
        raise ValueError("[0:0:1] lies on a curve: choose another change")
    res = sympy.resultant(fc, gc, Z)
    if res == 0:
        raise ValueError("the curves have a common component")
    _, factors = sympy.factor_list(res)
    return sorted((sympy.Poly(h, X, Y).total_degree(), m) for h, m in factors)


def total(pattern):
    """Number of intersection points counted with multiplicity."""
    return sum(points * mult for points, mult in pattern)


def describe(pattern):
    """Human-readable form, e.g. '2 pts x1' or '1 pt x2 + 1 pt x1'."""
    parts = []
    for points, mult in sorted(pattern, key=lambda pm: (-pm[1], pm[0])):
        word = "pt" if points == 1 else "pts"
        parts.append(f"{points} {word} x{mult}")
    return " + ".join(parts)


def main():
    print("Intersections in the complex projective plane (multiplicity xm)")
    print(f"{'curves':<38} {'d*e':>3}  points found")
    agree = True
    for name, f, g in EXAMPLES:
        first, second = (intersection_pattern(f, g, c) for c in CHANGES)
        agree = agree and first == second
        de = degree(f) * degree(g)
        print(f"{name:<38} {de:>3}  {describe(first)} = {total(first)}")
    print(f"Both coordinate changes give the same pattern: {agree}")
    print("Points at infinity, complex points and tangency (multiplicity > 1)")
    print("are exactly what is needed for the count to be d*e every time.")
    print()
    print("Epistemic status: exact symbolic computation (resultants and")
    print("factorisation over Q in SymPy) for ten examples; the multiplicities")
    print("are meaningful because the coordinate change is generic, which we")
    print("check only by agreement of two changes. Evidence, not a proof of")
    print("Bezout's theorem.")


if __name__ == "__main__":
    main()
