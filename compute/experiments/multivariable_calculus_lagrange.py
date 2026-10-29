"""Lagrange multipliers, solved exactly with SymPy.

To find the extreme values of f on the constraint set g = c, solve the
system grad f = lambda grad g, g = c. SymPy solves it exactly for three
problems: xy on the circle x^2 + y^2 = 2, the volume xyz of a box with surface
area 6, and the point of the plane x + 2y + 2z = 9 closest to the origin.
Each candidate is evaluated; the extreme values exist because the constraint
set is compact (first problem) or for a separate reason explained in the
lesson.

Runs in the browser (Pyodide) with the sympy package loaded.
"""

import sympy

EXPERIMENT = {
    "id": "multivariable_calculus_lagrange",
    "title": "Lagrange multipliers solved exactly",
    "evidence": ["symbolic", "exact"],
    "lessons": ["multivariable-calculus"],
    "summary": (
        "Uses SymPy to solve the Lagrange system grad f = lambda grad g, g = c "
        "exactly for three constrained problems (xy on a circle, the largest "
        "box of given surface area, the nearest point of a plane), lists every "
        "critical point with its value, and checks the multiplier equations. "
        "Exact, but only as reliable as SymPy's solver, which finds candidates; "
        "existence of an extremum needs the separate arguments in the lesson."
    ),
    "packages": ["sympy"],
}

x, y, z, lam = sympy.symbols("x y z lambda", real=True)


def lagrange_points(f, g, c, variables):
    """Solve grad f = lambda grad g, g = c; return sorted (point, value) pairs."""
    eqs = [sympy.diff(f, v) - lam * sympy.diff(g, v) for v in variables]
    eqs.append(g - c)
    sols = sympy.solve(eqs, list(variables) + [lam], dict=True)
    out = []
    for s in sols:
        point = tuple(sympy.nsimplify(s[v]) for v in variables)
        out.append((point, sympy.simplify(f.subs(s))))
    return sorted(out, key=lambda pv: (float(pv[1]), [float(p) for p in pv[0]]))


def satisfies_multiplier_rule(f, g, point, variables):
    """True if grad f is a multiple of grad g at the point (2- or 3-vectors)."""
    sub = dict(zip(variables, point))
    gf = sympy.Matrix([sympy.diff(f, v).subs(sub) for v in variables])
    gg = sympy.Matrix([sympy.diff(g, v).subs(sub) for v in variables])
    return sympy.Matrix.hstack(gf, gg).rank() <= 1


PROBLEMS = [
    ("max/min of xy on x^2 + y^2 = 2", x * y, x**2 + y**2, 2, (x, y)),
    ("max of xyz on 2(xy + yz + zx) = 6, x, y, z > 0",
     x * y * z, 2 * (x * y + y * z + z * x), 6, (x, y, z)),
    ("min of x^2 + y^2 + z^2 on x + 2y + 2z = 9",
     x**2 + y**2 + z**2, x + 2 * y + 2 * z, 9, (x, y, z)),
]


def main():
    print(f"Lagrange multipliers with SymPy {sympy.__version__}")
    for title, f, g, c, variables in PROBLEMS:
        print(title)
        points = lagrange_points(f, g, c, variables)
        if len(variables) == 3 and "xyz" in title:
            points = [(p, v) for p, v in points if all(t > 0 for t in p)]
        for point, value in points:
            ok = satisfies_multiplier_rule(f, g, point, variables)
            print(f"   point {str(point):<16} value {str(value):<4} rule holds: {ok}")
    print("Readings: xy ranges over [-1, 1] on the circle; the best box is the")
    print("unit cube (volume 1); the nearest point is (1, 2, 2), at distance 3,")
    print("which is |9| / |(1, 2, 2)|, the point-to-plane distance formula.")
    print()
    print("Epistemic status: exact symbolic solutions of the multiplier")
    print("equations, as reliable as SymPy's solver. The method only lists")
    print("candidates: that a maximum or minimum exists at all is a separate")
    print("argument (compactness of the circle; for the box and the plane, the")
    print("reasoning given in the lesson).")


if __name__ == "__main__":
    main()
