"""The Nullstellensatz with Groebner bases: tangency, nilpotents and radicals.

For an ideal I = (g1, ..., gr) of Q[x, y], membership f in I is decided by a
Groebner basis. The Nullstellensatz says f vanishes on the complex zero set
V(I) exactly when f^k lies in I for some k, and Rabinowitsch's trick turns
this into one membership test: f is in the radical of I iff 1 lies in the
ideal (g1, ..., gr, 1 - t f) of Q[x, y, t]. We test both on examples where a
line is tangent to a curve (the intersection is a double point, and the
coordinate ring has a nilpotent), and on an ideal with no real zeros.
Exact symbolic computation with sympy.
"""

import sympy as sp

EXPERIMENT = {
    "id": "commutative_algebra_nullstellensatz",
    "title": "Radicals and the Nullstellensatz by Groebner bases",
    "evidence": ["symbolic", "exact"],
    "lessons": ["commutative-algebra"],
    "summary": (
        "Uses Groebner bases over Q to decide ideal membership, finds the "
        "least k with f^k in I for tangent intersections (parabola and line, "
        "circle and tangent line, a cusp), and checks that this agrees with "
        "Rabinowitsch's single test 1 in (I, 1 - t f). It also shows an ideal "
        "with no real zeros that is proper because it has complex zeros. "
        "Exact checks of examples; the Nullstellensatz is proved in the lesson."
    ),
    "packages": ["sympy"],
}

x, y, t = sp.symbols("x y t")


def in_ideal(f, gens, variables=(x, y)):
    """Decide f in (gens) with a Groebner basis (lex order)."""
    basis = sp.groebner(list(gens), *variables, order="lex")
    return basis.contains(sp.sympify(f))


def radical_exponent(f, gens, max_k=6):
    """Least k <= max_k with f^k in (gens), or None."""
    for k in range(1, max_k + 1):
        if in_ideal(sp.expand(f ** k), gens):
            return k
    return None


def in_radical(f, gens):
    """Rabinowitsch: f is in rad(gens) iff 1 is in (gens, 1 - t f)."""
    g = sp.groebner(list(gens) + [1 - t * f], x, y, t, order="lex")
    return list(g.exprs) == [1]


def is_proper(gens):
    """(gens) is a proper ideal iff its reduced Groebner basis is not [1]."""
    return list(sp.groebner(list(gens), x, y, order="lex").exprs) != [1]


EXAMPLES = [
    ("parabola y = x^2, tangent y = 0", [y - x**2, y], x),
    ("parabola y = x^2, secant y = 1", [y - x**2, y - 1], x**2 - 1),
    ("circle, tangent line x = 1", [x**2 + y**2 - 1, x - 1], y),
    ("cusp y^2 = x^3, line y = 0", [y**2 - x**3, y], x),
    ("double line x^2 = 0, xy = 0", [x**2, x * y], x),
    ("double line x^2 = 0, xy = 0", [x**2, x * y], y),
]


def main():
    print("f vanishes on V(I) iff f^k in I for some k (k = None: never).")
    for name, gens, f in EXAMPLES:
        k = radical_exponent(f, gens)
        rab = in_radical(f, gens)
        agree = (k is not None) == rab
        print(f"  {name}:")
        print(f"    f = {f}: least k = {k}; Rabinowitsch says {rab}; "
              f"agree: {agree}")
    print("No real zeros, but proper (complex zeros +-i):",
          is_proper([x**2 + 1, y]))
    print("Empty complex zero set, so 1 lies in I = (xy - 1, x):",
          not is_proper([x * y - 1, x]))
    print()
    print("Epistemic status: exact Groebner basis computations over Q for "
          "the listed\nideals; they illustrate the Nullstellensatz but cannot "
          "prove it, and they say\nnothing about ideals not tested. The "
          "theorem needs an algebraically closed\nfield, as the ideal "
          "(x^2 + 1, y) shows over the reals.")


if __name__ == "__main__":
    main()
