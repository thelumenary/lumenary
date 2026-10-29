"""Exterior calculus on R^3, symbolically.

A differential form on R^3 is stored as a dictionary from increasing index
tuples to SymPy expressions: {(0,): P, (1,): Q, (2,): R} is P dx + Q dy + R dz.
We implement the wedge product (with the sign of the sorting permutation) and
the exterior derivative d, and let SymPy check, for forms with arbitrary
smooth coefficient functions: d(d w) = 0 in every degree, the graded rule
a ^ b = (-1)^(kl) b ^ a, the Leibniz rule for d, and the dictionary between
d and grad, curl, div (so curl grad = 0 and div curl = 0 are d d = 0). Finally
we check Stokes' theorem (the divergence theorem) exactly on the unit cube for
one vector field. Evidence: symbolic verification, relying on SymPy's
equality of mixed partial derivatives.
"""

import re
from itertools import product

import sympy

EXPERIMENT = {
    "id": "differential_forms_exterior_calculus",
    "title": "Exterior calculus on R^3: wedge, d, and d d = 0",
    "evidence": ["symbolic"],
    "lessons": ["differential-forms"],
    "summary": (
        "Implements differential forms on R^3 as dictionaries of SymPy "
        "coefficients, with the wedge product and the exterior derivative. With "
        "arbitrary coefficient functions it verifies d(dw) = 0 in degrees 0 to "
        "2, graded anticommutativity, the Leibniz rule, and that d is grad, curl "
        "and div; it then checks the divergence theorem exactly on the unit cube "
        "for one field. Symbolic verification on examples."
    ),
    "packages": ["sympy"],
}

X = sympy.symbols("x y z")
NAMES = ("dx", "dy", "dz")


def sort_sign(indices):
    """(sign, sorted tuple) of a tuple of indices; sign 0 if one repeats."""
    if len(set(indices)) < len(indices):
        return 0, ()
    sign, idx = 1, list(indices)
    for i in range(len(idx)):
        for j in range(len(idx) - 1 - i):
            if idx[j] > idx[j + 1]:
                idx[j], idx[j + 1] = idx[j + 1], idx[j]
                sign = -sign
    return sign, tuple(idx)


def clean(form):
    """Drop zero coefficients after expanding."""
    out = {}
    for key, c in form.items():
        c = sympy.expand(c)
        if c != 0:
            out[key] = c
    return out


def add(*forms):
    """Sum of forms."""
    out = {}
    for f in forms:
        for key, c in f.items():
            out[key] = out.get(key, 0) + c
    return clean(out)


def scale(c, form):
    """Multiply a form by a function or number."""
    return clean({key: c * v for key, v in form.items()})


def wedge(a, b):
    """The wedge product of two forms."""
    out = {}
    for (ka, ca), (kb, cb) in product(a.items(), b.items()):
        sign, key = sort_sign(ka + kb)
        if sign:
            out[key] = out.get(key, 0) + sign * ca * cb
    return clean(out)


def d(form):
    """The exterior derivative: d(c dx_I) = sum_i (dc/dx_i) dx_i ^ dx_I."""
    out = {}
    for key, c in form.items():
        for i, xi in enumerate(X):
            sign, new = sort_sign((i,) + key)
            if sign:
                out[new] = out.get(new, 0) + sign * sympy.diff(c, xi)
    return clean(out)


def generic(degree, name):
    """A k-form whose coefficients are arbitrary functions of x, y, z."""
    keys = [k for k in product(range(3), repeat=degree) if list(k) == sorted(set(k))]
    return {k: sympy.Function(f"{name}{''.join(map(str, k))}")(*X) for k in keys}


def short(expr):
    """Write Derivative(f(x, y, z), x) as f_x and f(x, y, z) as f."""
    text = str(expr)
    text = re.sub(r"Derivative\((\w+)\(x, y, z\), (\w)\)", r"\1_\2", text)
    return re.sub(r"(\w+)\(x, y, z\)", r"\1", text)


def show(form):
    """Readable text for a form."""
    if not form:
        return "0"
    parts = []
    for key in sorted(form, key=lambda k: (len(k), k)):
        basis = "^".join(NAMES[i] for i in key)
        parts.append(f"({short(form[key])}){' ' + basis if basis else ''}")
    return " + ".join(parts)


def main():
    print(f"Exterior calculus on R^3 (SymPy {sympy.__version__})")
    for k in range(3):
        w = generic(k, "w")
        print(f"  d(d w) = {show(d(d(w)))} for a general {k}-form w")
    a, b, c = generic(1, "a"), generic(1, "b"), generic(2, "c")
    print("  a^b + b^a = 0 for 1-forms:", add(wedge(a, b), wedge(b, a)) == {})
    print("  a^c - c^a = 0 for a 1-form a and a 2-form c:",
          add(wedge(a, c), scale(-1, wedge(c, a))) == {})
    leibniz = add(d(wedge(a, b)), scale(-1, wedge(d(a), b)), wedge(a, d(b)))
    print("  d(a^b) = da^b - a^db for 1-forms:", leibniz == {})
    print()
    f = sympy.Function("f")(*X)
    P, Q, R = (sympy.Function(n)(*X) for n in "PQR")
    A, B, C = (sympy.Function(n)(*X) for n in "ABC")
    print("Vector calculus inside d:")
    print("  d f =", show(d({(): f})), " (grad)")
    curl = d({(0,): P, (1,): Q, (2,): R})
    print("  d(P dx + Q dy + R dz): dy^dz:", short(curl[(1, 2)]),
          " dz^dx:", short(-curl[(0, 2)]))
    print("                         dx^dy:", short(curl[(0, 1)]), " (curl)")
    div = d({(1, 2): A, (0, 2): -B, (0, 1): C})
    print("  d(A dy^dz + B dz^dx + C dx^dy) =", show(div), " (div)")
    print("  so curl(grad f) = 0 and div(curl F) = 0 are both d(d w) = 0")
    print()
    x, y, z = X
    field = {(1, 2): x * y ** 2, (0, 2): -(y * z), (0, 1): x * z ** 2}
    volume = sympy.integrate(d(field)[(0, 1, 2)], (x, 0, 1), (y, 0, 1),
                             (z, 0, 1))
    P, Q, R = field[(1, 2)], -field[(0, 2)], field[(0, 1)]
    flux = sum(
        sympy.integrate(F_comp.subs(v, 1) - F_comp.subs(v, 0), *lim)
        for F_comp, v, lim in [(P, x, [(y, 0, 1), (z, 0, 1)]),
                               (Q, y, [(x, 0, 1), (z, 0, 1)]),
                               (R, z, [(x, 0, 1), (y, 0, 1)])])
    print("Stokes on the unit cube for F = (x y^2, y z, x z^2):")
    print(f"  integral of d(omega) = {volume}, flux through boundary = {flux}")
    print()
    print("Epistemic status: symbolic verification. The identities hold for")
    print("arbitrary coefficient functions because SymPy treats mixed partials")
    print("as equal (true for C^2 functions); the cube check is one example of")
    print("Stokes' theorem, which is proved in the lesson, not here.")


if __name__ == "__main__":
    main()
