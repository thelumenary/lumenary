"""A braiding that is not symmetric: the R-matrix of the quantum group.

On V = C^2 (basis e1, e2) take the 4 x 4 matrix acting on V (x) V
    R(q) = [[q, 0, 0, 0], [0, 0, 1, 0], [0, 1, q - 1/q, 0], [0, 0, 0, q]].
Up to a scalar it is the braiding c_{V,V} of the category of representations
of the quantum group U_q(sl_2). At q = 1 it is the swap of tensor factors,
the symmetric braiding of vector spaces. SymPy checks, with q a symbol:
* the braid (Yang-Baxter) relation on V (x) V (x) V, which every braiding in a
  braided monoidal category satisfies;
* the Hecke relation (R - q)(R + 1/q) = 0;
* that R^2 = 1 exactly when q^2 = 1, so for other q braiding twice is not the
  identity: the category is braided but not symmetric.
"""

import sympy

EXPERIMENT = {
    "id": "monoidal_categories_braiding",
    "title": "A braided but not symmetric R-matrix",
    "evidence": ["symbolic"],
    "lessons": ["monoidal-categories"],
    "summary": (
        "With SymPy and a symbolic parameter q, verifies that the U_q(sl_2) "
        "R-matrix on C^2 (x) C^2 satisfies the braid (Yang-Baxter) relation "
        "and the Hecke relation, reduces to the swap at q = 1, and squares to "
        "the identity only when q^2 = 1 - a braiding that is not symmetric."
    ),
    "packages": ["sympy"],
}

Q = sympy.symbols("q", nonzero=True)


def r_matrix(q):
    """The braiding matrix R(q) on V (x) V, basis e11, e12, e21, e22."""
    return sympy.Matrix([[q, 0, 0, 0],
                         [0, 0, 1, 0],
                         [0, 1, q - sympy.Integer(1) / q, 0],
                         [0, 0, 0, q]])


def swap():
    """The symmetric braiding of vector spaces: v (x) w -> w (x) v."""
    return sympy.Matrix([[1, 0, 0, 0],
                         [0, 0, 1, 0],
                         [0, 1, 0, 0],
                         [0, 0, 0, 1]])


def on_first_two(m):
    """m (x) id_V acting on V (x) V (x) V."""
    return sympy.kronecker_product(m, sympy.eye(2))


def on_last_two(m):
    """id_V (x) m acting on V (x) V (x) V."""
    return sympy.kronecker_product(sympy.eye(2), m)


def braid_defect(m):
    """(m1 m2 m1 - m2 m1 m2), simplified, for m1 = m (x) 1, m2 = 1 (x) m."""
    a, b = on_first_two(m), on_last_two(m)
    return sympy.simplify(a * b * a - b * a * b)


def hecke_defect(m, q):
    """(m - q)(m + 1/q), simplified."""
    eye = sympy.eye(m.shape[0])
    return sympy.simplify((m - q * eye) * (m + eye / q))


def square_minus_identity(m):
    """m^2 - 1, simplified."""
    return sympy.simplify(m * m - sympy.eye(m.shape[0]))


def main():
    r = r_matrix(Q)
    print("R(q) on V (x) V, basis e1e1, e1e2, e2e1, e2e2:")
    for row in r.tolist():
        print("   " + "  ".join(f"{str(x):>7}" for x in row))
    print(f"R(1) is the swap of tensor factors:          "
          f"{r_matrix(1) == swap()}")
    zero8 = sympy.zeros(8, 8)
    print(f"braid relation R1 R2 R1 = R2 R1 R2 (8 x 8):  "
          f"{braid_defect(r) == zero8}")
    print(f"Hecke relation (R - q)(R + 1/q) = 0:         "
          f"{hecke_defect(r, Q) == sympy.zeros(4, 4)}")
    diff = square_minus_identity(r)
    print(f"R^2 - 1 = (q - 1/q) R:                       "
          f"{sympy.simplify(diff - (Q - 1 / Q) * r) == sympy.zeros(4, 4)}")
    roots = sympy.solve([x for x in diff if x != 0], Q, dict=True)
    print(f"values of q with R^2 = 1:                    "
          f"{sorted(s[Q] for s in roots)}")
    r2 = r_matrix(sympy.Integer(2))
    print(f"q = 2: R^2 = 1? {square_minus_identity(r2) == sympy.zeros(4, 4)}"
          f";  braid relation? {braid_defect(r2) == zero8}")
    print()
    print("Epistemic status: exact symbolic verification of matrix "
          "identities, as\nreliable as SymPy's simplification of rational "
          "functions of q. It checks\nconsequences of the braiding axioms on "
          "one representation; that these\nmatrices come from a braided "
          "monoidal category (Drinfeld, Jimbo) is a\ntheorem cited in the "
          "lesson, not proved here.")


if __name__ == "__main__":
    main()
