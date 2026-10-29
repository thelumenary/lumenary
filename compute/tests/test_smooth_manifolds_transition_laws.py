import sympy

import smooth_manifolds_transition_laws as st

U, V = st.U, st.V


def test_north_inverse_lands_on_sphere():
    assert st.on_sphere(U, V) == 0
    assert st.north_inverse(0, 0) == (0, 0, -1)
    x, y, z = st.north_inverse(sympy.Integer(1), sympy.Integer(0))
    assert (x, y, z) == (1, 0, 0)


def test_transition_is_inversion():
    t = st.transition()
    r = U**2 + V**2
    assert sympy.simplify(t[0] - U / r) == 0
    assert sympy.simplify(t[1] - V / r) == 0


def test_jacobian_determinant_negative():
    J = st.jacobian(st.transition())
    det = sympy.simplify(J.det())
    assert sympy.simplify(det + 1 / (U**2 + V**2) ** 2) == 0
    assert det.subs({U: 1, V: 2}) < 0


def test_pairing_is_invariant_and_wrong_rule_is_not():
    Jp = st.jacobian(st.transition()).subs({U: 1, V: 2})
    vec = sympy.Matrix([3, -1])
    cov = sympy.Matrix([2, 5])
    new_v, new_w, wrong_w = st.transform(Jp, vec, cov)
    assert st.pairing(cov, vec) == 1
    assert st.pairing(new_w, new_v) == 1
    assert st.pairing(wrong_w, new_v) == sympy.Rational(1, 25)
    assert new_w.T.tolist()[0] == [-14, -23]


def test_pairing_invariant_for_generic_jacobian():
    a, b, c, d = sympy.symbols("a b c d")
    J = sympy.Matrix([[a, b], [c, d]])
    v = sympy.Matrix(sympy.symbols("v1 v2"))
    w = sympy.Matrix(sympy.symbols("w1 w2"))
    new_v, new_w, _ = st.transform(J, v, w)
    diff = (new_w.T * new_v)[0, 0] - (w.T * v)[0, 0]
    assert sympy.simplify(diff) == 0
