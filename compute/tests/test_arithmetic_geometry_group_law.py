from fractions import Fraction as F

import arithmetic_geometry_group_law as gl


def test_identity_and_inverse():
    P = (F(3), F(5))
    assert gl.add(None, P, 0) == P
    assert gl.add(P, None, 0) == P
    assert gl.add(P, gl.neg(P), 0) is None
    assert gl.neg(None) is None


def test_bachet_duplication():
    P = (F(3), F(5))
    assert gl.add(P, P, 0) == (F(129, 100), F(-383, 1000))
    assert gl.on_curve(gl.add(P, P, 0), 0, -2)
    assert not gl.is_integral(gl.add(P, P, 0))


def test_torsion_point_of_order_six():
    P = (F(2), F(3))
    assert gl.order(P, 0) == 6
    assert gl.multiple(2, P, 0) == (F(0), F(1))
    assert gl.multiple(3, P, 0) == (F(-1), F(0))
    assert gl.multiple(6, P, 0) is None
    assert all(gl.is_integral(gl.multiple(n, P, 0)) for n in range(7))


def test_infinite_order_point_has_no_small_order():
    assert gl.order((F(3), F(5)), 0, limit=20) is None


def test_sums_stay_on_curve():
    a, b = F(0), F(-2)
    P = (F(3), F(5))
    R = None
    for _ in range(8):
        R = gl.add(R, P, a)
        assert gl.on_curve(R, a, b)


def test_points_mod_and_hasse():
    pts = gl.points_mod(2, 3, 13)
    assert pts[0] is None
    assert len(pts) == 18
    assert abs(len(pts) - 14) <= 2 * 13 ** 0.5
    for P in pts[1:]:
        x, y = P
        assert (y * y - x ** 3 - 2 * x - 3) % 13 == 0


def test_group_law_mod_p_closed_and_associative():
    pts = gl.points_mod(2, 3, 13)
    s = set(pts)
    for P in pts:
        for Q in pts:
            assert gl.add_mod(P, Q, 2, 13) in s
            assert gl.add_mod(P, Q, 2, 13) == gl.add_mod(Q, P, 2, 13)
    assert gl.associativity_failures(pts[:6], 2, 13) == []


def test_associativity_detects_a_broken_law(monkeypatch):
    # Forgetting to reflect the third point breaks the group law.
    good_add = gl.add_mod

    def bad_add(P, Q, a, p):
        if P is None:
            return Q
        if Q is None:
            return P
        R = good_add(P, Q, a, p)
        return None if R is None else (R[0], (-R[1]) % p)
    monkeypatch.setattr(gl, "add_mod", bad_add)
    pts = gl.points_mod(2, 3, 13)
    assert gl.associativity_failures(pts, 2, 13) != []
