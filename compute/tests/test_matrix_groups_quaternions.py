from fractions import Fraction

import matrix_groups_quaternions as mgq

ONE = (1, 0, 0, 0)
I, J, K = (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)


def neg(q):
    return tuple(-x for x in q)


def test_hamilton_relations():
    assert mgq.qmul(I, I) == neg(ONE)
    assert mgq.qmul(J, J) == neg(ONE) and mgq.qmul(K, K) == neg(ONE)
    assert mgq.qmul(I, J) == K and mgq.qmul(J, I) == neg(K)
    assert mgq.qmul(mgq.qmul(I, J), K) == neg(ONE)  # ijk = -1


def test_norm_is_multiplicative_and_conjugate_inverts():
    p = (1, 2, -3, 4)
    q = (2, 0, 5, -1)
    assert mgq.norm_sq(mgq.qmul(p, q)) == mgq.norm_sq(p) * mgq.norm_sq(q)
    n = mgq.norm_sq(p)
    assert mgq.qmul(p, mgq.conj(p)) == (n, 0, 0, 0)


def test_rho_is_a_rotation_and_two_to_one():
    q = mgq.frac_q(1, 2, 2, 4, den=5)
    r = mgq.rho(q)
    assert mgq.matmul(mgq.transpose(r), r) == mgq.IDENTITY
    assert mgq.det3(r) == 1
    assert mgq.rho(neg(q)) == r
    assert mgq.rho(ONE) == mgq.IDENTITY


def test_rho_of_i_is_half_turn_about_x_axis():
    assert mgq.rho(I) == ((1, 0, 0), (0, -1, 0), (0, 0, -1))


def test_homomorphism_and_non_commutativity():
    p = mgq.frac_q(3, 4, 0, 0, den=5)
    q = mgq.frac_q(2, 1, 4, 2, den=5)
    assert mgq.rho(mgq.qmul(p, q)) == mgq.matmul(mgq.rho(p), mgq.rho(q))
    assert mgq.matmul(mgq.rho(p), mgq.rho(q)) != mgq.matmul(mgq.rho(q),
                                                            mgq.rho(p))


def test_hurwitz_units_form_binary_tetrahedral_group():
    units = mgq.hurwitz_units()
    assert len(units) == 24 and len(set(units)) == 24
    assert all(mgq.norm_sq(u) == 1 for u in units)
    assert all(mgq.qmul(a, b) in units for a in units for b in units)
    images = {mgq.rho(u) for u in units}
    assert len(images) == 12


def test_show():
    assert mgq.show(mgq.frac_q(1, 2, 2, 4, den=5)) == "(1, 2, 2, 4)/5"
    assert mgq.show((Fraction(1), Fraction(0), Fraction(0), Fraction(0))) == \
        "(1, 0, 0, 0)"
