import pytest

import quotients_polynomial_fields as qp


def test_mulmod_in_f4():
    f = [1, 1, 1]          # x^2 + x + 1 over F_2
    x = (0, 1)
    assert qp.poly_mulmod(x, x, f, 2) == (1, 1)          # x^2 = x + 1
    assert qp.poly_mulmod((1, 1), x, f, 2) == (1, 0)     # (x+1) x = x^2 + x = 1


def test_i_squared_in_f9():
    f = [1, 0, 1]          # x^2 + 1 over F_3: x plays the role of i
    assert qp.poly_mulmod((0, 1), (0, 1), f, 3) == (2, 0)  # x^2 = -1


@pytest.mark.parametrize("p, f", qp.CASES)
def test_field_iff_irreducible(p, f):
    n = len(f) - 1
    assert (len(qp.units(f, p)) == p ** n - 1) == qp.is_irreducible(f, p)


def test_irreducibility_examples():
    assert qp.is_irreducible([1, 1, 1], 2)
    assert not qp.is_irreducible([1, 0, 1], 2)            # (x + 1)^2
    assert not qp.is_irreducible([1, 0, 1, 0, 1], 2)      # (x^2 + x + 1)^2, no root
    assert not qp.has_root([1, 0, 1, 0, 1], 2)


def test_generators_have_full_order():
    for p, f in [(2, [1, 1, 1]), (3, [1, 0, 1]), (2, [1, 1, 0, 0, 1])]:
        g = qp.generator(f, p)
        n = len(f) - 1
        seen, power = set(), g
        for _ in range(p ** n - 1):
            seen.add(power)
            power = qp.poly_mulmod(power, g, f, p)
        assert len(seen) == p ** n - 1


def test_crt():
    assert qp.crt_is_isomorphism(3, 4)
    assert qp.crt_is_isomorphism(5, 7)
    assert not qp.crt_is_isomorphism(2, 2)
    assert not qp.crt_is_isomorphism(4, 6)


def test_show_poly():
    assert qp.show_poly([1, 1, 0, 1]) == "x^3+x+1"
    assert qp.show_poly([2, 0, 1]) == "x^2+2"
    assert qp.show_poly((0, 1)) == "x"
