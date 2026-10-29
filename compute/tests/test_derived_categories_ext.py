from math import gcd

import pytest

import derived_categories_ext as de


def test_mult_kernel_image():
    assert de.mult_kernel_image(6, 2) == (2, 3)
    assert de.mult_kernel_image(5, 0) == (5, 1)
    assert de.mult_kernel_image(7, 3) == (1, 7)


def test_cohomology_orders_simple_complexes():
    # Z/4 --2--> Z/4: H^0 = ker 2 = {0, 2}, H^1 = Z/4 / {0, 2}.
    assert de.cohomology_orders(4, [2]) == [2, 2]
    # A single term has H^0 equal to the whole group.
    assert de.cohomology_orders(5, []) == [5]
    # Exact sequence Z/4 --2--> Z/4 --2--> Z/4 in the middle.
    assert de.cohomology_orders(4, [2, 2])[1] == 1


@pytest.mark.parametrize("a,b", [(2, 2), (4, 6), (3, 5), (12, 18), (1, 7)])
def test_ext_over_z_is_gcd_then_zero(a, b):
    ext = de.ext_over_z(a, b, top=4)
    assert ext[0] == ext[1] == gcd(a, b) == de.homs(a, b)
    assert ext[2:] == [1, 1, 1]


def test_ext_over_z4_and_z9():
    assert de.ext_over_zn(4, 2, 2) == [2] * 6
    assert de.ext_over_zn(4, 2, 4) == [2, 1, 1, 1, 1, 1]  # Z/4 self-injective
    assert de.ext_over_zn(9, 3, 3) == [3] * 6
    assert de.ext_over_zn(4, 4, 2)[0] == 2  # Hom(Z/4, Z/2) = Z/2, free module
    assert de.ext_over_zn(4, 4, 2)[1:] == [1] * 5  # Z/4 is projective
    with pytest.raises(ValueError):
        de.ext_over_zn(4, 3, 2)


def test_extension_counts():
    assert de.extension_classes(2) == (2, 1)
    assert de.extension_classes(3) == (3, 2)


def test_cyclicity_detector():
    zero = {(a, b): 0 for a in range(3) for b in range(3)}
    assert not de.extension_is_cyclic(zero, 3)  # split: Z/3 x Z/3
    carry = {(a, b): (a + b) // 3 for a in range(3) for b in range(3)}
    assert de.extension_is_cyclic(carry, 3)  # the "carry" cocycle gives Z/9
