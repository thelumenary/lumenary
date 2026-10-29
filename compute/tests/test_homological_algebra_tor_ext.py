from math import gcd

import homological_algebra_tor_ext as te


def test_kernel_and_cokernel_sizes():
    assert te.kernel_size(4, 6) == 2
    assert te.cokernel_size(4, 6) == 2
    assert te.kernel_size(3, 5) == 1
    assert te.kernel_size(6, 6) == 6           # multiplication by 0
    assert te.cokernel_size(1, 7) == 1


def test_gcd_formula_exhaustive():
    for m in range(1, 16):
        for n in range(1, 16):
            assert te.kernel_size(m, n) == gcd(m, n)
            assert te.cokernel_size(m, n) == gcd(m, n)


def test_second_resolution_presents_z_mod_m():
    for m in range(1, 12):
        a = te.second_resolution(m)
        det = a[0][0] * a[1][1] - a[0][1] * a[1][0]
        assert abs(det) == m                   # cokernel has order m
        assert gcd(gcd(a[0][0], a[0][1]), gcd(a[1][0], a[1][1])) == 1   # cyclic


def test_tor_independent_of_resolution():
    for m in range(1, 10):
        for n in range(1, 10):
            assert te.tor1_from_matrix(te.second_resolution(m), n) == te.kernel_size(m, n)


def test_identity_matrix_has_trivial_kernel():
    assert te.tor1_from_matrix([[1, 0], [0, 1]], 5) == 1
    assert te.tor1_from_matrix([[0, 0], [0, 0]], 3) == 9
