import math

import numpy as np

import homotopy_theory_hopf_linking as hl


def test_hopf_maps_s3_to_s2():
    rng = np.random.default_rng(7)
    v = rng.normal(size=(200, 4))
    v /= np.linalg.norm(v, axis=1)[:, None]
    z, w = v[:, 0] + 1j * v[:, 1], v[:, 2] + 1j * v[:, 3]
    assert np.allclose(np.linalg.norm(hl.hopf(z, w), axis=1), 1.0)


def test_fibres_lie_on_s3_and_map_to_p():
    for p in hl.POINTS.values():
        z, w = hl.fibre(p, n=64)
        assert np.allclose(abs(z) ** 2 + abs(w) ** 2, 1.0)
        assert np.allclose(hl.hopf(z, w), p)


def test_fibre_handles_both_hemispheres():
    for p in (hl.unit([0, 0, 1]), hl.unit([0, 0.3, -1]), hl.unit([1, 0, 0])):
        z, w = hl.fibre(p, n=16)
        assert np.allclose(hl.hopf(z, w), p)


def test_linking_number_of_hopf_fibres_is_one():
    names = list(hl.POINTS)
    for a, b in [(names[0], names[1]), (names[2], names[4])]:
        c1 = hl.stereographic(*hl.fibre(hl.POINTS[a]))
        c2 = hl.stereographic(*hl.fibre(hl.POINTS[b]))
        assert abs(hl.linking_number(c1, c2) - 1) < 1e-8


def test_linking_number_controls():
    flat = hl.round_circle([0, 0, 0])
    assert abs(hl.linking_number(flat, hl.round_circle([3, 0, 0], vertical=True))) < 1e-8
    # the standard Hopf link of two round circles links once (up to sign)
    linked = hl.linking_number(flat, hl.round_circle([1, 0, 0], vertical=True))
    assert abs(abs(linked) - 1) < 1e-8
    # reversing the orientation of one curve flips the sign
    c2 = hl.round_circle([1, 0, 0], vertical=True)[::-1]
    assert math.isclose(hl.linking_number(flat, c2), -linked, abs_tol=1e-6)


def test_spectral_derivative_of_circle():
    c = hl.round_circle([0, 0, 0], n=32)
    d = hl.spectral_derivative(c)
    t = 2 * np.pi * np.arange(32) / 32
    assert np.allclose(d[:, 0], -np.sin(t)) and np.allclose(d[:, 1], np.cos(t))
