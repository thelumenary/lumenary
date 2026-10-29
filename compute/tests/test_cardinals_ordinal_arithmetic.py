import random

import pytest

import cardinals_ordinal_arithmetic as oa

W, ONE, ZERO = oa.OMEGA, oa.ONE, oa.ZERO


def test_finite_ordinals_behave_like_natural_numbers():
    for m in range(6):
        for n in range(6):
            assert oa.add(oa.nat(m), oa.nat(n)) == oa.nat(m + n)
            assert oa.mul(oa.nat(m), oa.nat(n)) == oa.nat(m * n)
            assert oa.cmp(oa.nat(m), oa.nat(n)) == (m > n) - (m < n)
    with pytest.raises(ValueError):
        oa.nat(-1)


def test_non_commutativity_examples():
    two = oa.nat(2)
    assert oa.add(ONE, W) == W
    assert oa.cmp(oa.add(W, ONE), W) == 1
    assert oa.mul(two, W) == W
    assert oa.mul(W, two) == oa.add(W, W) == ((ONE, 2),)
    assert oa.fmt(oa.mul(two, oa.add(W, ONE))) == "w + 2"
    assert oa.fmt(oa.mul(oa.add(W, ONE), two)) == "w*2 + 1"


def test_comparison_is_a_strict_total_order_on_samples():
    rng = random.Random(7)
    sample = [oa.random_ordinal(rng) for _ in range(60)]
    for a in sample:
        assert oa.cmp(a, a) == 0
        for b in sample:
            assert oa.cmp(a, b) == -oa.cmp(b, a)
    # w^2 is larger than every w*k + n
    w2 = ((oa.nat(2), 1),)
    assert oa.cmp(w2, ((ONE, 10**6), (ZERO, 10**6))) == 1


def test_laws_on_random_triples():
    rng = random.Random(11)
    assoc = lambda a, b, c: oa.mul(oa.mul(a, b), c) == oa.mul(a, oa.mul(b, c))
    left = lambda a, b, c: oa.mul(a, oa.add(b, c)) == oa.add(oa.mul(a, b), oa.mul(a, c))
    right = lambda a, b, c: oa.mul(oa.add(a, b), c) == oa.add(oa.mul(a, c), oa.mul(b, c))
    assert oa.law_failures(rng, 400, assoc) == []
    assert oa.law_failures(rng, 400, left) == []
    assert oa.law_failures(rng, 400, right)


def test_hereditary_base_and_bump():
    assert oa.hereditary(4, 2) == ((W, 1),)  # 4 = 2^(2^1) -> w^w
    assert oa.fmt(oa.hereditary(26, 3)) == "w^2*2 + w*2 + 2"
    assert oa.bump(4, 2) == 27  # 2^(2^1) -> 3^(3^1)
    assert oa.bump(26, 3) == 42


def test_goodstein_sequences():
    assert [v for _, v in oa.goodstein(3, 10)] == [3, 3, 3, 2, 1, 0]
    seq = oa.goodstein(4, 8)
    assert [v for _, v in seq] == [4, 26, 41, 60, 83, 109, 139, 173]
    ords = [oa.hereditary(v, b) for b, v in seq]
    assert all(oa.cmp(x, y) == 1 for x, y in zip(ords, ords[1:]))
