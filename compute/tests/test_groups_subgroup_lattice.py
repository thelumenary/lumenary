import pytest

import groups_subgroup_lattice as gl


def test_compose_and_inverse():
    r = (1, 2, 0)
    s = (1, 0, 2)
    assert gl.compose(r, gl.inverse(r)) == (0, 1, 2)
    # first s, then r differs from first r, then s: S3 is not abelian
    assert gl.compose(r, s) != gl.compose(s, r)


@pytest.mark.parametrize(
    "perm, expected",
    [((0, 1, 2, 3), 1), ((1, 0, 2, 3), 2), ((1, 2, 0, 3), 3),
     ((1, 2, 3, 0), 4), ((1, 0, 3, 2), 2), ((1, 2, 0, 4, 3), 6)],
)
def test_order_is_lcm_of_cycle_lengths(perm, expected):
    assert gl.order(perm) == expected


def test_group_orders():
    sizes = {name: len(gl.closure(gens, n)) for name, n, gens in gl.examples()}
    assert sizes == {"S3": 6, "D4": 8, "A4": 12, "S4": 24, "C12": 12}


def test_known_subgroup_counts():
    expected = {"S3": (6, 3), "D4": (10, 6), "A4": (10, 3), "S4": (30, 4), "C12": (6, 6)}
    for name, n, gens in gl.examples():
        group = gl.closure(gens, n)
        counts, normal, _ = gl.census(group, n)
        assert (sum(counts.values()), normal) == expected[name]


def test_lagrange_and_a4_counterexample():
    for name, n, gens in gl.examples():
        group = gl.closure(gens, n)
        counts, _, missing = gl.census(group, n)
        assert all(len(group) % d == 0 for d in counts)
        assert missing == ([6] if name == "A4" else [])


def test_every_subgroup_is_closed_and_contains_identity():
    group = gl.closure(gl.examples()[3][2], 4)
    for sub in gl.all_subgroups(group, 4):
        assert (0, 1, 2, 3) in sub
        assert all(gl.compose(a, b) in sub for a in sub for b in sub)


def test_normality():
    s3 = gl.closure([(1, 0, 2), (1, 2, 0)], 3)
    a3 = gl.closure([(1, 2, 0)], 3)
    reflection = gl.closure([(1, 0, 2)], 3)
    assert gl.is_normal(a3, s3)
    assert not gl.is_normal(reflection, s3)
