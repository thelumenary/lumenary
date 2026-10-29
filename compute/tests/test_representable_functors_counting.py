import representable_functors_counting as rf


def test_maps_and_subsets_counts():
    assert len(rf.maps(3, 2)) == 8          # |Hom(3, 2)| = 2^3
    assert len(rf.maps(0, 5)) == 1          # one map out of the empty set
    assert len(rf.maps(2, 0)) == 0          # no map from a nonempty set to ∅
    assert len(rf.subsets(4)) == 16
    # subsets of X correspond bijectively to maps X -> {0, 1}
    assert sorted(rf.chi(s, 3) for s in rf.subsets(3)) == sorted(rf.maps(3, 2))


def test_powerset_naturality_has_no_failures():
    checks, failures = rf.powerset_naturality(3)
    assert failures == 0
    expected = sum(n ** m * 2 ** n for n in range(4) for m in range(4))
    assert checks == expected == 389


def test_hom_counts_match_relations():
    s3 = rf.symmetric_group_3()
    for n in range(1, 5):
        assert rf.count_homs(rf.cyclic_group(n), s3) == rf.nth_roots_of_one(n, s3)
    assert rf.count_homs(rf.klein_four(), s3) == rf.commuting_involution_pairs(s3) == 10
    # orders in S3: one identity, three transpositions, two 3-cycles
    assert [rf.nth_roots_of_one(n, s3) for n in (1, 2, 3, 6)] == [1, 4, 3, 6]


def test_count_homs_between_cyclic_groups():
    # |Hom(Z/m, Z/n)| = gcd(m, n)
    from math import gcd
    for m in range(1, 6):
        for n in range(1, 6):
            assert rf.count_homs(rf.cyclic_group(m), rf.cyclic_group(n)) == gcd(m, n)


def test_counting_test():
    assert rf.fits_contravariant([2 ** n for n in range(6)]) == 2
    assert rf.fits_contravariant([rf.bell(n) for n in range(6)]) is None
    assert rf.fits_covariant([n * n for n in range(6)]) == 2
    assert rf.fits_covariant([1] * 6) == 0             # Hom(∅, −) is constant 1
    assert rf.fits_covariant([n for n in range(6)]) == 1  # identity = Hom(1, −)
    assert rf.fits_covariant([2 ** n for n in range(6)]) is None
    assert rf.fits_covariant([2 * n for n in range(6)]) is None


def test_bell_numbers():
    assert [rf.bell(n) for n in range(7)] == [1, 1, 2, 5, 15, 52, 203]
