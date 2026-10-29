import enumerative_combinatorics_partitions as ep


def test_known_partition_numbers():
    p = ep.partition_counts(100)
    assert p[:11] == [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42]
    assert p[50] == 204226
    assert p[100] == 190569292


def test_euler_theorem_up_to_80():
    assert ep.odd_part_counts(80) == ep.distinct_part_counts(80)


def test_generating_functions_match_enumeration():
    odd = ep.odd_part_counts(15)
    distinct = ep.distinct_part_counts(15)
    total = ep.partition_counts(15)
    for n in range(16):
        parts = ep.partitions(n)
        assert len(parts) == total[n]
        assert sum(all(x % 2 for x in q) for q in parts) == odd[n]
        assert sum(len(set(q)) == len(q) for q in parts) == distinct[n]


def test_glaisher_is_a_bijection():
    for n in range(1, 16):
        parts = ep.partitions(n)
        odds = [q for q in parts if all(x % 2 for x in q)]
        distinct = {q for q in parts if len(set(q)) == len(q)}
        images = [ep.glaisher(q) for q in odds]
        assert len(set(images)) == len(images)
        assert set(images) == distinct
        assert all(sum(q) == n for q in images)


def test_series_helpers():
    s = [1] + [0] * 5
    ep.times_geometric(s, 2)
    assert s == [1, 0, 1, 0, 1, 0]
    ep.times_one_plus(s, 1)
    assert s == [1, 1, 1, 1, 1, 1]


def test_ramanujan_congruence_and_asymptotics():
    p = ep.partition_counts(200)
    assert all(p[n] % 5 == 0 for n in range(4, 200, 5))
    assert all(p[n] % 7 == 0 for n in range(5, 200, 7))
    ratios = [p[n] / ep.hardy_ramanujan(n) for n in (50, 100, 200)]
    assert ratios == sorted(ratios) and 0.9 < ratios[0] < 1 and ratios[-1] < 1
