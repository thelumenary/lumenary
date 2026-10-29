import adjunctions_galois_finite as ag


def test_lattice_helpers():
    P, le = ag.divisors(12)
    assert P == [1, 2, 3, 4, 6, 12]
    assert ag.join(P, le, 4, 6) == 12 and ag.join(P, le, 2, 3) == 6
    assert ag.bottom(P, le) == 1
    Q, leq = ag.boolean_square()
    assert ag.join(Q, leq, 1, 2) == 3 and ag.bottom(Q, leq) == 0


def test_monotone_map_counts():
    # Monotone maps from the 3-chain to itself: multisets of size 3 from 3 values.
    assert len(ag.monotone_maps(ag.chain(3), ag.chain(3))) == 10
    assert len(ag.monotone_maps(ag.chain(2), ag.boolean_square())) == 9


def test_adjoint_exists_iff_joins_preserved():
    cases = [(ag.boolean_square(), ag.chain(3)), (ag.chain(3), ag.boolean_square()),
             (ag.divisors(12), ag.chain(3)), (ag.chain(3), ag.divisors(12))]
    for L, M in cases:
        for f in ag.monotone_maps(L, M):
            has = ag.right_adjoint(f, L, M) is not None
            assert has == ag.preserves_joins(f, L, M)


def test_right_adjoint_formula_and_counterexample():
    L, M = ag.chain(3), ag.divisors(12)
    u = ag.right_adjoint({0: 1, 1: 2, 2: 4}, L, M)
    assert u == {1: 0, 2: 1, 3: 0, 4: 2, 6: 1, 12: 2}
    # Constant map at the top does not preserve the bottom: no right adjoint.
    assert ag.right_adjoint({0: 12, 1: 12, 2: 12}, L, M) is None
    # A map that misses binary joins: on B2, send {0} and {1} to 1, {0,1} to 2.
    f = {0: 0, 1: 1, 2: 1, 3: 2}
    assert not ag.preserves_joins(f, ag.boolean_square(), ag.chain(3))
    assert ag.right_adjoint(f, ag.boolean_square(), ag.chain(3)) is None


def test_currying():
    assert ag.curry({(0, 0): 1, (0, 1): 0}, [0], [0, 1]) == {0: (1, 0)}
    assert ag.currying_report([0, 1], [0, 1], [0, 1], [0, 1], ["x", "y"]) == (True, True)
    assert ag.currying_report([0], [0, 1, 2], [0, 1], [0], ["x"]) == (True, True)
