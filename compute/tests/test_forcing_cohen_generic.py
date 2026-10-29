import forcing_cohen_generic as fc


def test_meet_decide_and_avoid_extend():
    p = (1, 0)
    q = fc.meet_decide(p, 5)
    assert len(q) == 6 and q[:2] == p
    assert fc.meet_decide(q, 3) == q
    zero = lambda n: 0
    r = fc.meet_avoid((0, 0), zero)
    assert r == (0, 0, 1) and fc.disagreement(r, zero) == 2
    assert fc.meet_avoid(r, zero) == r


def test_ground_reals():
    reals = fc.ground_reals()
    names = [name for name, _ in reals]
    assert "primes" in names and "(01)" in names and "1(0)" in names
    primes = dict(reals)["primes"]
    assert [primes(n) for n in range(8)] == [0, 0, 1, 1, 0, 1, 0, 1]
    alt = dict(reals)["(01)"]
    assert [alt(n) for n in range(5)] == [0, 1, 0, 1, 0]


def test_generic_escapes_every_listed_real():
    reals = fc.ground_reals()
    g, chain = fc.build_generic(reals, 32)
    assert fc.is_chain(chain)
    assert len(g) >= 32
    assert all(fc.disagreement(g, x) is not None for _, x in reals)


def test_generic_escapes_any_finite_list_of_periodic_reals():
    # The construction works against any list, here ten other rules.
    reals = [("x%d" % k, (lambda k: (lambda n: (n * k) % 2))(k)) for k in range(10)]
    g, _ = fc.build_generic(reals, 5)
    assert all(fc.disagreement(g, x) is not None for _, x in reals)


def test_is_chain_detects_incompatibility():
    assert fc.is_chain([(), (1,), (1, 0)])
    assert not fc.is_chain([(1,), (0, 0)])
