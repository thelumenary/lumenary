import lambda_calculus_confluence as cf

I = ("lam", ("var", 0))
K = ("lam", ("lam", ("var", 1)))
W = ("lam", ("app", ("var", 0), ("var", 0)))
OMEGA = ("app", W, W)


def test_term_counts():
    # Size 1: the single free variable; size 2: λ.0 and λ.1.
    assert cf.terms_of_size(1, 0) == [("var", 0)]
    assert sorted(cf.terms_of_size(2, 0)) == [("lam", ("var", 0)), ("lam", ("var", 1))]
    # Closed terms (free=0) of size 3: λλ.0 and λλ.1 only.
    assert len(cf.terms_of_size(3, 0, free=0)) == 2
    for t in cf.terms_of_size(6, 0):
        assert cf.size_of(t) == 6


def test_reducts_find_every_redex():
    t = ("app", W, ("app", I, ("var", 0)))  # (λx. x x)(I z): two redexes
    rs = cf.reducts(t)
    assert len(rs) == 2
    assert ("app", W, ("var", 0)) in rs
    assert ("app", ("app", I, ("var", 0)), ("app", I, ("var", 0))) in rs
    assert cf.reducts(("var", 3)) == frozenset()


def test_omega_graph_is_a_single_loop():
    g = cf.reduction_graph(OMEGA)
    assert g == {OMEGA: frozenset({OMEGA})}
    assert cf.has_cycle(g)
    assert cf.analyse(OMEGA)["normal_forms"] == 0


def test_k_i_omega_is_weakly_but_not_strongly_normalising():
    t = ("app", ("app", K, I), OMEGA)
    g = cf.reduction_graph(t)
    normal = [u for u in g if not g[u]]
    assert normal == [I]
    assert cf.has_cycle(g)


def test_routes_of_different_lengths():
    t = ("app", W, ("app", I, ("var", 0)))
    g = cf.reduction_graph(t)
    nf = ("app", ("var", 0), ("var", 0))
    assert not g[nf]
    assert cf.path_lengths(g, t, nf) == (2, 3)


def test_exploding_term_is_set_aside():
    w3 = ("lam", ("app", ("app", ("var", 0), ("var", 0)), ("var", 0)))
    assert cf.reduction_graph(("app", w3, w3), cap=50) is None


def test_survey_finds_no_counterexample():
    s = cf.survey(9)
    assert s["terms"] == 9419
    assert s["two_nf"] == 0 and s["not_joinable"] == 0
    assert s["no_nf"] == 1  # Omega itself
