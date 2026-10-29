import sheaves_finite_spaces as sf

OPENS = sf.opens_of(sf.PSEUDOCIRCLE_OPENS)


def test_opens_form_a_topology():
    for u in OPENS:
        for v in OPENS:
            assert u | v in OPENS and u & v in OPENS
    assert frozenset() in OPENS and frozenset("abcd") in OPENS


def test_minimal_neighbourhoods():
    assert sf.minimal_nbhd("a", OPENS) == frozenset("a")
    assert sf.minimal_nbhd("c", OPENS) == frozenset("abc")
    assert sf.minimal_nbhd("d", OPENS) == frozenset("abd")


def test_locally_constant_sections_count_components():
    def count(u):
        return len(sf.locally_constant(frozenset(u), OPENS, (0, 1)))
    assert count("") == 1
    assert count("ab") == 4      # two components
    assert count("abc") == 2     # connected
    assert count("abcd") == 2


def test_constant_presheaf_fails_only_at_empty_set():
    fails = sf.sheaf_failures(OPENS, lambda u: [0, 1], lambda s, w: s)
    assert fails == [(frozenset(), ())]


def test_repaired_constant_presheaf_fails_on_disconnected_cover():
    fails = sf.sheaf_failures(OPENS, sf.constant_repaired, sf.restrict_repaired)
    assert fails and all(u == frozenset("ab") for u, _ in fails)


def test_locally_constant_functions_form_a_sheaf():
    def lc(u):
        return sf.locally_constant(u, OPENS, (0, 1))
    assert sf.sheaf_failures(OPENS, lc, sf.restrict) == []


def test_cech_cohomology():
    assert sf.cech_h1_dimension((frozenset("abc"), frozenset("abd")), OPENS) == (1, 1)
    iopens = sf.opens_of(sf.INTERVAL_OPENS)
    assert sf.cech_h1_dimension((frozenset("ac"), frozenset("ad")), iopens) == (1, 0)
