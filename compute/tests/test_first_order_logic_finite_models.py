import pytest

import first_order_logic_finite_models as fo


def test_satisfaction_clauses():
    dom = range(3)
    cycle = frozenset({(0, 1), (1, 2), (2, 0)})
    serial = ("all", "x", ("some", "y", fo.R("x", "y")))
    hub = ("some", "x", ("all", "y", fo.R("x", "y")))
    assert fo.satisfies(dom, cycle, serial)
    assert not fo.satisfies(dom, cycle, hub)
    assert fo.satisfies(dom, cycle, fo.R("x", "y"), {"x": 0, "y": 1})
    assert not fo.satisfies(dom, cycle, fo.R("x", "y"), {"x": 1, "y": 0})
    assert fo.satisfies(dom, cycle, ("imp", fo.R("x", "x"), ("eq", "x", "y")),
                        {"x": 0, "y": 2})          # false premise
    with pytest.raises(ValueError):
        fo.satisfies(dom, cycle, ("xor", fo.R("x", "y")), {"x": 0, "y": 0})


def test_strict_and_nonstrict_orders():
    dom = range(3)
    # "less than" on {0, 1, 2}: every x has a y with ... fails at the top
    less = frozenset((a, b) for a in dom for b in dom if a < b)
    forall_exists = ("all", "x", ("some", "y", fo.R("y", "x")))
    exists_forall = ("some", "y", ("all", "x", fo.R("y", "x")))
    assert not fo.satisfies(dom, less, forall_exists)   # x = 0 has nothing below
    assert not fo.satisfies(dom, less, exists_forall)
    leq = less | {(a, a) for a in dom}
    assert fo.satisfies(dom, leq, forall_exists)
    assert fo.satisfies(dom, leq, exists_forall)       # 0 is below everything


def test_model_counts():
    eq, po, lo = (fo.THEORIES[k] for k in
                  ("equivalence relation", "partial order", "linear order"))
    assert [len(fo.models(n, eq)) for n in (1, 2, 3)] == [1, 2, 5]   # Bell
    assert [len(fo.models(n, po)) for n in (1, 2, 3)] == [1, 3, 19]
    assert [len(fo.models(n, lo)) for n in (1, 2, 3)] == [1, 2, 6]   # n!
    assert len(fo.all_relations(3)) == 512


def test_isomorphism_classes():
    po = fo.THEORIES["partial order"]
    assert len({fo.canonical(r, 3) for r in fo.models(3, po)}) == 5
    lo = fo.THEORIES["linear order"]
    assert len({fo.canonical(r, 3) for r in fo.models(3, lo)}) == 1
    r = frozenset({(0, 1)})
    assert fo.canonical(r, 3) == fo.canonical(frozenset({(2, 0)}), 3)


def test_invariance_and_separation():
    assert fo.invariance_holds(2, list(fo.SENTENCES.values()))
    assert fo.invariance_holds(3, list(fo.SENTENCES.values()))
    po = fo.THEORIES["partial order"]
    reps = {fo.canonical(r, 3): r for r in fo.models(3, po)}
    profiles = {tuple(fo.satisfies(range(3), r, s)
                      for s in fo.SENTENCES.values()) for r in reps.values()}
    assert len(profiles) == 5
