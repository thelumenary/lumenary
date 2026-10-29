import pytest

import formal_proof_lean_proof_checker as pc

P_IMP_P = pc.imp("p", "p")


def test_axiom_shapes():
    assert pc.axiom("K", "a", "b") == pc.imp("a", pc.imp("b", "a"))
    s = pc.axiom("S", "a", "b", "c")
    assert s[1] == pc.imp("a", pc.imp("b", "c"))
    with pytest.raises(ValueError):
        pc.axiom("K", "a")


def test_identity_proof_checks():
    assert pc.check(pc.P_IMP_P, P_IMP_P) == (True, "")
    lines, err = pc.derive(pc.P_IMP_P)
    assert err is None and len(lines) == 5 and lines[-1] == P_IMP_P


def test_faulty_proofs_rejected():
    bad = pc.P_IMP_P[:3] + [("MP", 1, 3)]
    ok, msg = pc.check(bad, P_IMP_P)
    assert not ok and msg.startswith("line 4")
    assert pc.check([("MP", 2, 1)], P_IMP_P)[0] is False  # forward reference
    assert pc.check(pc.P_IMP_P[:4], P_IMP_P)[0] is False  # stops early
    assert pc.check([("X", "p")], P_IMP_P)[0] is False


def test_tautologies():
    assert pc.is_tautology(P_IMP_P)
    assert not pc.is_tautology(pc.imp("p", "q"))
    assert pc.is_tautology(pc.axiom("S", "p", "q", "r"))
    assert pc.is_tautology(pc.imp(pc.imp(pc.imp("p", "q"), "p"), "p"))


def test_proved_lines_are_tautologies():
    lines, _ = pc.derive(pc.P_IMP_P)
    assert all(pc.is_tautology(f) for f in lines)
    assert pc.show(pc.imp("p", pc.imp("q", "p"))) == "(p -> (q -> p))"
