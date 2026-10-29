import pytest

import intro_lean_mini_checker as mc

ZERO, S, add, num, var = mc.ZERO, mc.S, mc.add, mc.num, mc.var


def test_numerals_and_show():
    assert num(0) == ZERO and num(2) == S(S(ZERO))
    assert mc.show(num(7)) == "7"
    assert mc.show(add(num(2), num(3))) == "2 + 3"
    assert mc.show(S(add(var("n"), ZERO))) == "S(n + 0)"


def test_rules_at_the_root():
    n = var("n")
    assert mc.rewrite_root(add(n, ZERO), {}) == [("A1", n)]
    assert mc.rewrite_root(add(n, S(ZERO)), {}) == [("A2", S(add(n, ZERO)))]
    assert mc.rewrite_root(add(ZERO, n), {}) == []  # stuck: n is a variable


def test_two_plus_two_proof_is_accepted():
    two = num(2)
    proof = [add(two, two), S(add(two, num(1))), S(S(add(two, ZERO))), num(4)]
    assert mc.check_chain(proof) == (True, ["A2", "A2", "A1"])
    # Read backwards, it is still a valid chain.
    ok, names = mc.check_chain(list(reversed(proof)))
    assert ok and all(name.endswith("backwards") for name in names)


def test_wrong_steps_are_rejected():
    two = num(2)
    assert mc.check_chain([add(two, two), num(5)]) == (False, 1)
    assert mc.check_chain([add(two, two), num(4)]) == (False, 1)  # true, but 3 steps at once
    assert mc.check_chain([add(two, two), S(add(two, num(1))), num(5)]) == (False, 2)


def test_normalize_computes_sums():
    for a in range(6):
        for b in range(6):
            nf, steps = mc.normalize(add(num(a), num(b)))
            assert nf == num(a + b) and steps == b + 1


def test_zero_plus_variable_is_stuck_but_n_plus_zero_is_not():
    n = var("n")
    assert mc.normalize(add(n, ZERO)) == (n, 1)
    assert mc.normalize(add(ZERO, n)) == (add(ZERO, n), 0)


def test_induction_cases_check_with_hypothesis():
    k = var("k")
    assert mc.check_chain([add(ZERO, ZERO), ZERO]) == (True, ["A1"])
    step = [add(ZERO, S(k)), S(add(ZERO, k)), S(k)]
    assert mc.check_chain(step, {"IH": (add(ZERO, k), k)}) == (True, ["A2", "IH"])
    assert mc.check_chain(step)[0] is False  # without the hypothesis it fails


def test_normalize_limit():
    with pytest.raises(RuntimeError):
        mc.normalize(add(num(0), num(50)), limit=10)
