import sympy

import formal_methods_verification_conditions as vc

a, b, q, r = vc.a, vc.b, vc.q, vc.r


def test_wp_of_assignment_is_substitution():
    # wp(x := e, Q) = Q[e/x]; sequences substitute from the back
    post = sympy.Eq(q, 7)
    assert vc.wp_assignments([(q, q + 1)], post) == sympy.Eq(q + 1, 7)
    two = vc.wp_assignments([(r, r - b), (q, q + r)], sympy.Eq(q, 0))
    assert sympy.simplify(two.lhs - two.rhs - (q + r - b)) == 0


def test_good_invariant_vcs_hold_algebraically_and_on_the_box():
    for name, hyp, concl in vc.verification_conditions(vc.GOOD_INV):
        assert vc.equations_reduce(hyp, concl), name
        assert vc.box_counterexample(hyp, concl, 3) is None, name


def test_weak_invariant_exit_vc_has_a_genuine_counterexample():
    vcs = {n: (h, c) for n, h, c in vc.verification_conditions(vc.WEAK_INV)}
    hyp, concl = vcs["exit"]
    point = vc.box_counterexample(hyp, concl, 4)
    assert point is not None
    env = dict(zip(vc.VARS, point))
    assert bool(hyp.subs(env)) and not bool(concl.subs(env))
    # the failure is exactly the forgotten conjunct r >= 0
    assert env[r] < 0


def test_run_program_divides():
    assert vc.run_program(17, 5) == (3, 2)
    assert vc.run_program(0, 3) == (0, 0)
    assert vc.run_program(4, 4) == (1, 0)
    for a0 in range(0, 30):
        for b0 in range(1, 7):
            assert vc.run_program(a0, b0) == divmod(a0, b0)


def test_random_tests_are_seeded_and_pass():
    assert vc.random_tests(200) == 0
    assert vc.random_tests(50, seed=1) == vc.random_tests(50, seed=1)


def test_fmt_is_compact():
    text = vc.fmt(sympy.And(sympy.Eq(a, q * b + r), r >= 0))
    assert "=" in text and ">=" in text and "&" not in text
