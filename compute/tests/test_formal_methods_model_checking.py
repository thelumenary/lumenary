import formal_methods_model_checking as mc


def test_initial_state_and_successors():
    s = mc.INITIAL
    assert s == (0, 0, False, False, 0)
    # from the initial state either process can start: two successors
    assert sorted(mc.successors(mc.step_peterson, s)) == [
        (0, 1, False, False, 0), (1, 0, False, False, 0)]


def test_naive_protocol_violates_mutual_exclusion_with_shortest_trace():
    r = mc.check("check-then-set")
    assert not r["mutex"]
    trace = r["counterexample"]
    assert trace[0] == mc.INITIAL
    assert trace[-1][0] == 3 and trace[-1][1] == 3
    # each consecutive pair is a genuine transition of the protocol
    for a, b in zip(trace, trace[1:]):
        assert b in mc.successors(mc.step_check_then_set, a)
    # BFS gives a shortest trace: 6 steps (each process needs 3 to reach pc 3)
    assert len(trace) == 7


def test_set_then_check_is_safe_but_deadlocks():
    r = mc.check("set-then-check")
    assert r["mutex"]
    assert r["deadlocks"] == [(2, 2, True, True, 0)]
    assert not r["ag_ef_crit0"]


def test_peterson_is_safe_live_and_deadlock_free():
    r = mc.check("Peterson")
    assert r["mutex"] and not r["deadlocks"] and r["ag_ef_crit0"]
    assert r["states"] == 34
    sizes = r["ef_sizes"]
    # the iterates increase and stabilise at the whole state space
    assert sizes == sorted(sizes) and sizes[-1] == sizes[-2] == 34


def test_ef_fixpoint_on_a_small_graph():
    succ = {0: [1], 1: [2], 2: [2], 3: [3]}
    ef, sizes = mc.ef_fixpoint(succ, {2})
    assert ef == {0, 1, 2}
    assert sizes == [1, 2, 3, 3]
    assert mc.ef_fixpoint(succ, set())[0] == set()


def test_blocked_steps_return_none():
    waiting = (3, 3, True, True, 0)
    assert mc.step_peterson(waiting, 1) is None      # turn = 0, flag0 up
    assert mc.step_peterson(waiting, 0) == (4, 3, True, True, 0)
