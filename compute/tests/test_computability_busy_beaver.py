import computability_busy_beaver as bb


def test_champion_halts_after_six_steps_with_four_ones():
    assert bb.classify(bb.CHAMPION) == ("halts", 6, 4)


def test_census_classifies_everything():
    counts, best_steps, best_ones = bb.census()
    assert sum(counts.values()) == 12 ** 4 == 20736
    assert counts.get("unknown", 0) == 0
    assert (best_steps, best_ones) == (6, 4)
    assert counts["halts"] == 9784


def test_unreachable_halt_certificate():
    # A0 -> 1RB, B0 -> 1LA and the 1-entries never halt either.
    machine = ((1, 1, 1), (1, 1, 0), (1, -1, 0), (0, -1, 1))
    assert not bb.halt_reachable(machine)
    assert bb.classify(machine)[0] == "unreachable"


def test_cycle_certificate():
    # A0 -> 0RB, B0 -> 0LA bounces between two cells forever; B1 halts but
    # is never reached because the tape stays blank.
    machine = ((0, 1, 1), (1, 1, bb.HALT), (0, -1, 0), (1, 1, bb.HALT))
    assert bb.halt_reachable(machine)
    assert bb.classify(machine)[0] == "cycle"


def test_translated_certificate():
    # A0 -> 1RA marches right forever, leaving 1s; A1 would halt.
    machine = ((1, 1, 0), (1, 1, bb.HALT), (0, 1, 0), (0, 1, 0))
    assert bb.classify(machine)[0] == "translated"


def test_certificates_never_contradict_long_runs():
    # Soundness spot check: machines certified as non-halting do not halt
    # within 200 steps of plain simulation.
    def halts_within(machine, n):
        tape, pos, state = {}, 0, 0
        for _ in range(n):
            w, m, nxt = machine[2 * state + tape.get(pos, 0)]
            tape[pos] = w
            pos += m
            if nxt == bb.HALT:
                return True
            state = nxt
        return False

    checked = 0
    for k, machine in enumerate(bb.all_machines()):
        if k % 7:
            continue
        kind = bb.classify(machine)[0]
        if kind != "halts":
            assert not halts_within(machine, 200)
            checked += 1
    assert checked > 1000
