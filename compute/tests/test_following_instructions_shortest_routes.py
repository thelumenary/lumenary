from math import comb

import pytest

import following_instructions_shortest_routes as fi


def test_run_arrows():
    assert fi.run_arrows("") == (0, 0)
    assert fi.run_arrows("RRU") == (2, 1)
    assert fi.run_arrows("URR") == fi.run_arrows("RUR") == (2, 1)
    assert fi.run_arrows("UD", start=(5, 5)) == (5, 5)


def test_shortest_programs_match_distance_and_binomial():
    best = fi.shortest_programs(5)
    assert best[(0, 0)] == (0, 1)
    assert best[(2, 1)] == (3, 3)
    assert best[(-1, -1)] == (2, 2)
    for sq, (n, count) in best.items():
        if fi.distance(sq) <= 5:
            assert n == fi.distance(sq)
            assert count == comb(n, abs(sq[0]))


def test_no_program_beats_the_distance():
    # every square reached by k cards is at most k away
    from itertools import product
    for k in range(4):
        for p in product("UDLR", repeat=k):
            assert fi.distance(fi.run_arrows(p)) <= k


def test_robot_turns_and_order():
    assert fi.run_robot("") == ((0, 0), 0)
    assert fi.run_robot("FR") == ((0, 1), 1)
    assert fi.run_robot("RF") == ((1, 0), 1)
    assert fi.run_robot("LR") == fi.run_robot("RL") == ((0, 0), 0)
    assert fi.run_robot("LLLL") == ((0, 0), 0)
    with pytest.raises(ValueError):
        fi.run_robot("FX")


def test_debugging_finds_the_one_fix():
    assert fi.run_robot("FFLF")[0] == (-1, 2)
    assert fi.one_change_fixes("FFLF", (1, 2)) == ["FFRF"]
    assert fi.one_change_fixes("FFRF", (1, 2)) == []  # already correct: any change breaks it


def test_correct_programs():
    good = fi.correct_robot_programs((1, 2), 6)
    assert "FFRF" in good and "RFLFF" in good
    assert min(len(p) for p in good) == 4
    assert all(fi.run_robot(p)[0] == (1, 2) for p in good)
