import pytest

import computability_turing_machines as tm


def test_incrementer_on_every_byte():
    for n in range(256):
        out, steps = tm.increment(n)
        assert out == n + 1
        assert steps == tm.trailing_ones(n) + 1


def test_incrementer_larger_inputs_and_carries():
    assert tm.increment(0) == (1, 1)
    assert tm.increment(2**20 - 1) == (2**20, 21)
    assert tm.increment(2**20) == (2**20 + 1, 1)


def test_binary_tape_round_trip():
    for n in [0, 1, 2, 5, 11, 255, 1000]:
        assert tm.read_binary(tm.binary_tape(n)) == n
    assert tm.binary_tape(11) == {0: 1, -1: 1, -2: 0, -3: 1}


def test_unary_adder_values_and_steps():
    for m in range(8):
        for n in range(8):
            ones, steps = tm.add(m, n)
            assert ones == m + n
            assert steps == m + n + 3


def test_trailing_ones():
    assert [tm.trailing_ones(n) for n in range(8)] == [0, 1, 0, 2, 0, 1, 0, 3]


def test_run_raises_when_no_halt():
    loop = {("q", 0): (0, tm.RIGHT, "q"), ("q", 1): (1, tm.RIGHT, "q")}
    with pytest.raises(RuntimeError):
        tm.run(loop, {}, 0, "q", max_steps=50)


def test_amortised_cost_identity():
    # Summing (trailing ones + 1) over 0 .. 2^k - 1 gives 2^(k+1) - 1.
    for k in range(1, 10):
        total = sum(tm.increment(n)[1] for n in range(2**k))
        assert total == 2 ** (k + 1) - 1
