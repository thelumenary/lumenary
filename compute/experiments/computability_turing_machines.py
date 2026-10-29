"""Two small Turing machines, simulated and checked on many inputs.

A Turing machine is a finite table: in state q reading symbol s, write a
symbol, move one cell left or right, and go to a new state (or halt). We
simulate two machines from the lesson:

* a one-state binary incrementer, checked on every input n < 256, with the
  number of steps it takes (the amortised cost of counting is below 2 steps);
* a three-state unary adder turning 1^m 0 1^n into 1^(m+n), checked for all
  m, n <= 12.

The checks are exhaustive for the stated ranges only. They are evidence that
the machines are correct, not a proof for all inputs; the proofs are short
inductions given in the lesson's exercises.
"""

import textwrap

EXPERIMENT = {
    "id": "computability_turing_machines",
    "title": "Simulating Turing machines: a binary counter and a unary adder",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["computability"],
    "summary": (
        "Simulates a one-state binary incrementer on every input below 256 and a "
        "three-state unary adder on all pairs m, n <= 12, checking every output "
        "exactly and recording step counts. Exhaustive for those ranges only: it is "
        "evidence of correctness, not a proof for all inputs."
    ),
    "packages": [],
}

HALT = None
LEFT, RIGHT = -1, 1

#: Binary incrementer. Head starts on the least significant bit.
INCREMENT = {
    ("carry", 1): (0, LEFT, "carry"),
    ("carry", 0): (1, LEFT, HALT),
}

#: Unary adder: input 1^m 0 1^n with the head on the leftmost cell.
ADD = {
    ("A", 1): (1, RIGHT, "A"),
    ("A", 0): (1, RIGHT, "B"),
    ("B", 1): (1, RIGHT, "B"),
    ("B", 0): (0, LEFT, "C"),
    ("C", 1): (0, LEFT, HALT),
    ("C", 0): (0, LEFT, HALT),
}


def run(machine, tape, head, state, max_steps=10_000):
    """Run until the machine halts. Return (tape dict, head, steps).

    ``tape`` maps positions to symbols (missing cells are blank 0). Raises
    RuntimeError if the machine has not halted after ``max_steps`` steps:
    a step bound can never certify that a machine runs forever.
    """
    tape = dict(tape)
    for steps in range(1, max_steps + 1):
        write, move, state = machine[(state, tape.get(head, 0))]
        tape[head] = write
        head += move
        if state is HALT:
            return tape, head, steps
    raise RuntimeError("no halt within the step bound")


def binary_tape(n):
    """Binary digits of n, least significant bit at position 0, others left."""
    bits = bin(n)[2:]
    return {-i: int(b) for i, b in enumerate(reversed(bits))}


def read_binary(tape):
    """Read the number written on the tape (the most significant 1 first)."""
    cells = [p for p, s in tape.items() if s == 1]
    if not cells:
        return 0
    return sum(2 ** (-p) for p in cells if p <= 0)


def increment(n):
    """Run the incrementer on n; return (output, steps)."""
    tape, _, steps = run(INCREMENT, binary_tape(n), 0, "carry")
    return read_binary(tape), steps


def unary_tape(m, n):
    """The input 1^m 0 1^n written from position 0 to the right."""
    cells = [1] * m + [0] + [1] * n
    return {i: s for i, s in enumerate(cells)}


def add(m, n):
    """Run the unary adder on (m, n); return (number of 1s left, steps)."""
    tape, _, steps = run(ADD, unary_tape(m, n), 0, "A")
    return sum(tape.values()), steps


def trailing_ones(n):
    """Number of 1s at the end of the binary expansion of n."""
    count = 0
    while n & 1:
        n >>= 1
        count += 1
    return count


def main():
    print("1. Binary incrementer (1 state): carry 1s to the left, then halt.")
    rows = [(n, *increment(n)) for n in range(256)]
    bad = [n for n, out, _ in rows if out != n + 1]
    steps_ok = all(s == trailing_ones(n) + 1 for n, _, s in rows)
    print(f"   inputs 0..255 checked: {len(rows)}, wrong outputs: {len(bad)}")
    print(f"   steps = (trailing 1s) + 1 for every input: {steps_ok}")
    for n in (11, 127, 128):
        out, s = increment(n)
        unit = "step" if s == 1 else "steps"
        print(f"   {n:>3} = {n:08b} -> {out:>3} = {out:08b} in {s} {unit}")
    total = sum(s for _, _, s in rows)
    print(f"   average steps over 0..255: {total}/256 = {total / 256:.4f}")
    print()
    print("2. Unary adder (3 states): 1^m 0 1^n -> 1^(m+n).")
    pairs = [(m, n) for m in range(13) for n in range(13)]
    wrong = [(m, n) for m, n in pairs if add(m, n)[0] != m + n]
    print(f"   pairs with m, n <= 12 checked: {len(pairs)}, wrong: {len(wrong)}")
    print(f"   steps for (3, 4): {add(3, 4)[1]}; for (12, 12): {add(12, 12)[1]}")
    print("   steps = m + n + 3 on every pair: "
          f"{all(add(m, n)[1] == m + n + 3 for m, n in pairs)}")
    print()
    print(textwrap.fill(
        "Epistemic status: exact simulation, exhaustive for the 256 inputs and "
        "169 pairs above, so it is evidence of correctness and of the step "
        "formulas, not a proof for all inputs (that needs an induction on the "
        "length of the input). Every run here halted; a run that had not halted "
        "would have proved nothing, since no step bound separates slow machines "
        "from machines that never halt.",
        width=78,
    ))


if __name__ == "__main__":
    main()
