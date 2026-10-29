"""Every two-state Turing machine, classified: the busy beaver S(2) = 6.

Radó's busy-beaver function S(n) is the largest number of steps taken by an
n-state, two-symbol Turing machine that halts when started on a blank tape;
Sigma(n) is the largest number of 1s such a machine can leave. Both grow
faster than any computable function, so no algorithm computes them.

For n = 2 there are 12^4 = 20736 machines, and we can settle every one:
it either halts (we watch it) or it carries a certificate that it never
halts. The three certificates are sound arguments, explained in the lesson:

* no halting instruction can ever be reached from the start state;
* a whole configuration repeats, so the run is periodic;
* a translated cycle: the machine returns to the same state at a new record
  position with the same tape contents behind it, so it repeats forever,
  shifted along the tape.

Running a machine for longer never certifies that it runs forever; the
certificates are what turn this search into a (computer-assisted) proof.
"""

import itertools
import textwrap

EXPERIMENT = {
    "id": "computability_busy_beaver",
    "title": "All two-state Turing machines: halting runs and non-halting proofs",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["computability"],
    "summary": (
        "Enumerates all 20736 two-state, two-symbol Turing machines, runs each on a "
        "blank tape, and either watches it halt or finds a sound certificate that it "
        "never halts (unreachable halt, repeated configuration, translated cycle). "
        "Every machine is classified, which yields S(2) = 6 and Sigma(2) = 4, as "
        "far as this code is correct."
    ),
    "packages": [],
}

HALT = -1
OPTIONS = [(w, m, n) for w in (0, 1) for m in (-1, 1) for n in (0, 1, HALT)]
#: Rado's champion: A0 -> 1RB, A1 -> 1LB, B0 -> 1LA, B1 -> 1R halt.
CHAMPION = ((1, 1, 1), (1, -1, 1), (1, -1, 0), (1, 1, HALT))


def all_machines():
    """All tables (A0, A1, B0, B1); entry = (write, move, next state)."""
    return itertools.product(OPTIONS, repeat=4)


def halt_reachable(machine):
    """Can a halting instruction be reached from state A in the state graph?"""
    seen, todo = {0}, [0]
    while todo:
        q = todo.pop()
        for symbol in (0, 1):
            nxt = machine[2 * q + symbol][2]
            if nxt == HALT:
                return True
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return False


def _translated(history, t1, t2, d):
    """Sound test for a translated cycle between two records in direction d."""
    s1, p1, tape1 = history[t1]
    s2, p2, tape2 = history[t2]
    if s1 != s2 or p1 == p2:
        return False
    back = max(-d * (history[t][1] - p1) for t in range(t1, t2 + 1))
    return all(tape1.get(p1 - d * o, 0) == tape2.get(p2 - d * o, 0)
               for o in range(back + 1))


def classify(machine, max_steps=30):
    """Return ("halts", steps, ones) or (certificate name, step, None).

    Certificates: "unreachable", "cycle", "translated". If none applies
    within max_steps the answer is ("unknown", max_steps, None).
    """
    if not halt_reachable(machine):
        return "unreachable", 0, None
    tape, pos, state, lo, hi = {}, 0, 0, 0, 0
    history, seen = [], set()
    records = {1: [], -1: []}
    for step in range(max_steps):
        key = (state, pos, frozenset(p for p, s in tape.items() if s))
        if key in seen:
            return "cycle", step, None
        seen.add(key)
        history.append((state, pos, dict(tape)))
        for d in (1, -1):
            if step == 0 or (pos > hi if d == 1 else pos < lo):
                records[d].append(step)
                for t1 in records[d][:-1]:
                    if _translated(history, t1, step, d):
                        return "translated", step, None
        lo, hi = min(lo, pos), max(hi, pos)
        write, move, nxt = machine[2 * state + tape.get(pos, 0)]
        tape[pos] = write
        pos += move
        if nxt == HALT:
            return "halts", step + 1, sum(tape.values())
        state = nxt
    return "unknown", max_steps, None


def census(max_steps=30):
    """Classify every machine; return (counts, max steps, max ones)."""
    counts, best_steps, best_ones = {}, 0, 0
    for machine in all_machines():
        kind, steps, ones = classify(machine, max_steps)
        counts[kind] = counts.get(kind, 0) + 1
        if kind == "halts":
            best_steps = max(best_steps, steps)
            best_ones = max(best_ones, ones)
    return counts, best_steps, best_ones


def main():
    counts, best_steps, best_ones = census()
    total = sum(counts.values())
    print(f"Two-state, two-symbol machines: {total} (12 choices for 4 entries)")
    labels = [
        ("halts", "halt on the blank tape (watched)"),
        ("unreachable", "never halt: no halt instruction reachable"),
        ("cycle", "never halt: a configuration repeats"),
        ("translated", "never halt: translated cycle"),
        ("unknown", "unclassified within 30 steps"),
    ]
    for kind, label in labels:
        print(f"  {counts.get(kind, 0):>6}  {label}")
    print()
    print(f"Longest halting run S(2) = {best_steps} steps; "
          f"most 1s Sigma(2) = {best_ones}.")
    kind, steps, ones = classify(CHAMPION)
    print(f"Rado's champion A0:1RB A1:1LB B0:1LA B1:1RH -> {kind}, "
          f"{steps} steps, {ones} ones.")
    print("Known values (from the literature, not computed here):")
    print("  S(3) = 21, S(4) = 107, S(5) = 47,176,870; S(6) is unknown.")
    print()
    print(textwrap.fill(
        "Epistemic status: an exhaustive, exact classification of all 20736 "
        "machines. Each non-halting verdict rests on a certificate that is a "
        "valid proof of non-halting, so the computation proves S(2) = 6 and "
        "Sigma(2) = 4 - provided this code implements the machines and the "
        "certificates correctly, which tests check but do not prove. Simply "
        "running machines longer could never have shown that they run forever.",
        width=78,
    ))


if __name__ == "__main__":
    main()
