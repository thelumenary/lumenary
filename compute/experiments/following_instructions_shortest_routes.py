"""Shortest programs, many correct answers, and fixing a bug.

Part 1 runs every arrow-card program of up to 6 cards (up, down, left,
right) from the start square of a grid. For each square it finds the
shortest programs that end there, and checks two patterns: the shortest
length is "squares across plus squares up", and the number of shortest
programs is a binomial coefficient. Part 2 is a floor robot with the buttons
forward (F), turn left (L) and turn right (R): it tries every one-instruction
change of a buggy program to find the fixes, counts the correct programs, and
checks which pairs of instructions can be swapped without changing the result.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from itertools import product
from math import comb
import textwrap

EXPERIMENT = {
    "id": "following_instructions_shortest_routes",
    "title": "Shortest programs, many answers, and fixing a bug",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["following-instructions"],
    "summary": (
        "Runs all 5,460 arrow programs of 1 to 6 cards, finds the shortest "
        "programs to each square reached and checks that their length is the "
        "across-plus-up distance and their number a binomial coefficient; then "
        "searches every one-instruction fix of a buggy floor-robot program. "
        "Exhaustive for these program lengths only."
    ),
    "packages": [],
}

MOVES = {"U": (0, 1), "D": (0, -1), "L": (-1, 0), "R": (1, 0)}
HEADINGS = [(0, 1), (1, 0), (0, -1), (-1, 0)]  # north, east, south, west


def run_arrows(program, start=(0, 0)):
    """Follow arrow cards (a string of U, D, L, R); return the end square."""
    x, y = start
    for card in program:
        dx, dy = MOVES[card]
        x, y = x + dx, y + dy
    return (x, y)


def shortest_programs(max_cards):
    """Map each square to (shortest length, number of shortest programs)."""
    best = {(0, 0): (0, 1)}
    for n in range(1, max_cards + 1):
        for program in product("UDLR", repeat=n):
            end = run_arrows(program)
            if end not in best:
                best[end] = (n, 1)
            elif best[end][0] == n:
                best[end] = (n, best[end][1] + 1)
    return best


def distance(square):
    """Squares across plus squares up or down from the start."""
    return abs(square[0]) + abs(square[1])


def run_robot(program, pos=(0, 0), facing=0):
    """Press robot buttons (a string of F, L, R); return (square, facing).

    The robot starts facing north (index 0 of HEADINGS); turns happen on
    the spot.
    """
    x, y = pos
    for button in program:
        if button == "F":
            dx, dy = HEADINGS[facing]
            x, y = x + dx, y + dy
        elif button == "L":
            facing = (facing - 1) % 4
        elif button == "R":
            facing = (facing + 1) % 4
        else:
            raise ValueError(f"unknown button {button!r}")
    return (x, y), facing


def one_change_fixes(program, target):
    """Every program that differs in one instruction and ends on target."""
    fixes = []
    for i, old in enumerate(program):
        for new in "FLR":
            if new != old:
                changed = program[:i] + new + program[i + 1:]
                if run_robot(changed)[0] == target:
                    fixes.append(changed)
    return fixes


def correct_robot_programs(target, max_len):
    """All robot programs of length 1..max_len that end on the target."""
    return ["".join(p) for n in range(1, max_len + 1)
            for p in product("FLR", repeat=n) if run_robot(p)[0] == target]


def main():
    best = shortest_programs(6)
    print("1. Arrow programs: every program of 1 to 6 cards was run.")
    print("   square    shortest  how many shortest  (a+b choose a)")
    for sq in [(1, 0), (2, 1), (-2, 1), (2, 2), (3, 1), (3, 3)]:
        n, count = best[sq]
        a, b = abs(sq[0]), abs(sq[1])
        print(f"   {str(sq):<9} {n:6d} {count:13d} {comb(a + b, a):16d}")
    near = [sq for sq in best if distance(sq) <= 6]
    ok_len = all(best[sq][0] == distance(sq) for sq in near)
    ok_count = all(best[sq][1] == comb(distance(sq), abs(sq[0])) for sq in near)
    print(f"   {len(near)} squares reached. Shortest = across + up: {ok_len}")
    print(f"   Number of shortest programs = (a+b choose a): {ok_count}")
    print()
    target, buggy = (1, 2), "FFLF"
    print("2. Floor robot: F = forward, L = turn left, R = turn right.")
    print(f"   Target: 1 right and 2 up. Buggy program {buggy} ends at "
          f"{run_robot(buggy)[0]}.")
    print(f"   One-instruction fixes: {', '.join(one_change_fixes(buggy, target))}")
    good = correct_robot_programs(target, 6)
    shortest = min(len(p) for p in good)
    print(f"   Correct programs of up to 6 buttons: {len(good)}; "
          f"the shortest has {shortest}.")
    for a, b in [("F", "L"), ("F", "R"), ("L", "R")]:
        same = run_robot(a + b) == run_robot(b + a)
        print(f"   {a}{b} and {b}{a} end the same way: {same}")
    print()
    print(textwrap.fill(
        "Epistemic status: exact and exhaustive for the programs tried (all "
        "arrow programs of up to 6 cards, all robot programs of up to 6 "
        "buttons), so these results are certain for them. The patterns are "
        "evidence, not a proof, for longer programs; the lesson's Lean file "
        "proves that no arrow program is shorter than the distance and that "
        "a program of exactly that length always exists.",
        width=78,
    ))


if __name__ == "__main__":
    main()
