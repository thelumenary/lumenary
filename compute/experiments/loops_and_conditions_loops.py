"""Loops that close, loops that stop, and a loop that never stops.

A turtle starts at a point facing up and runs the loop 'repeat n times:
forward 1, turn right by some angle'. The program reports how far from the
start it finishes and how much it has turned altogether: the path closes
up when the total turning is a whole number of full turns (360 degrees).
Then it runs three 'repeat until' loops: counting up by 3 until the number
is bigger than 20, counting down by 2 from 10 until it is exactly 0, and
counting down by 2 from 9 until it is exactly 0 - a loop whose stopping
condition is never true, so the program has to give up after 1000 steps.
"""

import math
import textwrap

EXPERIMENT = {
    "id": "loops_and_conditions_loops",
    "title": "Loops that close, loops that stop, and one that never stops",
    "evidence": ["numerical", "exact"],
    "lessons": ["loops-and-conditions"],
    "summary": (
        "Runs turtle loops 'repeat n times: forward 1, turn right a degrees' "
        "for squares, triangles, hexagons and a star, reporting the distance "
        "from the start (floating point) and the total turning. Then runs "
        "three 'repeat until' loops, one of which never meets its stopping "
        "condition and is cut off after 1000 steps."
    ),
    "packages": [],
}


def turtle_loop(repeats, angle):
    """Run 'repeat: forward 1, turn right angle'. Return (end, total turn)."""
    x, y, heading = 0.0, 0.0, 90.0  # heading in degrees; 90 means 'up'
    for _ in range(repeats):
        x += math.cos(math.radians(heading))
        y += math.sin(math.radians(heading))
        heading -= angle  # turning right is clockwise
    return (x, y), repeats * angle


def repeat_until(start, step, stop, limit=1000):
    """Repeat 'number = step(number)' until stop(number) is true.

    Returns (final number, steps taken, stopped?) - gives up after limit."""
    number = start
    for steps in range(limit):
        if stop(number):
            return number, steps, True
        number = step(number)
    return number, limit, stop(number)


def main():
    print("repeat n times: forward 1, turn right by a degrees")
    print("   n     a  distance from start  total turning")
    for repeats, angle in [(4, 90), (3, 120), (6, 60), (3, 60), (5, 144),
                           (8, 45)]:
        (x, y), turned = turtle_loop(repeats, angle)
        distance = math.hypot(x, y)
        print(f"{repeats:>4}  {angle:>4}  {distance:>19.3f}  {turned:>9} deg")
    print("Here the path closes exactly when the total turning is a whole")
    print("number of full turns: 360, 720, ... degrees.")
    print()
    print("repeat until:")
    loops = [
        ("start 0, add 3 until bigger than 20", 0, lambda n: n + 3,
         lambda n: n > 20),
        ("start 10, take 2 until exactly 0", 10, lambda n: n - 2,
         lambda n: n == 0),
        ("start 9, take 2 until exactly 0", 9, lambda n: n - 2,
         lambda n: n == 0),
    ]
    for text, start, step, stop in loops:
        number, steps, stopped = repeat_until(start, step, stop)
        if stopped:
            print(f"  {text}: stops after {steps} steps at {number}")
        else:
            print(f"  {text}: gave up after {steps} steps (at {number})")
    print()
    print(textwrap.fill(
        "Epistemic status: the turtle distances are floating-point "
        "calculations, rounded to 3 decimal places, so '0.000' means 'zero "
        "up to rounding' - the lesson explains with angles why these paths "
        "close exactly. The counting loops use exact whole numbers. Giving "
        "up after 1000 steps does not prove that a loop never stops; the "
        "odd-number argument in the lesson does.",
        width=78,
    ))


if __name__ == "__main__":
    main()
