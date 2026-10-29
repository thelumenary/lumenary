"""Slides, turns and flips of letters on squared paper.

Each letter is a set of squares on a grid, with (0, 0) at its centre. The
program moves the letters with flips and half turns and draws the results
in text, so you can see that a flip and a half turn are different moves -
even though for a very symmetric letter like H they give the same picture.
Then it checks, for every point of a 21 x 21 grid, that flipping twice
puts the point back, that two flips in crossing lines make a turn, that
two flips in parallel lines make a slide, and that no move changes the
distance between two points.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap
from itertools import product

EXPERIMENT = {
    "id": "symmetry_transformations_moves",
    "title": "Slides, turns and flips on squared paper",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["symmetry-transformations"],
    "summary": (
        "Draws the letters F and H after a flip and after a half turn, to "
        "show that the two moves differ even when the pictures agree. Then "
        "checks on every point of a 21 x 21 grid that flipping twice undoes "
        "a flip, two crossing flips make a turn, two parallel flips make a "
        "slide, and moves keep distances. Exact, for that grid only."
    ),
    "packages": [],
}

#: Letters drawn in a 3 x 5 box of squares centred at (0, 0).
LETTERS = {
    "F": {(-1, y) for y in range(-2, 3)} | {(0, 2), (1, 2), (0, 0)},
    "H": {(-1, y) for y in range(-2, 3)} | {(1, y) for y in range(-2, 3)}
    | {(0, 0)},
}


def flip_v(p):
    """Flip in the vertical mirror line through (0, 0)."""
    return (-p[0], p[1])


def flip_h(p):
    """Flip in the horizontal mirror line through (0, 0)."""
    return (p[0], -p[1])


def flip_d(p):
    """Flip in the diagonal mirror line y = x."""
    return (p[1], p[0])


def flip_at(c, p):
    """Flip in the vertical mirror line x = c."""
    return (2 * c - p[0], p[1])


def quarter_turn(p):
    """Turn a quarter turn anticlockwise about (0, 0)."""
    return (-p[1], p[0])


def half_turn(p):
    """Turn a half turn about (0, 0)."""
    return (-p[0], -p[1])


def slide(a, b, p):
    """Slide a squares right and b squares up."""
    return (p[0] + a, p[1] + b)


def dist2(p, q):
    """The square of the distance between two points."""
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2


def move_shape(move, shape):
    """Apply a move to every square of a shape."""
    return {move(p) for p in shape}


def picture(shape):
    """Rows of '#' and '.' for a shape inside the 3 x 5 letter box."""
    return ["".join("#" if (x, y) in shape else "." for x in range(-1, 2))
            for y in range(2, -3, -1)]


def check_on_grid(radius):
    """Check the rules on every point (and pair of points) of a square grid.

    Returns a dict from rule name to True/False.
    """
    pts = list(product(range(-radius, radius + 1), repeat=2))
    moves = [flip_v, flip_d, quarter_turn, lambda p: slide(3, -2, p)]
    some = pts[:: max(1, len(pts) // 60)]
    return {
        "flip twice = no move": all(flip_v(flip_v(p)) == p for p in pts),
        "two flips at 90 degrees = half turn":
            all(flip_h(flip_v(p)) == half_turn(p) for p in pts),
        "two flips at 45 degrees = quarter turn":
            all(flip_v(flip_d(p)) == quarter_turn(p) for p in pts),
        "flips in x = 1 then x = 4 = slide 6":
            all(flip_at(4, flip_at(1, p)) == slide(6, 0, p) for p in pts),
        "moves keep every distance": all(
            dist2(m(p), m(q)) == dist2(p, q)
            for m in moves for p in some for q in pts),
    }


def main():
    for name, shape in LETTERS.items():
        rows = zip(picture(shape), picture(move_shape(flip_v, shape)),
                   picture(move_shape(half_turn, shape)))
        print(f"{name}: original  flipped  half-turned")
        for a, b, c in rows:
            print(f"   {a:<10}{b:<9}{c}")
        same = move_shape(flip_v, shape) == move_shape(half_turn, shape)
        print(f"   Flip and half turn give the same picture? "
              f"{'yes' if same else 'no'}")
    corner = (-1, 2)
    print(f"Even for H, the corner square {corner} goes to {flip_v(corner)}"
          f" by the flip,")
    print(f"but to {half_turn(corner)} by the half turn: different moves.")
    print()
    print("Checked on every point of a 21 x 21 grid:")
    for rule, ok in check_on_grid(10).items():
        print(f"  {rule:<40} {'true' if ok else 'FALSE'}")
    print()
    print(textwrap.fill(
        "Epistemic status: exact whole-number arithmetic, checked on every "
        "point of one 21 x 21 grid (and many pairs of points for distances). "
        "That is finite evidence; the lesson explains why the rules hold "
        "everywhere, and the Lean module proves them for every point.",
        width=78,
    ))


if __name__ == "__main__":
    main()
