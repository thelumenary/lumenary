"""The eight grid symmetries: composing turns and flips, exhaustively.

Four rotations about the origin (by 0, 90, 180 and 270 degrees) and four
reflections (in the x-axis, the y-axis and the lines y = x and y = -x) all
send grid points to grid points. The experiment composes every pair of them,
identifies each result by its effect on the points (1, 0) and (0, 1), and
prints the composition table. From the table it reads off: composites stay
in the set (closure), every move has an undo, two reflections always give a
rotation, and the order of composition often matters. It also checks on a
grid that all eight keep distances. Exact and exhaustive for these 8 moves.
"""

EXPERIMENT = {
    "id": "rigid_motions_similarity_symmetries",
    "title": "Composing the eight grid symmetries",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["rigid-motions-similarity"],
    "summary": (
        "Composes every pair of the eight rigid motions that fix the origin and "
        "map the square grid to itself (four rotations, four reflections), prints "
        "the composition table, and checks closure, undos, that two reflections "
        "always give a rotation (by twice the angle between the mirrors), how "
        "often order matters, and that all eight keep distances on a grid."
    ),
    "packages": [],
}

#: Each move as a function of (x, y), with its mirror angle or turn angle.
MOVES = {
    "R0": lambda x, y: (x, y),
    "R90": lambda x, y: (-y, x),
    "R180": lambda x, y: (-x, -y),
    "R270": lambda x, y: (y, -x),
    "Mx": lambda x, y: (x, -y),     # mirror: the x-axis (angle 0)
    "Md": lambda x, y: (y, x),      # mirror: y = x (angle 45)
    "My": lambda x, y: (-x, y),     # mirror: the y-axis (angle 90)
    "Ma": lambda x, y: (-y, -x),    # mirror: y = -x (angle 135)
}
MIRROR_ANGLE = {"Mx": 0, "Md": 45, "My": 90, "Ma": 135}
NAMES = list(MOVES)


def signature(f):
    """Images of (1, 0) and (0, 1); a linear move is fixed by these two."""
    return (f(1, 0), f(0, 1))


def name_of(f):
    """The name of the move with the same effect as f."""
    sig = signature(f)
    for name, g in MOVES.items():
        if signature(g) == sig:
            return name
    return None


def then(first, second):
    """The composite: do ``first``, then ``second``."""
    f, g = MOVES[first], MOVES[second]
    return lambda x, y: g(*f(x, y))


def table():
    """table[(a, b)] = name of 'a, then b'."""
    return {(a, b): name_of(then(a, b)) for a in NAMES for b in NAMES}


def keeps_distances(f, radius=3):
    """True if f keeps squared distances between all grid points."""
    pts = [(x, y) for x in range(-radius, radius + 1)
           for y in range(-radius, radius + 1)]
    for p in pts:
        for q in pts:
            fp, fq = f(*p), f(*q)
            d_before = (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2
            d_after = (fp[0] - fq[0]) ** 2 + (fp[1] - fq[1]) ** 2
            if d_before != d_after:
                return False
    return True


def main():
    t = table()
    print("Composition table: row = first move, column = second move")
    print("      " + "".join(f"{b:>6}" for b in NAMES))
    for a in NAMES:
        print(f"{a:>6}" + "".join(f"{t[(a, b)]:>6}" for b in NAMES))
    print()
    closed = all(v is not None for v in t.values())
    undo = all(any(t[(a, b)] == "R0" for b in NAMES) for a in NAMES)
    print(f"Every composite is one of the eight: {closed}")
    print(f"Every move has an undo among the eight: {undo}")
    mirrors = list(MIRROR_ANGLE)
    twice = all(
        t[(m1, m2)] == f"R{(2 * (MIRROR_ANGLE[m2] - MIRROR_ANGLE[m1])) % 360}"
        for m1 in mirrors for m2 in mirrors)
    print("Mirror m1 then mirror m2 = rotation by 2 x (angle m2 - angle m1):"
          f" {twice}")
    pairs = [(a, b) for i, a in enumerate(NAMES) for b in NAMES[i + 1:]]
    differ = [(a, b) for a, b in pairs if t[(a, b)] != t[(b, a)]]
    print(f"Pairs of different moves where the order matters: {len(differ)}"
          f" of {len(pairs)}")
    print(f"  e.g. Mx then Md = {t[('Mx', 'Md')]}, but Md then Mx ="
          f" {t[('Md', 'Mx')]}")
    print(f"All eight keep distances on a 7 x 7 grid: "
          f"{all(keeps_distances(f) for f in MOVES.values())}")
    print()
    print("Epistemic status: exact and exhaustive for these eight moves. The")
    print("two-mirrors rule is proved in the lesson for mirrors at any angle;")
    print("here it is checked only for mirrors at multiples of 45 degrees.")


if __name__ == "__main__":
    main()
