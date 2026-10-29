"""Same perimeter, different area - and the other way round.

Kofi has 24 metres of fence for a rectangular goat pen with whole-metre
sides. The program lists every such rectangle and its area. Then it fixes
the area instead (24 square metres) and lists every perimeter. Finally it
builds every shape made of 5 unit squares joined edge to edge (counting
shapes as different if they cannot be slid onto each other) and counts their
perimeters by checking every side of every square.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap
from collections import Counter

EXPERIMENT = {
    "id": "area_angles_rectangles",
    "title": "Same perimeter, different area: rectangles and pentominoes",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["area-angles"],
    "summary": (
        "Lists every whole-number rectangle with perimeter 24 (areas from 11 "
        "to 36, largest for the 6 x 6 square) and every rectangle with area "
        "24 (perimeters from 20 to 50). Then builds all 63 shapes of five "
        "unit squares (up to sliding) and counts their perimeters exactly. "
        "Exhaustive for these cases only."
    ),
    "packages": [],
}

#: The four neighbours of a square: right, left, up, down.
STEPS = ((1, 0), (-1, 0), (0, 1), (0, -1))


def rectangles_with_perimeter(p):
    """All (width, height) with whole sides, width <= height, perimeter p."""
    if p % 2:
        return []
    half = p // 2
    return [(w, half - w) for w in range(1, half // 2 + 1)]


def rectangles_with_area(a):
    """All (width, height) with whole sides, width <= height, area a."""
    return [(w, a // w) for w in range(1, a + 1) if a % w == 0 and w * w <= a]


def perimeter(squares):
    """Count the sides of the squares that face outside the shape."""
    shape = set(squares)
    return sum((x + dx, y + dy) not in shape
               for x, y in shape for dx, dy in STEPS)


def normalise(squares):
    """Slide a shape so that its lowest-left corner is at (0, 0)."""
    min_x = min(x for x, _ in squares)
    min_y = min(y for _, y in squares)
    return frozenset((x - min_x, y - min_y) for x, y in squares)


def shapes_of_size(n):
    """All shapes of n unit squares joined edge to edge, up to sliding."""
    shapes = {normalise([(0, 0)])}
    for _ in range(n - 1):
        bigger = set()
        for shape in shapes:
            for x, y in shape:
                for dx, dy in STEPS:
                    new = (x + dx, y + dy)
                    if new not in shape:
                        bigger.add(normalise(shape | {new}))
        shapes = bigger
    return shapes


def main():
    print("Rectangles with perimeter 24 (whole-number sides):")
    for w, h in rectangles_with_perimeter(24):
        print(f"  {w:>2} x {h:<2} area {w * h:>2}")
    print("Same fence, different areas: the square 6 x 6 holds the most.")
    print()
    print("Rectangles with area 24:")
    for w, h in rectangles_with_area(24):
        print(f"  {w:>2} x {h:<2} perimeter {2 * (w + h):>2}")
    print("Same area, different perimeters.")
    print()
    pentominoes = shapes_of_size(5)
    counts = Counter(perimeter(s) for s in pentominoes)
    print(f"Shapes of 5 squares (up to sliding): {len(pentominoes)}")
    for p in sorted(counts):
        print(f"  perimeter {p}: {counts[p]} shapes")
    print("All have area 5, but not all have the same perimeter.")
    print()
    print(textwrap.fill(
        "Epistemic status: exact and exhaustive for these cases - every "
        "whole-number rectangle with perimeter 24 or area 24, and every "
        "shape of 5 squares, was checked. It shows that area and perimeter "
        "are different measures; it does not prove anything about other "
        "sizes or shapes with curved sides.",
        width=78,
    ))


if __name__ == "__main__":
    main()
