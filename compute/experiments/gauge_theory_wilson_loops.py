"""Wilson loops: gauge invariance, non-abelian holonomy and Aharonov-Bohm.

Part 1. A random SU(2) lattice gauge field on a square grid. Parallel
transport around a closed loop is a product of link matrices. A random gauge
transformation changes that holonomy matrix (by conjugation), but not its
trace, the Wilson loop.

Part 2. A U(1) field on a grid whose curvature (plaquette angle) vanishes on
every square except one, which carries flux Phi: a thin solenoid. Loops that
never touch the solenoid, and see zero field everywhere they go, still pick
up the phase exp(i * w * Phi), where w is their winding number around it.
Two "Dirac strings" (vector potentials) for the same solenoid differ by a
gauge transformation and give identical Wilson loops.

Evidence: numerical (floating-point) computation on concrete configurations
with a fixed seed. Gauge invariance is a theorem (formalised in Lean in the
lesson); these runs illustrate it.
"""

import cmath
import math
import random

EXPERIMENT = {
    "id": "gauge_theory_wilson_loops",
    "title": "Wilson loops, gauge invariance and the Aharonov-Bohm phase",
    "evidence": ["numerical", "experimental"],
    "lessons": ["gauge-theory"],
    "summary": (
        "Builds a random SU(2) lattice gauge field and shows that a random gauge "
        "transformation changes holonomy matrices but not their traces (Wilson "
        "loops). Then builds a U(1) field that is flat except on one plaquette "
        "(a solenoid of flux Phi) and shows that loops in the field-free region "
        "acquire the phase exp(i w Phi), the same for two gauge-equivalent "
        "vector potentials. Numerical illustration of theorems."
    ),
    "packages": [],
}


def mat_mul(a, b):
    """Product of 2 x 2 complex matrices."""
    return [[a[i][0] * b[0][j] + a[i][1] * b[1][j] for j in range(2)]
            for i in range(2)]


def dagger(a):
    """Conjugate transpose (the inverse, for unitary matrices)."""
    return [[a[j][i].conjugate() for j in range(2)] for i in range(2)]


def trace(a):
    """Trace of a 2 x 2 matrix."""
    return a[0][0] + a[1][1]


def random_su2(rng):
    """A random SU(2) matrix from a random unit quaternion."""
    q = [rng.gauss(0, 1) for _ in range(4)]
    r = math.sqrt(sum(x * x for x in q))
    a, b, c, d = (x / r for x in q)
    return [[complex(a, b), complex(c, d)], [complex(-c, d), complex(a, -b)]]


def rectangle_path(x0, y0, w, h):
    """Counter-clockwise rectangle of width w and height h from (x0, y0)."""
    return ["E"] * w + ["N"] * h + ["W"] * w + ["S"] * h, (x0, y0)


STEP = {"E": (1, 0), "W": (-1, 0), "N": (0, 1), "S": (0, -1)}


def holonomy(links, start, steps, mul, inv, one):
    """Ordered product of link variables along a lattice path.

    links[(x, y, "E")] lives on (x, y) -> (x + 1, y), links[(x, y, "N")] on
    (x, y) -> (x, y + 1); backward steps use the inverse.
    """
    x, y = start
    total = one
    for s in steps:
        dx, dy = STEP[s]
        if s in "EN":
            u = links[(x, y, s)]
        else:
            u = inv(links[(x + dx, y + dy, "E" if s == "W" else "N")])
        total = mul(total, u)
        x, y = x + dx, y + dy
    return total


def gauge(links, g, mul, inv):
    """U(x -> y) -> g(x) U(x -> y) g(y)^-1."""
    out = {}
    for (x, y, d), u in links.items():
        dx, dy = STEP[d]
        out[(x, y, d)] = mul(mul(g[(x, y)], u), inv(g[(x + dx, y + dy)]))
    return out


def grid_links(size, value):
    """All links of the grid {0..size}^2, each set by value(x, y, d)."""
    links = {}
    for x in range(size + 1):
        for y in range(size + 1):
            if x < size:
                links[(x, y, "E")] = value(x, y, "E")
            if y < size:
                links[(x, y, "N")] = value(x, y, "N")
    return links


def solenoid_field(size, center, phi, string="east"):
    """U(1) phases: flat everywhere except flux phi through one plaquette.

    The Dirac string runs from the plaquette to the edge of the grid, east or
    north; links it crosses carry exp(i phi) (or exp(-i phi)).
    """
    cx, cy = center

    def value(x, y, d):
        if string == "east" and d == "N" and y == cy and x > cx:
            return cmath.exp(1j * phi)
        if string == "north" and d == "E" and x == cx and y > cy:
            return cmath.exp(-1j * phi)
        return 1 + 0j
    return grid_links(size, value)


def u1_ops():
    """Multiplication, inverse and identity for unit complex numbers."""
    return (lambda a, b: a * b), (lambda a: a.conjugate()), 1 + 0j


def plaquette_angles(links, size):
    """Angle of the holonomy around every unit square of the grid."""
    mul, inv, one = u1_ops()
    return {(x, y): cmath.phase(holonomy(links, (x, y), "ENWS", mul, inv, one))
            for x in range(size) for y in range(size)}


def main():
    rng = random.Random(1959)
    size = 8
    one2 = [[1 + 0j, 0j], [0j, 1 + 0j]]
    links = grid_links(size, lambda x, y, d: random_su2(rng))
    g = {(x, y): random_su2(rng) for x in range(size + 1)
         for y in range(size + 1)}
    moved = gauge(links, g, mat_mul, dagger)
    print("Part 1: random SU(2) field on an 8 x 8 grid, random gauge change")
    print(f"{'loop':<18}{'|change of matrix|':>20}{'Wilson loop W':>17}"
          f"{'change of W':>14}")
    for w, h in [(1, 1), (3, 2), (6, 6)]:
        steps, start = rectangle_path(1, 2, w, h)
        a = holonomy(links, start, steps, mat_mul, dagger, one2)
        b = holonomy(moved, start, steps, mat_mul, dagger, one2)
        dm = max(abs(a[i][j] - b[i][j]) for i in range(2) for j in range(2))
        wa, wb = trace(a).real, trace(b).real
        print(f"{f'{w} x {h} rectangle':<18}{dm:>20.3f}{wa:>17.6f}"
              f"{abs(wa - wb):>14.1e}")
    print()
    phi = 1.0
    print(f"Part 2: U(1) solenoid of flux {phi} through the square at (3, 3)")
    mul, inv, one = u1_ops()
    east = solenoid_field(size, (3, 3), phi, "east")
    north = solenoid_field(size, (3, 3), phi, "north")
    curv = plaquette_angles(east, size)
    nonzero = [p for p, t in curv.items() if abs(t) > 1e-12]
    print(f"  squares with nonzero curvature: {nonzero}")
    loops = [("around it, 4 x 4", ["E"] * 4 + ["N"] * 4 + ["W"] * 4 + ["S"] * 4,
              (1, 1)),
             ("around it twice", (["E"] * 4 + ["N"] * 4 + ["W"] * 4
                                  + ["S"] * 4) * 2, (1, 1)),
             ("clockwise", ["N"] * 6 + ["E"] * 6 + ["S"] * 6 + ["W"] * 6,
              (1, 1)),
             ("crosses string only", ["E"] * 2 + ["N"] * 2 + ["W"] * 2
              + ["S"] * 2, (5, 2))]
    print(f"  {'loop':<20}{'phase, string east':>20}{'phase, string north':>21}")
    for name, steps, start in loops:
        pe = cmath.phase(holonomy(east, start, steps, mul, inv, one))
        pn = cmath.phase(holonomy(north, start, steps, mul, inv, one))
        print(f"  {name:<20}{pe:>20.6f}{pn:>21.6f}")
    print("  (phases are taken in (-pi, pi]; winding twice gives 2 Phi = 2.)")
    print()
    print("Epistemic status: floating-point computation on specific lattice")
    print("configurations. It illustrates two theorems: Wilson loops are gauge")
    print("invariant, and the holonomy of a flat U(1) connection around a loop")
    print("is exp(i * winding number * enclosed flux).")


if __name__ == "__main__":
    main()
