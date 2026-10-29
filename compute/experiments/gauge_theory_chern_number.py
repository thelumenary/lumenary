"""The topological charge of a U(1) lattice gauge field on a torus.

A U(1) gauge field on an N x N periodic lattice assigns a phase exp(i a) to
each oriented link. The plaquette angle theta_p (the lattice field strength,
reduced to (-pi, pi]) is the flux through one square. Because every link
borders two plaquettes with opposite orientations, the raw plaquette angles
sum to zero, so after reduction their sum is a multiple of 2 pi:

    Q = (1 / 2 pi) * sum_p theta_p   is an integer,

the lattice version of the first Chern number (1/2 pi) * integral of F.
We build fields of charge k, apply random gauge transformations (Q and every
theta_p are unchanged), add random noise to the links (Q stays an integer and
equals k while the field is smooth, but can jump when it is rough), and
compare with the naive charge sum sin(theta_p) / 2 pi, which is not an
integer.

Evidence: numerical (floating-point) computation on a few lattices with a
fixed seed. The integrality of Q is a theorem for every configuration whose
plaquettes avoid the value pi; the runs illustrate it.
"""

import math
import random

EXPERIMENT = {
    "id": "gauge_theory_chern_number",
    "title": "Topological charge of U(1) lattice gauge fields on a torus",
    "evidence": ["numerical", "experimental"],
    "lessons": ["gauge-theory"],
    "summary": (
        "Builds U(1) lattice gauge fields of prescribed charge k on a periodic "
        "N x N lattice, computes the plaquette angles and the integer charge "
        "Q = sum(theta_p) / 2 pi (a lattice first Chern number), and shows that "
        "Q is unchanged by random gauge transformations and by small noise, "
        "while large noise can change it. Numerical illustration of theorems."
    ),
    "packages": [],
}


def reduce_angle(t):
    """The representative of t modulo 2 pi in (-pi, pi]."""
    r = math.fmod(t + math.pi, 2 * math.pi)
    if r <= 0:
        r += 2 * math.pi
    return r - math.pi


def charge_k_field(n, k):
    """Link angles (ax, ay) on an n x n torus with uniform flux 2 pi k / n^2.

    ax[x][y] is the angle on the link (x, y) -> (x + 1, y), ay[x][y] on the
    link (x, y) -> (x, y + 1); indices are taken modulo n.
    """
    b = 2 * math.pi * k / n ** 2
    ax = [[0.0] * n for _ in range(n)]
    ay = [[b * x for _ in range(n)] for x in range(n)]
    for y in range(n):
        ax[n - 1][y] = -b * n * y
    return ax, ay


def plaquettes(ax, ay):
    """Reduced plaquette angles theta[x][y] (counter-clockwise from (x, y))."""
    n = len(ax)
    return [[reduce_angle(ax[x][y] + ay[(x + 1) % n][y]
                          - ax[x][(y + 1) % n] - ay[x][y])
             for y in range(n)] for x in range(n)]


def charge(ax, ay):
    """Q = (1 / 2 pi) * sum of reduced plaquette angles."""
    return sum(map(sum, plaquettes(ax, ay))) / (2 * math.pi)


def naive_charge(ax, ay):
    """(1 / 2 pi) * sum of sin(theta_p): the 'field theory' density."""
    return sum(math.sin(t) for row in plaquettes(ax, ay) for t in row) / (2 * math.pi)


def gauge_transform(ax, ay, lam):
    """a(x -> y) -> a(x -> y) + lam(x) - lam(y), i.e. U -> g(x) U g(y)^-1."""
    n = len(ax)
    bx = [[ax[x][y] + lam[x][y] - lam[(x + 1) % n][y] for y in range(n)]
          for x in range(n)]
    by = [[ay[x][y] + lam[x][y] - lam[x][(y + 1) % n] for y in range(n)]
          for x in range(n)]
    return bx, by


def add_noise(ax, ay, sigma, rng):
    """Add independent Gaussian noise of size sigma to every link angle."""
    return ([[a + rng.gauss(0, sigma) for a in row] for row in ax],
            [[a + rng.gauss(0, sigma) for a in row] for row in ay])


def max_plaquette_change(f1, f2):
    """Largest difference of corresponding plaquette angles (mod 2 pi)."""
    p1, p2 = plaquettes(*f1), plaquettes(*f2)
    return max(abs(reduce_angle(a - b)) for r1, r2 in zip(p1, p2)
               for a, b in zip(r1, r2))


def main():
    rng = random.Random(1974)
    n = 12
    print(f"U(1) lattice gauge fields on a {n} x {n} torus")
    print(f"{'k':>3}{'Q':>9}{'Q after gauge':>15}{'max dtheta':>12}"
          f"{'naive Q':>10}")
    for k in [0, 1, 2, -3, 7]:
        field = charge_k_field(n, k)
        lam = [[rng.uniform(-math.pi, math.pi) for _ in range(n)]
               for _ in range(n)]
        moved = gauge_transform(*field, lam)
        print(f"{k:>3}{charge(*field):>9.4f}{charge(*moved):>15.4f}"
              f"{max_plaquette_change(field, moved):>12.1e}"
              f"{naive_charge(*field):>10.4f}")
    print()
    print("Noise on every link of the k = 2 field (10 samples each):")
    base = charge_k_field(n, 2)
    for sigma in [0.05, 0.3, 1.0, 3.0]:
        qs = [charge(*add_noise(*base, sigma, rng)) for _ in range(10)]
        off = max(abs(q - round(q)) for q in qs)
        print(f"  sigma = {sigma:<5}Q = {[round(q) for q in qs]}")
        print(f"{'':16}largest distance from an integer: {off:.0e}")
    print()
    print("Epistemic status: floating-point computation on finitely many")
    print("configurations. That Q is an integer, and gauge invariant, is a")
    print("theorem (each link occurs in two plaquettes with opposite signs);")
    print("that Q survives small noise is continuity of an integer-valued")
    print("function. The jumps for rough fields are lattice artefacts.")


if __name__ == "__main__":
    main()
