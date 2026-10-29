"""The heat equation on a computer: series solution versus finite differences.

We solve u_t = u_xx on [0, pi] with u = 0 at both ends and u(0, x) = x(pi - x).
Separation of variables gives the exact solution
    u(t, x) = sum over odd n of (8 / (pi n^3)) exp(-n^2 t) sin(n x).
The explicit scheme replaces u_t and u_xx by difference quotients:
    u_j <- r u_(j-1) + (1 - 2r) u_j + r u_(j+1),  r = dt / dx^2.
For r <= 1/2 each new value is an average of old ones (discrete maximum
principle), the scheme is stable, and its error shrinks like dx^2. For
r > 1/2 the highest grid mode is multiplied by about 1 - 4r < -1 per step and
the computation explodes. Evidence: numerical; the series is summed to 200
terms (truncation error below 1e-6).
"""

import math

EXPERIMENT = {
    "id": "pde_intro_heat_scheme",
    "title": "Heat equation: series solution versus finite differences",
    "evidence": ["numerical"],
    "lessons": ["pde-intro"],
    "summary": (
        "Solves u_t = u_xx on [0, pi] with zero boundary values and initial "
        "data x(pi - x), comparing the explicit finite-difference scheme with "
        "the Fourier sine series solution. For r = dt/dx^2 <= 1/2 the error is "
        "small and falls like dx^2 and the maximum principle holds; for r = "
        "0.6 the highest mode grows each step and the scheme blows up."
    ),
    "packages": [],
}


def exact(t, x, terms=200):
    """Fourier sine series solution for initial data x(pi - x)."""
    return sum(8 / (math.pi * n ** 3) * math.exp(-n * n * t) * math.sin(n * x)
               for n in range(1, 2 * terms, 2))


def step(u, r):
    """One explicit step with fixed zero boundary values u[0] = u[-1] = 0."""
    new = [0.0] * len(u)
    for j in range(1, len(u) - 1):
        new[j] = r * u[j - 1] + (1 - 2 * r) * u[j] + r * u[j + 1]
    return new


def solve(intervals, r, t_end):
    """Run the scheme to (about) t_end; return (grid, values, t, max seen)."""
    dx = math.pi / intervals
    dt = r * dx * dx
    steps = max(1, round(t_end / dt))
    xs = [j * dx for j in range(intervals + 1)]
    u = [x * (math.pi - x) for x in xs]
    u[-1] = 0.0
    top = max(u)
    for _ in range(steps):
        u = step(u, r)
        top = max(top, max(u))
    return xs, u, steps * dt, top


def max_error(intervals, r, t_end):
    """Largest |scheme - exact| over the grid at the final time."""
    xs, u, t, _ = solve(intervals, r, t_end)
    return max(abs(a - exact(t, x)) for x, a in zip(xs, u))


def main():
    peak0 = (math.pi / 2) ** 2
    print("u_t = u_xx on [0, pi], u(0, x) = x(pi - x), compared at t = 0.5")
    print("  r     max error (20 intervals)   largest value ever / initial max")
    for r in [0.25, 0.4, 0.5, 0.6]:
        _, _, _, top = solve(20, r, 0.5)
        print(f" {r:4.2f}   {max_error(20, r, 0.5):24.3e}   {top / peak0:18.3g}")
    print()
    print("Refining the grid with r = 0.4 fixed (error should fall ~ dx^2):")
    prev = None
    for n in [10, 20, 40]:
        e = max_error(n, 0.4, 0.5)
        ratio = "" if prev is None else f"   ratio {prev / e:.2f}"
        print(f"  {n:3d} intervals: max error {e:.3e}{ratio}")
        prev = e
    print()
    print("Epistemic status: numerical experiment. The series solution and the")
    print("stability threshold r = 1/2 are proved in the lesson (the discrete")
    print("maximum principle is also checked in Lean); the table only shows")
    print("them at work for one initial condition and a few grids.")


if __name__ == "__main__":
    main()
