"""Pointwise versus uniform convergence: measuring sup-distances.

Uniform convergence of f_n to f on S means sup over S of |f_n - f| -> 0. We
measure that supremum for three classic sequences, using exact formulas where
calculus gives them and a fine grid as a cross-check:

1. x^n -> 0 pointwise on [0, 1), but the sup over [0, 1) is 1 for every n
   (not uniform); on [0, 0.9] the sup is 0.9^n -> 0 (uniform).
2. h_n(x) = 2 n^2 x exp(-n^2 x^2) -> 0 pointwise on [0, 1], yet the integral
   of h_n over [0, 1] is 1 - exp(-n^2) -> 1: limit and integral cannot be
   swapped, and indeed sup h_n = sqrt(2) n exp(-1/2) blows up.
3. s_n(x) = sin(n x)/n -> 0 uniformly (sup = 1/n), but the derivatives
   cos(n x) do not converge at x = pi: limit and derivative cannot be swapped.

Evidence: exact closed forms (derived in the docstrings) plus numerical grid
checks; the grid can only ever estimate a supremum from below.
"""

import math

EXPERIMENT = {
    "id": "real_analysis_uniform_convergence",
    "title": "Pointwise versus uniform convergence: sup-distances",
    "evidence": ["exact", "numerical"],
    "lessons": ["real-analysis"],
    "summary": (
        "Computes sup |f_n - f| for x^n on [0, 1) and on [0, 0.9], for the "
        "spikes 2n^2 x exp(-n^2 x^2) and for sin(nx)/n, using exact formulas "
        "and a grid cross-check. Shows convergence that is pointwise but not "
        "uniform, a sequence whose integrals do not converge to the integral "
        "of the limit, and uniform convergence that does not carry over to "
        "derivatives. Finite computations: illustrations, not proofs."
    ),
    "packages": [],
}


def grid(a, b, points):
    """Equally spaced points from a to b inclusive (points >= 2)."""
    if points < 2:
        raise ValueError("need at least two points")
    step = (b - a) / (points - 1)
    return [a + i * step for i in range(points)]


def grid_sup(func, xs):
    """Largest |func(x)| over the sample points xs: a lower bound for the sup."""
    return max(abs(func(x)) for x in xs)


def spike(n, x):
    """h_n(x) = 2 n^2 x exp(-n^2 x^2), a moving spike of area about 1."""
    return 2 * n * n * x * math.exp(-(n * x) ** 2)


def spike_sup(n):
    """Exact sup of h_n on [0, 1]: at x = 1/(n sqrt 2), h_n = sqrt(2) n e^(-1/2)."""
    return math.sqrt(2) * n * math.exp(-0.5)


def spike_integral(n):
    """Exact integral of h_n over [0, 1]: [-exp(-n^2 x^2)] from 0 to 1."""
    return 1 - math.exp(-n * n)


def midpoint_integral(func, a, b, strips):
    """Composite midpoint rule, a numerical check of spike_integral."""
    width = (b - a) / strips
    return width * sum(func(a + (i + 0.5) * width) for i in range(strips))


def main():
    xs = grid(0.0, 1.0, 20001)[:-1]  # [0, 1) sampled
    print("1. x^n -> 0 pointwise on [0, 1); is it uniform?")
    print("    n   sup on [0,0.9]   grid sup on [0,1)   exact sup on [0,1)")
    for n in [1, 5, 20, 100, 1000]:
        near = grid_sup(lambda x: x ** n, xs)
        print(f"{n:5d}   {0.9 ** n:14.3e}   {near:17.6f}   {1:18d}")
    print("   On [0, 0.9]: uniform. On [0, 1): the sup stays 1, so not uniform.")
    print()
    print("2. Spikes h_n -> 0 pointwise on [0, 1], but their integrals do not")
    print("    n   h_n(1/2)    sup h_n   integral (exact)   midpoint rule")
    for n in [1, 2, 5, 10, 50]:
        mid = midpoint_integral(lambda x: spike(n, x), 0.0, 1.0, 4000)
        print(f"{n:5d}   {spike(n, 0.5):9.2e}   {spike_sup(n):7.2f}"
              f"   {spike_integral(n):16.6f}   {mid:13.6f}")
    print("   lim of integrals = 1, but integral of lim = 0.")
    print()
    print("3. sin(nx)/n -> 0 uniformly (sup = 1/n); derivatives cos(nx)")
    for n in [1, 2, 3, 4, 10, 11]:
        sup = grid_sup(lambda x: math.sin(n * x) / n, grid(0, math.pi, 2001))
        print(f"   n = {n:2d}: grid sup = {sup:.4f}, derivative at pi ="
              f" {math.cos(n * math.pi):+.0f}")
    print()
    print("Epistemic status: the suprema and integrals in the 'exact' columns")
    print("come from closed forms proved by calculus; the grid and midpoint")
    print("columns are numerical cross-checks (a grid only bounds a sup from")
    print("below). Finitely many n can illustrate, but not prove, what happens")
    print("as n -> infinity; the proofs are in the lesson.")


if __name__ == "__main__":
    main()
