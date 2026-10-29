"""Fourier series: the Gibbs overshoot and Parseval's identity, measured.

The square wave sign(sin x) has Fourier series (4/pi) * sum over odd k of
sin(kx)/k. Its partial sum with n non-zero terms, S_n, has derivative
(2/pi) sin(2nx)/sin(x), so its first maximum to the right of the jump at 0 is
at x = pi/(2n), exactly. We evaluate S_n there: the peak does not shrink to 1
but tends to (2/pi) Si(pi) = 1.17898..., an overshoot of about 9% of the jump.
At x = 0 every partial sum is 0, the average of the one-sided limits, as
Dirichlet's theorem predicts. Then Parseval's identity for the sawtooth
f(x) = x on (-pi, pi), whose sine coefficients are 2(-1)^(n+1)/n, gives
sum 1/n^2 = pi^2/6; we watch the partial sums close in, with error ~ 1/N.

Evidence: numerical (floating point, Simpson's rule for Si(pi)), with the
locations of the maxima and the Parseval formula derived exactly.
"""

import math

EXPERIMENT = {
    "id": "pde_intro_fourier_gibbs",
    "title": "Fourier series: Gibbs overshoot and Parseval's identity",
    "evidence": ["numerical"],
    "lessons": ["pde-intro"],
    "summary": (
        "Evaluates partial sums of the square-wave Fourier series at their "
        "first peak x = pi/(2n) and shows the peak tending to (2/pi) Si(pi) "
        "= 1.17898 instead of 1 (the Gibbs phenomenon), checks that the sums "
        "are 0 at the jump, and uses Parseval's identity for the sawtooth to "
        "approach sum 1/n^2 = pi^2/6 with error about 1/N. Numerical evidence."
    ),
    "packages": [],
}


def square_partial(x, n):
    """S_n(x) = (4/pi) * sum_{j=1..n} sin((2j-1)x)/(2j-1)."""
    return 4 / math.pi * sum(math.sin((2 * j - 1) * x) / (2 * j - 1)
                             for j in range(1, n + 1))


def first_peak(n):
    """Value of S_n at its first maximum to the right of 0, x = pi/(2n)."""
    return square_partial(math.pi / (2 * n), n)


def sine_integral(x, steps=2000):
    """Si(x) = integral of sin(t)/t from 0 to x, by Simpson's rule."""
    if steps % 2:
        raise ValueError("steps must be even")
    f = lambda t: 1.0 if t == 0 else math.sin(t) / t
    h = x / steps
    s = f(0) + f(x)
    s += 4 * sum(f((2 * i - 1) * h) for i in range(1, steps // 2 + 1))
    s += 2 * sum(f(2 * i * h) for i in range(1, steps // 2))
    return s * h / 3


def gibbs_limit():
    """(2/pi) Si(pi), the limit of the first peaks."""
    return 2 / math.pi * sine_integral(math.pi)


def sawtooth_coefficient(n):
    """b_n = (1/pi) * integral of x sin(nx) over (-pi, pi) = 2(-1)^(n+1)/n."""
    return 2 * (-1) ** (n + 1) / n


def parseval_partial(N):
    """(1/4) * sum_{n<=N} b_n^2, which Parseval says tends to pi^2/6."""
    return sum(sawtooth_coefficient(n) ** 2 for n in range(1, N + 1)) / 4


def main():
    g = gibbs_limit()
    print("Square wave sign(sin x): peak of S_n at x = pi/(2n)")
    print("     n      peak    S_n(0)   S_n(pi/2)")
    for n in [1, 5, 10, 50, 200, 1000]:
        print(f"{n:6d}   {first_peak(n):.5f}   {square_partial(0.0, n):+.1f}"
              f"   {square_partial(math.pi / 2, n):.5f}")
    print(f"limit (2/pi) Si(pi) = {g:.5f}: overshoot {100 * (g - 1) / 2:.2f}%"
          " of the jump")
    print("The peak moves towards the jump but never shrinks: the convergence")
    print("is pointwise, not uniform, near a discontinuity.")
    print()
    print("Parseval for f(x) = x on (-pi, pi): sum 1/n^2 = pi^2/6")
    print("      N    partial sum      error   N * error")
    for N in [10, 100, 1000, 10000]:
        err = math.pi ** 2 / 6 - parseval_partial(N)
        print(f"{N:7d}   {parseval_partial(N):.9f}   {err:.2e}   {N * err:.4f}")
    print()
    print("Epistemic status: numerical evidence. The peak locations and the")
    print("coefficients are derived exactly; the values are floating-point")
    print("and Si(pi) comes from Simpson's rule. Finitely many n cannot prove")
    print("the limits; the Gibbs constant and Parseval's identity are proved")
    print("in the lesson and its references.")


if __name__ == "__main__":
    main()
