"""Gibbs overshoot, Fejer's cure and Parseval, for the square wave.

The square wave f = sign(sin x) has Fourier series (4/pi) sum over odd k of
sin(k x)/k. Its partial sums S_N overshoot the jump at 0 by about 9% of the
jump however large N is (the Gibbs phenomenon, limit (2/pi) Si(pi)). The
Fejer means (averages of S_0, ..., S_N) never exceed 1, because the Fejer
kernel is a positive approximate identity. Parseval's identity gives the
exact L^2 error of S_N and the sum 1 + 1/9 + 1/25 + ... = pi^2/8.
"""

import math

import numpy as np

EXPERIMENT = {
    "id": "harmonic_analysis_gibbs_fejer",
    "title": "Gibbs overshoot, Fejer means and Parseval",
    "evidence": ["numerical"],
    "lessons": ["harmonic-analysis"],
    "summary": (
        "Samples the Fourier partial sums S_N of the square wave near its jump: "
        "the maximum stays near (2/pi) Si(pi) = 1.17898 as N grows, an overshoot "
        "of about 9% of the jump. The Fejer means stay below 1. Parseval gives "
        "the L^2 error of S_N, and the sum of 1/k^2 over odd k tends to pi^2/8. "
        "Sampled maxima for finitely many N: evidence, with the limits proved in "
        "the lesson."
    ),
    "packages": ["numpy"],
}


def partial_sum(n, x):
    """S_n(x) for the square wave: (4/pi) * sum of sin(kx)/k, odd k <= n."""
    x = np.asarray(x, dtype=float)
    total = np.zeros_like(x)
    for k in range(1, n + 1, 2):
        total += np.sin(k * x) / k
    return 4 / math.pi * total


def fejer_mean(n, x):
    """sigma_n(x) = (S_0 + S_1 + ... + S_n)(x) / (n + 1)."""
    x = np.asarray(x, dtype=float)
    current = np.zeros_like(x)
    total = np.zeros_like(x)
    for m in range(n + 1):
        if m % 2 == 1:
            current = current + 4 / math.pi * np.sin(m * x) / m
        total += current
    return total / (n + 1)


def sine_integral(t, steps=2000):
    """Si(t) = integral of sin(u)/u from 0 to t, by Simpson's rule."""
    if steps % 2:
        steps += 1
    h = t / steps
    def g(u):
        return 1.0 if u == 0 else math.sin(u) / u
    s = g(0) + g(t)
    s += sum((4 if i % 2 else 2) * g(i * h) for i in range(1, steps))
    return s * h / 3


def l2_error_squared(n):
    """(1/pi) * integral of (f - S_n)^2 over (-pi, pi), by Parseval:
    2 minus the sum of (4/(pi k))^2 over odd k <= n."""
    return 2 - sum((4 / (math.pi * k)) ** 2 for k in range(1, n + 1, 2))


def odd_reciprocal_squares(n):
    """1 + 1/9 + 1/25 + ... over odd k <= n."""
    return sum(1 / k ** 2 for k in range(1, n + 1, 2))


def main():
    grid = np.linspace(1e-6, math.pi / 2, 20001)
    gibbs = 2 / math.pi * sine_integral(math.pi)
    print("Square wave sign(sin x): jump of size 2 at x = 0")
    print(f"Gibbs limit (2/pi) Si(pi) = {gibbs:.6f}")
    print(f"{'N':>5} {'max S_N':>10} {'overshoot/jump':>15} {'max Fejer':>10}")
    for n in [9, 49, 199, 999]:
        top = float(np.max(partial_sum(n, grid)))
        fej = float(np.max(fejer_mean(n, grid)))
        print(f"{n:>5} {top:>10.6f} {(top - 1) / 2:>15.4f} {fej:>10.6f}")
    print("The overshoot does not shrink; it moves towards the jump.")
    print("The Fejer means stay below sup |f| = 1 (positive kernel).")
    print()
    print("Parseval: L^2 error of S_N, and sum over odd k of 1/k^2")
    for n in [1, 9, 99, 999]:
        print(f"  N = {n:>3}: error^2 = {l2_error_squared(n):.6f},"
              f" partial sum = {odd_reciprocal_squares(n):.6f}")
    print(f"  pi^2/8 = {math.pi ** 2 / 8:.6f}")
    print()
    print("Epistemic status: numerical evidence. Maxima are sampled on a grid of")
    print("20001 points and Si(pi) is computed by Simpson's rule; finitely many N")
    print("are shown. That the overshoot tends to (2/pi) Si(pi) - 1 and that")
    print("Fejer means of continuous functions converge uniformly are theorems")
    print("proved in the lesson, not consequences of this table.")


if __name__ == "__main__":
    main()
