"""Where Ito's extra term comes from: Riemann sums along one Brownian path.

We sample one Brownian path on [0, 1] at 2^16 equally spaced times (seeded
Gaussian increments) and evaluate, for coarser partitions, the left-point
sum (Ito), the average of the endpoint values (Stratonovich), the quadratic
variation and the total variation. The left sums approach (B_1^2 - 1)/2,
the trapezoidal sums equal B_1^2/2 exactly, the quadratic variation tends to
1 = t, and the total variation grows without bound like sqrt(2n/pi).
"""

import math
import random

EXPERIMENT = {
    "id": "stochastic_processes_ito_sums",
    "title": "Ito versus Stratonovich sums along a Brownian path",
    "evidence": ["numerical", "statistical"],
    "lessons": ["stochastic-processes"],
    "summary": (
        "Samples one seeded Brownian path at 2^16 points and computes left-point "
        "(Ito) and trapezoidal (Stratonovich) sums of B dB, quadratic variation "
        "and total variation on dyadic partitions. The Ito sums approach "
        "(B_1^2 - 1)/2, the Stratonovich sums equal B_1^2/2, the quadratic "
        "variation approaches 1 and the total variation diverges. One path, "
        "finitely many partitions: illustration, not proof."
    ),
    "packages": [],
}


def brownian_path(levels, rng):
    """B at times k / 2^levels, k = 0..2^levels, from Gaussian increments."""
    n = 2 ** levels
    sd = math.sqrt(1.0 / n)
    path = [0.0]
    for _ in range(n):
        path.append(path[-1] + rng.gauss(0.0, sd))
    return path


def subsample(path, step):
    """Every step-th value of the path (a coarser partition)."""
    return path[::step]


def ito_sum(path):
    """Left-point sum of B dB: sum of B_k (B_(k+1) - B_k)."""
    return math.fsum(a * (b - a) for a, b in zip(path, path[1:]))


def stratonovich_sum(path):
    """Trapezoidal sum: sum of (B_k + B_(k+1))/2 * (B_(k+1) - B_k)."""
    return math.fsum((a + b) / 2 * (b - a) for a, b in zip(path, path[1:]))


def quadratic_variation(path):
    """Sum of squared increments."""
    return math.fsum((b - a) ** 2 for a, b in zip(path, path[1:]))


def total_variation(path):
    """Sum of absolute increments."""
    return math.fsum(abs(b - a) for a, b in zip(path, path[1:]))


def main():
    levels = 16
    path = brownian_path(levels, random.Random(1944))
    b1 = path[-1]
    print(f"One Brownian path on [0, 1]; B_1 = {b1:.5f}")
    print(f"Targets: (B_1^2 - 1)/2 = {(b1 * b1 - 1) / 2:.5f},"
          f" B_1^2/2 = {b1 * b1 / 2:.5f}")
    print("      n     Ito sum   Stratonovich   quad. var.   total var.")
    for m in [2, 4, 6, 8, 10, 12, 14, 16]:
        p = subsample(path, 2 ** (levels - m))
        print(f"  {2 ** m:>5}   {ito_sum(p):>9.5f}   {stratonovich_sum(p):>10.5f}"
              f"   {quadratic_variation(p):>9.5f}   {total_variation(p):>9.2f}")
    p = path
    gap = stratonovich_sum(p) - ito_sum(p) - quadratic_variation(p) / 2
    print(f"Stratonovich - Ito - QV/2 on the finest grid: {gap:.1e}")
    print(f"sqrt(2n/pi) for n = 2^16: {math.sqrt(2 * 2 ** 16 / math.pi):.2f}")
    print("The Stratonovich sum telescopes to B_1^2/2 on every partition; the")
    print("Ito sum differs from it by half the quadratic variation, which")
    print("tends to t = 1. Unbounded total variation is why no ordinary")
    print("(Riemann-Stieltjes) integral against B exists.")
    print()
    print("Epistemic status: floating-point computation on a single seeded")
    print("pseudo-random path and finitely many partitions. The identities")
    print("between the sums are exact algebra (formalised in Lean); the limits")
    print("are theorems (quadratic variation of Brownian motion), illustrated")
    print("here, not proved.")


if __name__ == "__main__":
    main()
