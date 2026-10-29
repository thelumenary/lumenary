"""The logistic map x -> r x (1 - x): period doubling, Feigenbaum's constant and chaos.

For each growth rate r we iterate the map past its transient and detect the
period of the attractor. Then we locate the "superstable" parameters R_n at
which the critical point 1/2 lies on a cycle of period 2^n, by Newton's
method, and form the ratios (R_n - R_(n-1)) / (R_(n+1) - R_n), which approach
Feigenbaum's constant 4.669... Finally the Lyapunov exponent - the average of
log|f'(x_k)| along the orbit - is negative on stable cycles and equals log 2
at r = 4, where nearby orbits separate exponentially.
"""

import math

EXPERIMENT = {
    "id": "mathematical_biology_logistic_map",
    "title": "Logistic map: period doubling, Feigenbaum ratios and Lyapunov exponents",
    "evidence": ["numerical"],
    "lessons": ["mathematical-biology"],
    "summary": (
        "Iterates the logistic map to find attractor periods (1, 2, 4, 8, chaos, a "
        "period-3 window), computes superstable parameters by Newton's method and the "
        "ratios of their gaps, which approach Feigenbaum's constant 4.669, and estimates "
        "Lyapunov exponents, showing exponential divergence of nearby orbits at r = 4. "
        "Floating-point evidence about finitely many iterates."
    ),
    "packages": [],
}


def logistic(r, x):
    """One step of the logistic map."""
    return r * x * (1 - x)


def orbit(r, x0, n):
    """[x_0, ..., x_n] for the logistic map."""
    xs = [x0]
    for _ in range(n):
        xs.append(logistic(r, xs[-1]))
    return xs


def attractor_period(r, x0=0.2, transient=3000, max_period=64, tol=1e-9):
    """Smallest p <= max_period with x_(n+p) = x_n after the transient, else None."""
    x = x0
    for _ in range(transient):
        x = logistic(r, x)
    start = x
    for p in range(1, max_period + 1):
        x = logistic(r, x)
        if abs(x - start) < tol:
            return p
    return None


def superstable_gap(r, n):
    """f_r^(2^n)(1/2) - 1/2: zero exactly when 1/2 lies on a 2^n-cycle."""
    x = 0.5
    for _ in range(2 ** n):
        x = logistic(r, x)
    return x - 0.5


def superstable_parameters(count):
    """R_0 = 2, R_1 = 1 + sqrt 5, ... found by Newton's method with a numerical
    derivative, each started from an extrapolation of the previous gaps."""
    rs = [2.0, 1 + math.sqrt(5)]
    delta = 4.0
    while len(rs) < count:
        n = len(rs)
        r = rs[-1] + (rs[-1] - rs[-2]) / delta
        for _ in range(60):
            g = superstable_gap(r, n)
            h = 1e-10
            dg = (superstable_gap(r + h, n) - superstable_gap(r - h, n)) / (2 * h)
            step = g / dg
            r -= step
            if abs(step) < 1e-14:
                break
        rs.append(r)
        delta = (rs[-2] - rs[-3]) / (rs[-1] - rs[-2])
    return rs


def lyapunov(r, x0=0.2, transient=1000, n=20000):
    """Average of log|f_r'(x_k)| = log|r (1 - 2 x_k)| along the orbit."""
    x = x0
    for _ in range(transient):
        x = logistic(r, x)
    total = 0.0
    for _ in range(n):
        total += math.log(abs(r * (1 - 2 * x)) + 1e-300)
        x = logistic(r, x)
    return total / n


def main():
    print("Attractor period after 3000 iterations from x0 = 0.2:")
    for r in [2.8, 3.2, 3.5, 3.56, 3.7, 3.83]:
        p = attractor_period(r)
        print(f"  r = {r:<5} period {p if p else 'none found (chaotic?)'}")
    rs = superstable_parameters(8)
    print()
    print("Superstable parameters R_n and Feigenbaum ratios:")
    for n, r in enumerate(rs):
        line = f"  R_{n} = {r:.10f}"
        if n >= 2:
            ratio = (rs[n - 1] - rs[n - 2]) / (rs[n] - rs[n - 1])
            line += f"   ratio {ratio:.5f}"
        print(line)
    print("  (Feigenbaum's constant: 4.66920...)")
    print()
    print("Lyapunov exponents (negative: stable cycle; positive: chaos):")
    for r in [2.8, 3.2, 3.5, 3.7, 3.83, 4.0]:
        print(f"  r = {r:<5} {lyapunov(r):+.4f}")
    print(f"  log 2 = {math.log(2):.4f}")
    a, b = orbit(4.0, 0.3, 40), orbit(4.0, 0.3 + 1e-10, 40)
    gaps = [abs(x - y) for x, y in zip(a, b)]
    first = next(i for i, g in enumerate(gaps) if g > 0.1)
    print(f"At r = 4, starts 1e-10 apart differ by > 0.1 after {first} steps.")
    print()
    print("Epistemic status: floating-point iteration of finitely many steps.")
    print("Periods, ratios and exponents are numerical estimates; the")
    print("universality of Feigenbaum's constant was proved by Lanford (1982)")
    print("with computer assistance, and chaos at r = 4 is a theorem.")


if __name__ == "__main__":
    main()
