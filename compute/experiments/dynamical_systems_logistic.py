"""The logistic map x -> r x (1 - x): periods, Feigenbaum's constant, chaos.

Three numerical experiments. (1) For several r we discard a long transient
and look for the period of the attractor. (2) The superstable parameters R_n,
where the attracting 2^n-cycle passes through the critical point x = 1/2,
solve f_r^(2^n)(1/2) = 1/2; we find them by Newton's method in r (the
derivative in r is computed alongside the orbit) and watch the ratios of
successive gaps approach Feigenbaum's delta = 4.6692... (3) The Lyapunov
exponent, the orbit average of ln |f_r'(x)|, is negative on periodic windows
and positive in chaos; at r = 4 its exact value is ln 2.

Evidence: numerical, in floating point. Periods and exponents are found for
finitely many iterates; Feigenbaum's constant is approached, not proved.
"""

import math

EXPERIMENT = {
    "id": "dynamical_systems_logistic",
    "title": "Logistic map: periods, Feigenbaum's delta and Lyapunov exponents",
    "evidence": ["numerical"],
    "lessons": ["dynamical-systems"],
    "summary": (
        "Iterates x -> r x (1 - x): detects attractor periods for several r, "
        "computes the superstable parameters of the period-doubling cascade by "
        "Newton's method and shows the gap ratios approaching Feigenbaum's "
        "delta = 4.669, and estimates Lyapunov exponents (exactly ln 2 at "
        "r = 4). Floating-point evidence over finitely many iterates."
    ),
    "packages": [],
}


def logistic(r, x):
    """One step of the logistic map."""
    return r * x * (1 - x)


def attractor_period(r, x0=0.2, transient=4000, max_period=64, tol=1e-7):
    """Smallest p <= max_period with |f^p(x) - x| < tol after the transient."""
    x = x0
    for _ in range(transient):
        x = logistic(r, x)
    y = x
    for p in range(1, max_period + 1):
        y = logistic(r, y)
        if abs(y - x) < tol:
            return p
    return None


def superstable_residual(r, n):
    """g(r) = f_r^(2^n)(1/2) - 1/2 and its derivative g'(r)."""
    x, dx = 0.5, 0.0
    for _ in range(2 ** n):
        x, dx = r * x * (1 - x), x * (1 - x) + r * (1 - 2 * x) * dx
    return x - 0.5, dx


def superstable_parameters(count):
    """R_0, ..., R_{count-1}: superstable 2^n-cycles, by Newton's method."""
    values = [2.0, 1 + math.sqrt(5)]
    ratio = 4.0
    while len(values) < count:
        n = len(values)
        r = values[-1] + (values[-1] - values[-2]) / ratio
        for _ in range(60):
            g, dg = superstable_residual(r, n)
            step = g / dg
            r -= step
            if abs(step) < 1e-15:
                break
        values.append(r)
        ratio = (values[-2] - values[-3]) / (values[-1] - values[-2])
    return values[:count]


def lyapunov_exponent(r, x0=0.2, transient=1000, n=20000):
    """Average of ln |f_r'(x_k)| = ln |r (1 - 2 x_k)| along the orbit."""
    x = x0
    for _ in range(transient):
        x = logistic(r, x)
    total = 0.0
    for _ in range(n):
        total += math.log(abs(r * (1 - 2 * x)) + 1e-300)
        x = logistic(r, x)
    return total / n


def main():
    print("1. Attractor periods (after 4000 transient steps)")
    for r in [2.8, 3.2, 3.5, 3.56, 3.83, 3.9]:
        p = attractor_period(r)
        print(f"   r = {r:4.2f}: period {p if p else 'none found up to 64'}")
    print()
    print("2. Superstable parameters R_n and Feigenbaum ratios")
    rs = superstable_parameters(9)
    for n, r in enumerate(rs):
        line = f"   R_{n} = {r:.10f}"
        if n >= 2:
            delta = (rs[n - 1] - rs[n - 2]) / (r - rs[n - 1])
            line += f"   ratio {delta:.5f}"
        print(line)
    print("   Feigenbaum's delta = 4.66920...")
    print()
    print("3. Lyapunov exponents (20000 iterates)")
    for r in [2.8, 3.2, 3.83, 3.9, 4.0]:
        print(f"   r = {r:4.2f}: {lyapunov_exponent(r):+.4f}")
    print(f"   exact value at r = 4: ln 2 = {math.log(2):.4f}")
    print()
    print("Epistemic status: numerical. Periods, parameters and exponents are")
    print("floating-point computations over finitely many iterates; that the")
    print("gap ratios converge to a universal delta is a theorem (Lanford's")
    print("computer-assisted proof, 1982; Lyubich, 1999), not something this")
    print("table proves.")


if __name__ == "__main__":
    main()
