"""Zeros of the Riemann zeta function, and how they generate the primes.

We evaluate zeta(s) for complex s by Euler-Maclaurin summation (valid for all
s != 1, error far below 1e-10 in the range used), check it against
zeta(2) = pi^2/6, and locate the zeros on the critical line Re s = 1/2 as sign
changes of Hardy's real function Z(t) = exp(i theta(t)) zeta(1/2 + it),
refined by bisection. The first ten zeros are compared with the published
values (Odlyzko's tables), and their number with the Riemann-von Mangoldt
formula N(T) ~ (T/2 pi) log(T/2 pi) - T/2 pi + 7/8. Finally the explicit
formula of von Mangoldt,
    psi(x) = x - sum_rho x^rho / rho - log(2 pi) - log(1 - x^-2) / 2,
truncated to these ten pairs of zeros, is compared with the true psi(x):
each zero contributes a wave, and together they start to carve the staircase
of prime powers. Numerical evidence only: locating zeros on the line says
nothing about zeros off it, and the Riemann hypothesis remains open.
"""

import cmath
import math

EXPERIMENT = {
    "id": "analytic_number_theory_zeta_zeros",
    "title": "Zeros of zeta and the explicit formula",
    "evidence": ["numerical"],
    "lessons": ["analytic-number-theory"],
    "summary": (
        "Evaluates zeta(s) by Euler-Maclaurin summation, finds the first ten "
        "zeros on the critical line as sign changes of Hardy's Z-function, "
        "compares them with published values and with the Riemann-von "
        "Mangoldt count, and rebuilds psi(x) from those zeros with von "
        "Mangoldt's explicit formula. Numerical evidence; says nothing about "
        "zeros off the line."
    ),
    "packages": [],
}

#: Bernoulli numbers B_2, B_4, ..., B_16.
BERNOULLI = [1 / 6, -1 / 30, 1 / 42, -1 / 30, 5 / 66, -691 / 2730, 7 / 6,
             -3617 / 510]

#: First ten ordinates of zeros on the critical line (Odlyzko's tables).
KNOWN_ZEROS = [14.134725142, 21.022039639, 25.010857580, 30.424876126,
               32.935061588, 37.586178159, 40.918719012, 43.327073281,
               48.005150881, 49.773832478]


def zeta(s, n_terms=30):
    """Riemann zeta(s), s != 1, by Euler-Maclaurin summation."""
    s = complex(s)
    n = n_terms
    total = sum(k ** -s for k in range(1, n))
    total += n ** (1 - s) / (s - 1) + n ** -s / 2
    rising = s                      # s (s+1) ... (s + 2j - 2)
    fact = 2.0                      # (2j)!
    for j, b in enumerate(BERNOULLI, start=1):
        total += b / fact * rising * n ** (-s - 2 * j + 1)
        rising *= (s + 2 * j - 1) * (s + 2 * j)
        fact *= (2 * j + 1) * (2 * j + 2)
    return total


def theta(t):
    """Riemann-Siegel theta function, asymptotic series (accurate for t > 10)."""
    return (t / 2 * math.log(t / (2 * math.pi)) - t / 2 - math.pi / 8
            + 1 / (48 * t) + 7 / (5760 * t ** 3) + 31 / (80640 * t ** 5))


def hardy_z(t):
    """Hardy's Z(t) = exp(i theta(t)) zeta(1/2 + it), real for real t."""
    return (cmath.exp(1j * theta(t)) * zeta(0.5 + 1j * t)).real


def zeros_on_line(t_min, t_max, step=0.05):
    """Ordinates of sign changes of Z in [t_min, t_max], refined by bisection."""
    found = []
    t, z_old = t_min, hardy_z(t_min)
    while t < t_max:
        t_new = t + step
        z_new = hardy_z(t_new)
        if z_old * z_new < 0:
            lo, hi = t, t_new
            for _ in range(40):
                mid = (lo + hi) / 2
                if hardy_z(lo) * hardy_z(mid) <= 0:
                    hi = mid
                else:
                    lo = mid
            found.append((lo + hi) / 2)
        t, z_old = t_new, z_new
    return found


def riemann_von_mangoldt(T):
    """Main terms of N(T), the number of zeros with 0 < Im rho < T."""
    u = T / (2 * math.pi)
    return u * math.log(u) - u + 7 / 8


def psi_exact(x):
    """Chebyshev psi(x) = sum of log p over prime powers p^k <= x."""
    total = 0.0
    for p in range(2, int(x) + 1):
        if all(p % q for q in range(2, math.isqrt(p) + 1)):
            q = p
            while q <= x:
                total += math.log(p)
                q *= p
    return total


def psi_explicit(x, zeros):
    """von Mangoldt's explicit formula truncated to rho = 1/2 +- i gamma."""
    total = x - math.log(2 * math.pi) - 0.5 * math.log(1 - x ** -2)
    for g in zeros:
        rho = complex(0.5, g)
        total -= 2 * (x ** rho / rho).real
    return total


def main():
    z2 = zeta(2)
    print(f"zeta(2) = {z2.real:.12f}, pi^2/6 = {math.pi ** 2 / 6:.12f}")
    print(f"|zeta(1/2 + 14.134725i)| = {abs(zeta(0.5 + 14.134725j)):.1e}")
    zeros = zeros_on_line(10, 50)
    print(f"Zeros of Z(t) in 10 < t < 50: {len(zeros)} found")
    err = max(abs(a - b) for a, b in zip(zeros, KNOWN_ZEROS))
    for start in (0, 5):
        print("  " + "  ".join(f"{g:.6f}" for g in zeros[start:start + 5]))
    print(f"  largest difference from published values: {err:.1e}")
    print(f"  Riemann-von Mangoldt main term N(50) = "
          f"{riemann_von_mangoldt(50):.2f}")
    print("Explicit formula with these 10 pairs of zeros:")
    print(f"  {'x':>5} {'psi(x)':>8} {'from zeros':>11}")
    for x in (7.5, 10.5, 15.5, 20.5, 25.5, 30.5):
        print(f"  {x:>5} {psi_exact(x):>8.3f} {psi_explicit(x, zeros):>11.3f}")
    print()
    print("Epistemic status: numerical computation in double precision. It")
    print("finds zeros on the critical line in one window; it cannot rule out")
    print("zeros off the line, so it is evidence for, not a proof of, the")
    print("Riemann hypothesis, which is open.")


if __name__ == "__main__":
    main()
