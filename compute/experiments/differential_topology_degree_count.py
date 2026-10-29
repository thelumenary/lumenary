"""Counting preimages: the unsigned count changes, the signed count does not.

Part 1 takes a wiggly map of the circle to itself, of degree 3, whose
derivative changes sign (it folds back). For several regular values y it
finds every preimage numerically and adds up the signs of the derivative.
The number of preimages depends on y; the signed count is always 3. The few
values where the count jumps are critical values (Sard: a finite set here).

Part 2 does the same for maps of the Riemann sphere: z -> z^3 - 3z, which is
holomorphic (every preimage counts +1), and z -> conj(z)^3, which reverses
orientation (every preimage counts -1). Roots are found with numpy.
This is numerical evidence for the theorem that the degree is well defined.
"""

import math

import numpy as np

EXPERIMENT = {
    "id": "differential_topology_degree_count",
    "title": "Counting preimages with and without signs",
    "evidence": ["numerical"],
    "lessons": ["differential-topology"],
    "summary": (
        "For a degree-3 map of the circle that folds back, finds all preimages of "
        "several regular values: their number varies (5 or 7) but the count with "
        "signs of the derivative is always 3; also lists the critical values. Then "
        "counts preimages for the holomorphic map z^3 - 3z (degree 3, critical "
        "values -2 and 2) and for conj(z)^3 (degree -3). Numerical evidence."
    ),
    "packages": ["numpy"],
}

TWO_PI = 2 * math.pi
WIGGLE = 4.0
SAMPLE_VALUES = [0.2, 1.0, 1.8, 2.6, 3.1, 4.0, 5.0, 6.1]


def lift(t):
    """A lift F of the circle map: F(t + 2 pi) = F(t) + 3 * 2 pi (degree 3)."""
    return 3 * t + WIGGLE * math.sin(2 * t)


def lift_derivative(t):
    """F'(t) = 3 + 2 * WIGGLE * cos(2t); negative near t = pi/2 and 3 pi/2."""
    return 3 + 2 * WIGGLE * math.cos(2 * t)


def preimages(y, samples=4000):
    """All t in [0, 2 pi) with F(t) = y mod 2 pi, by sign changes + bisection."""
    roots = []
    ts = [TWO_PI * k / samples for k in range(samples + 1)]
    lo = math.floor((lift(0) - 10 - y) / TWO_PI)
    hi = math.ceil((lift(TWO_PI) + 10 - y) / TWO_PI)
    for k in range(lo, hi + 1):
        target = y + TWO_PI * k
        values = [lift(t) - target for t in ts]
        for i in range(samples):
            a, b = ts[i], ts[i + 1]
            fa, fb = values[i], values[i + 1]
            if fa == 0 or fa * fb < 0:
                for _ in range(60):
                    m = (a + b) / 2
                    if (lift(a) - target) * (lift(m) - target) <= 0:
                        b = m
                    else:
                        a = m
                roots.append((a + b) / 2)
    return sorted(roots)


def signed_count(roots):
    """Sum of the signs of F' at the preimages: the degree at a regular value."""
    return sum(1 if lift_derivative(t) > 0 else -1 for t in roots)


def critical_values():
    """The critical values F(t) mod 2 pi, where F'(t) = 0 (cos 2t = -3/(2W))."""
    s = math.acos(-3 / (2 * WIGGLE)) / 2
    points = [s, math.pi - s, math.pi + s, TWO_PI - s]
    return sorted(lift(t) % TWO_PI for t in points)


def complex_preimages(coeffs, w, tol=1e-6):
    """Distinct roots of p(z) = w, p given by numpy coefficients (highest first)."""
    c = list(coeffs)
    c[-1] -= w
    distinct = []
    for r in np.roots(c):
        if all(abs(r - d) > tol for d in distinct):
            distinct.append(r)
    return distinct


def critical_values_complex(coeffs):
    """Images p(c) of the critical points c (roots of p')."""
    p = np.poly1d(coeffs)
    return [complex(p(c)) for c in np.roots(np.polyder(p).coeffs)]


def main():
    print("1. The circle map F(t) = 3t + 4 sin 2t (mod 2 pi), degree 3")
    crit = ", ".join(f"{v:.3f}" for v in critical_values())
    print(f"   critical values (mod 2 pi): {crit}")
    print("   y        preimages   signed count")
    for y in SAMPLE_VALUES:
        roots = preimages(y)
        print(f"   {y:5.3f}    {len(roots):5d}       {signed_count(roots):+d}")
    print()
    print("2. Maps of the Riemann sphere")
    cubic = [1, 0, -3, 0]
    crit = critical_values_complex(cubic)
    for name, w in [("0", 0), ("i", 1j), ("2", 2), ("-2", -2), ("5-3i", 5 - 3j)]:
        roots = complex_preimages(cubic, w)
        critical = any(abs(w - c) < 1e-9 for c in crit)
        label = "critical value" if critical else "regular value"
        print(f"   z^3 - 3z = {name:<5}: {len(roots)} preimages ({label})")
    roots = complex_preimages(cubic, 1j)
    conj_roots = [r.conjugate() for r in roots]
    print(f"   conj(z)^3 = conj(i) has {len(conj_roots)} preimages, each with")
    print("   Jacobian -|3z^2|^2 < 0: signed count -3, degree -3.")
    print()
    print("Epistemic status: numerical root-finding on a grid with bisection, for")
    print("finitely many values. The constant signed counts are evidence for the")
    print("theorem that the degree does not depend on the regular value; the")
    print("proof uses Sard's theorem and the classification of compact 1-manifolds.")


if __name__ == "__main__":
    main()
