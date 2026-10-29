"""Complex tori and the j-invariant.

Every complex torus is C / (Z + tau Z) with tau in the upper half-plane, and
two tori are biholomorphic exactly when their tau's differ by an element of
SL(2, Z) acting by Mobius transformations. The j-invariant is a complete
invariant. We compute j(tau) = 1728 E4^3 / (E4^3 - E6^2) from the
q-expansions of the Eisenstein series (q = exp(2 pi i tau)), check that
j(tau + 1) = j(-1/tau) = j(tau), compute j(i) = 1728 and j(exp(2 pi i/3)) = 0,
reduce points to the standard fundamental domain, and show that tori of the
same shape but different size have the same j while the square and the
hexagonal tori are different. Numerical evidence from truncated series.
"""

import cmath
import math

EXPERIMENT = {
    "id": "riemann_surfaces_tori",
    "title": "Complex tori, the modular group and the j-invariant",
    "evidence": ["numerical"],
    "lessons": ["riemann-surfaces"],
    "summary": (
        "Computes the j-invariant of the torus C/(Z + tau Z) from q-expansions of "
        "Eisenstein series, checks its invariance under tau -> tau + 1 and "
        "tau -> -1/tau, evaluates j(i) = 1728 and j(rho) = 0, and reduces points "
        "of the upper half-plane to the fundamental domain of SL(2, Z): tori form "
        "a one-complex-parameter family. Numerical evidence (truncated series)."
    ),
    "packages": [],
}


def sigma(k, n):
    """Sum of the k-th powers of the divisors of n."""
    return sum(d**k for d in range(1, n + 1) if n % d == 0)


def eisenstein(tau, terms=60):
    """(E4, E6) at tau via E4 = 1 + 240 sum s3(n) q^n, E6 = 1 - 504 sum s5(n) q^n."""
    q = cmath.exp(2j * math.pi * tau)
    e4, e6, qn = 1 + 0j, 1 + 0j, 1 + 0j
    for n in range(1, terms + 1):
        qn *= q
        e4 += 240 * sigma(3, n) * qn
        e6 -= 504 * sigma(5, n) * qn
    return e4, e6


def j_invariant(tau, terms=60):
    """j(tau) = 1728 E4^3 / (E4^3 - E6^2)."""
    e4, e6 = eisenstein(tau, terms)
    return 1728 * e4**3 / (e4**3 - e6**2)


def reduce_to_fundamental_domain(tau, max_steps=100):
    """Apply T: tau -> tau + n and S: tau -> -1/tau until |Re| <= 1/2, |tau| >= 1."""
    steps = []
    for _ in range(max_steps):
        n = round(tau.real)
        if n:
            tau -= n
            steps.append(f"T^{-n}")
        if abs(tau) < 1 - 1e-12:
            tau = -1 / tau
            steps.append("S")
        else:
            return tau, steps
    raise RuntimeError("did not converge")


def lattice_tau(w1, w2):
    """The tau of the lattice Z w1 + Z w2, normalised to the upper half-plane."""
    tau = w2 / w1
    return tau if tau.imag > 0 else -tau


def main():
    i = 1j
    rho = cmath.exp(2j * math.pi / 3)
    print(f"j(i)       = {j_invariant(i).real:12.4f}   (square torus; exact 1728)")
    print(f"j(rho)     = {abs(j_invariant(rho + 1)):12.4e}   (hexagonal torus; exact 0)")
    tau = 0.3 + 1.1j
    print(f"j(tau)     = {j_invariant(tau):.6f}   for tau = 0.3 + 1.1i")
    print(f"j(tau + 1) = {j_invariant(tau + 1):.6f}")
    print(f"j(-1/tau)  = {j_invariant(-1 / tau, terms=120):.6f}")
    print()
    print("Reducing tau to the fundamental domain |Re tau| <= 1/2, |tau| >= 1:")
    for start in [3.7 + 0.2j, -0.45 + 0.05j, 0.1 + 0.6j]:
        end, steps = reduce_to_fundamental_domain(start)
        moves = " ".join(steps) if steps else "(already reduced)"
        x, y = round(end.real, 4) + 0.0, round(end.imag, 4)
        print(f"  {start}: {moves} -> {x:+.4f}{y:+.4f}i")
        print(f"     j before {j_invariant(start, 400):.2f}")
        print(f"     j after  {j_invariant(end):.2f}")
    print()
    t1 = lattice_tau(1 + 0j, 1j)
    t2 = lattice_tau(2 + 2j, -2 + 2j)
    print("Same shape, different size: lattices Z + iZ and (2+2i)Z + (-2+2i)Z")
    print(f"  j = {j_invariant(t1).real:.4f} and {j_invariant(t2).real:.4f}")
    print()
    print("Epistemic status: floating-point evaluation of truncated q-series, so")
    print("evidence only. The invariance of j under SL(2, Z) and the fact that j")
    print("classifies tori up to biholomorphism are theorems (see the lesson).")


if __name__ == "__main__":
    main()
