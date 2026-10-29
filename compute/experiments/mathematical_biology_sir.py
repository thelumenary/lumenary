"""The SIR epidemic: numerical solution versus the final-size relation.

We solve S' = -beta S I, I' = beta S I - gamma I, R' = gamma I (fractions of a
population, N = 1) with the classical Runge-Kutta method, starting from one
infected person in ten thousand. We compare the simulated final size and peak
with the exact predictions of the lesson: the final susceptible fraction s
solves s = exp(-R0 (1 - s)), and the peak prevalence is
1 - (1 + ln R0)/R0. We also check that the invariant S + I - (1/R0) ln S stays
constant along the numerical solution.
"""

import math

EXPERIMENT = {
    "id": "mathematical_biology_sir",
    "title": "SIR epidemics: Runge-Kutta solutions and the final-size relation",
    "evidence": ["numerical"],
    "lessons": ["mathematical-biology"],
    "summary": (
        "Integrates the SIR model with RK4 for several values of R0 and compares the "
        "simulated attack rate and peak with the final-size relation s = exp(-R0(1 - s)) "
        "and the peak formula 1 - (1 + ln R0)/R0, tracks the conserved quantity "
        "S + I - ln(S)/R0, and contrasts the attack rate with the herd immunity threshold "
        "1 - 1/R0 (overshoot). Numerical evidence for one model."
    ),
    "packages": [],
}


def sir_rhs(state, beta, gamma):
    """Right-hand side of the SIR equations (population fractions)."""
    s, i, r = state
    infection = beta * s * i
    return (-infection, infection - gamma * i, gamma * i)


def rk4_step(state, h, beta, gamma):
    """One classical Runge-Kutta step."""
    def shift(base, k, c):
        return tuple(b + c * x for b, x in zip(base, k))
    k1 = sir_rhs(state, beta, gamma)
    k2 = sir_rhs(shift(state, k1, h / 2), beta, gamma)
    k3 = sir_rhs(shift(state, k2, h / 2), beta, gamma)
    k4 = sir_rhs(shift(state, k3, h), beta, gamma)
    return tuple(x + h / 6 * (a + 2 * b + 2 * c + d)
                 for x, a, b, c, d in zip(state, k1, k2, k3, k4))


def simulate(r0, gamma=0.1, i0=1e-4, h=0.5, days=1500):
    """Return (final S, peak I, day of peak, max drift of the invariant)."""
    beta = r0 * gamma
    state = (1 - i0, i0, 0.0)

    def invariant(st):
        return st[0] + st[1] - math.log(st[0]) / r0

    v0 = invariant(state)
    peak, peak_day, drift = state[1], 0.0, 0.0
    for step in range(1, int(days / h) + 1):
        state = rk4_step(state, h, beta, gamma)
        if state[1] > peak:
            peak, peak_day = state[1], step * h
        drift = max(drift, abs(invariant(state) - v0))
    return state[0], peak, peak_day, drift


def final_size(r0, s0=1.0, tol=1e-15):
    """Root s in (0, 1) of s = s0 exp(-R0 (1 - s)) for R0 > 1, by Newton's method."""
    s = 0.5 / r0
    for _ in range(100):
        g = s - s0 * math.exp(-r0 * (1 - s))
        dg = 1 - r0 * s0 * math.exp(-r0 * (1 - s))
        step = g / dg
        s -= step
        if abs(step) < tol:
            break
    return s


def peak_prevalence(r0):
    """Peak infected fraction 1 - (1 + ln R0)/R0 (for S(0) = 1, I(0) = 0+)."""
    return 1 - (1 + math.log(r0)) / r0


def main():
    print("SIR with gamma = 0.1/day, I(0) = 1e-4, RK4 with step 0.5 days")
    print("  R0 | attack rate: RK4  final-size | peak I: RK4 formula | day"
          " | herd 1-1/R0")
    for r0 in [1.5, 2.0, 3.0, 5.0]:
        s_end, peak, day, drift = simulate(r0)
        s_inf = final_size(r0)
        print(f" {r0:>3} |        {1 - s_end:.4f}    {1 - s_inf:.4f} |"
              f"  {peak:.4f}  {peak_prevalence(r0):.4f} | {day:>3.0f} |"
              f"   {1 - 1 / r0:.3f}")
    print()
    _, _, _, drift = simulate(3.0)
    print(f"Largest drift of S + I - ln(S)/R0 along the R0 = 3 run: {drift:.1e}")
    print("Attack rates exceed the herd immunity threshold: the epidemic")
    print("overshoots, because infections continue after S/N falls below 1/R0.")
    print("Small differences from the formulas come from I(0) > 0.")
    print()
    print("Epistemic status: numerical solution (RK4) of one deterministic model")
    print("with chosen parameters, compared with exact relations derived in the")
    print("lesson. It says nothing about whether real epidemics follow the SIR")
    print("assumptions (homogeneous mixing, fixed parameters, lasting immunity).")


if __name__ == "__main__":
    main()
