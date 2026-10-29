"""Gambler's ruin: first-step analysis solved exactly, then checked by simulation.

A gambler with i coins bets one coin at a time, winning with probability p,
until she has N coins or none. The probability h(i) of reaching N and the
expected duration m(i) satisfy linear "first-step" equations. We solve these
tridiagonal systems exactly with fractions, compare with the closed-form
answers from the lesson, and then simulate the game. A fair game (p = 1/2) and
a slightly unfavourable one (p = 18/38, betting on red in roulette) behave
very differently.
"""

import random
from fractions import Fraction

EXPERIMENT = {
    "id": "markov_chains_gamblers_ruin",
    "title": "Gambler's ruin: exact first-step analysis versus simulation",
    "evidence": ["exact", "statistical"],
    "lessons": ["markov-chains"],
    "summary": (
        "Solves the first-step equations for the probability of reaching N before 0 and "
        "for the expected duration exactly (fractions), confirms the closed forms i/N, "
        "(1 - r^i)/(1 - r^N) and i(N - i), and compares with 4,000 simulated games for "
        "a fair coin and for p = 18/38. Exact for the listed cases; the simulation is "
        "statistical evidence."
    ),
    "packages": [],
}


def solve_tridiagonal(lower, diag, upper, rhs):
    """Solve a tridiagonal system exactly (Thomas algorithm with Fractions)."""
    n = len(diag)
    c, d = [Fraction(0)] * n, [Fraction(0)] * n
    c[0] = Fraction(upper[0]) / diag[0] if n > 1 else Fraction(0)
    d[0] = Fraction(rhs[0]) / diag[0]
    for i in range(1, n):
        denom = diag[i] - lower[i] * c[i - 1]
        c[i] = Fraction(upper[i]) / denom if i < n - 1 else Fraction(0)
        d[i] = (rhs[i] - lower[i] * d[i - 1]) / denom
    x = [Fraction(0)] * n
    x[-1] = d[-1]
    for i in range(n - 2, -1, -1):
        x[i] = d[i] - c[i] * x[i + 1]
    return x


def first_step(p, n_target, durations=False):
    """Exact h(i) (or m(i)) for i = 0..N from the first-step equations.

    For 0 < i < N: h(i) = p h(i+1) + q h(i-1), with h(0) = 0, h(N) = 1;
    m(i) = 1 + p m(i+1) + q m(i-1), with m(0) = m(N) = 0.
    """
    p = Fraction(p)
    q = 1 - p
    k = n_target - 1  # unknowns at 1..N-1
    lower = [-q] * k
    diag = [Fraction(1)] * k
    upper = [-p] * k
    if durations:
        rhs = [Fraction(1)] * k
    else:
        rhs = [Fraction(0)] * k
        rhs[-1] = p  # the term p h(N) = p moved to the right-hand side
    inner = solve_tridiagonal(lower, diag, upper, rhs)
    boundary = Fraction(0) if durations else Fraction(1)
    return [Fraction(0)] + inner + [boundary]


def ruin_formula(p, i, n_target):
    """Closed form: i/N if p = 1/2, else (1 - r^i)/(1 - r^N) with r = q/p."""
    p = Fraction(p)
    if p == Fraction(1, 2):
        return Fraction(i, n_target)
    r = (1 - p) / p
    return (1 - r ** i) / (1 - r ** n_target)


def simulate(p, i, n_target, games, rng):
    """Fraction of games reaching N, and the mean number of bets."""
    wins = total = 0
    for _ in range(games):
        x, steps = i, 0
        while 0 < x < n_target:
            x += 1 if rng.random() < p else -1
            steps += 1
        wins += x == n_target
        total += steps
    return wins / games, total / games


def main():
    rng = random.Random(1654)
    n_target, start, games = 20, 10, 4000
    print(f"Start with {start} coins, stop at 0 or {n_target};"
          f" {games} simulated games each")
    for label, p in [("fair coin, p = 1/2", Fraction(1, 2)),
                     ("roulette red, p = 18/38", Fraction(18, 38))]:
        h = first_step(p, n_target)
        m = first_step(p, n_target, durations=True)
        assert h[start] == ruin_formula(p, start, n_target)
        sim_h, sim_m = simulate(float(p), start, n_target, games, rng)
        print(f"{label}:")
        print(f"  P(reach {n_target}): exact {float(h[start]):.4f}"
              f" (formula agrees), simulated {sim_h:.4f}")
        print(f"  expected bets:  exact {float(m[start]):.2f},"
              f" simulated {sim_m:.2f}")
    print()
    fair_m = first_step(Fraction(1, 2), n_target, durations=True)
    ok = all(fair_m[i] == i * (n_target - i) for i in range(n_target + 1))
    print(f"Fair game: m(i) = i (N - i) for every i = 0..{n_target}: {ok}")
    print("A house edge of 1/19 per bet cuts the chance of doubling 10 coins")
    print("from 1/2 to about 1/4.")
    print()
    print("Epistemic status: the first-step solutions are exact rational")
    print("numbers and agree with the closed forms for these parameters; the")
    print("simulated frequencies are statistical evidence (standard error")
    print("about 0.008 for the probabilities).")


if __name__ == "__main__":
    main()
