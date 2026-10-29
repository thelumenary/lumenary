"""How much does it tell you when several checkers agree?

A toy model. A proof is correct with prior probability `prior`. Each of k
checkers (people, programs or AI systems) always accepts a correct proof and
accepts a flawed proof with probability q. With probability rho the checkers
share a blind spot and return one common verdict; otherwise they judge
independently. Then all k accept a flawed proof with probability
rho*q + (1 - rho)*q^k, and Bayes' rule gives the probability that the proof is
correct after k acceptances.

We compute this exactly (with fractions) for independent checkers (rho = 0)
and correlated ones (rho = 1/2), show the ceiling that correlated agreement
can never exceed, and confirm the formula by a seeded simulation of the model.
The Lean module proves the ceiling and the limit for independent checkers.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from fractions import Fraction
import random
import textwrap

EXPERIMENT = {
    "id": "research_ethics_agreement",
    "title": "When checkers agree: independent versus correlated errors",
    "evidence": ["exact", "statistical"],
    "lessons": ["research-ethics"],
    "summary": (
        "Computes exactly, in a toy Bayesian model, the probability that a proof is "
        "correct after k checkers accept it, for independent and for correlated "
        "checkers, shows the ceiling that correlated agreement never exceeds, and "
        "confirms the formula by a seeded simulation. It illustrates why agreement "
        "is no substitute for checking; real checkers do not follow this model."
    ),
    "packages": [],
}


def accept_flawed(q, rho, k):
    """Probability that all k checkers accept a flawed proof."""
    return rho * q + (1 - rho) * q ** k


def posterior(prior, q, rho, k):
    """Probability that the proof is correct, given k acceptances."""
    return prior / (prior + (1 - prior) * accept_flawed(q, rho, k))


def ceiling(prior, q, rho):
    """The limit of the posterior as k grows, for 0 <= q < 1."""
    return prior / (prior + (1 - prior) * rho * q)


def simulate(prior, q, rho, k, trials, seed=2024):
    """Monte Carlo estimate of P(correct | all k accept) in the model."""
    rng = random.Random(seed)
    accepted = correct_and_accepted = 0
    for _ in range(trials):
        correct = rng.random() < prior
        if correct:
            all_accept = True
        elif rng.random() < rho:
            all_accept = rng.random() < q
        else:
            all_accept = all(rng.random() < q for _ in range(k))
        if all_accept:
            accepted += 1
            correct_and_accepted += correct
    return correct_and_accepted / accepted, accepted


def main():
    prior, q = Fraction(1, 2), Fraction(3, 5)
    print(f"Prior P(correct) = {prior}; a flawed proof fools one checker "
          f"with probability {q}")
    print()
    print("  k   independent (rho = 0)   correlated (rho = 1/2)")
    for k in [1, 2, 3, 5, 10, 20]:
        ind = posterior(prior, q, 0, k)
        cor = posterior(prior, q, Fraction(1, 2), k)
        print(f"{k:>3}   {float(ind):>21.5f}   {float(cor):>22.5f}")
    cap = ceiling(prior, q, Fraction(1, 2))
    print(f"Ceiling for rho = 1/2: {cap} = {float(cap):.5f}, never exceeded")
    print()
    estimate, n = simulate(0.5, 0.6, 0.5, 10, 40000)
    exact = float(posterior(prior, q, Fraction(1, 2), 10))
    half_width = 1.96 * (estimate * (1 - estimate) / n) ** 0.5
    print(f"Simulation, rho = 1/2, k = 10: {estimate:.4f} +/- {half_width:.4f}"
          f" from {n} accepted runs")
    print(f"Exact value from the formula:   {exact:.4f}")
    print()
    print(textwrap.fill(
        "Epistemic status: the table is exact arithmetic in a toy model and the "
        "simulation is statistical evidence that the formula describes the "
        "model. The model is an illustration, not a description of real "
        "reviewers or AI systems, whose errors are correlated in unknown ways. "
        "Its lesson is qualitative: agreement is evidence only to the extent "
        "that the checkers' errors are independent, and it is never a proof.",
        width=78,
    ))


if __name__ == "__main__":
    main()
