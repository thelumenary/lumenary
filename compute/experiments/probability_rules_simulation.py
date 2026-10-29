"""Conditional probability as a relative frequency: simulated dice, doors, cards.

A conditional probability P(A | B) can be estimated by looking only at the
trials in which B happened and asking how often A happened too. A seeded
pseudo-random generator rolls two dice 60,000 times: "first die even" is
independent of "total 7", but "first die 6" is not independent of "total at
least 10", and two mutually exclusive events are as dependent as can be. The
Monty Hall game and drawing two cards without replacement show conditioning
changing a probability. Every estimate is printed next to its exact value.
"""

import random
from fractions import Fraction

EXPERIMENT = {
    "id": "probability_rules_simulation",
    "title": "Conditional probability by simulation: dice, doors and cards",
    "evidence": ["statistical", "exact"],
    "lessons": ["probability-rules"],
    "summary": (
        "Rolls two simulated dice 60,000 times (seeded) and estimates P(A), "
        "P(A | B) and P(A and B) for an independent pair, a dependent pair and "
        "a mutually exclusive pair, next to the exact values; plays 30,000 "
        "Monty Hall games (switching wins about 2/3 of the time) and draws two "
        "cards 60,000 times (P(second ace | first ace) = 3/51). Statistical "
        "evidence from one run, checked against exact probabilities."
    ),
    "packages": [],
}


def roll_pairs(rng, n):
    """n rolls of two fair dice, as (first, second) faces 1..6."""
    return [(rng.randint(1, 6), rng.randint(1, 6)) for _ in range(n)]


def estimate(trials, event, given=None):
    """Relative frequency of `event` among the trials where `given` holds."""
    pool = [t for t in trials if given is None or given(t)]
    return sum(1 for t in pool if event(t)) / len(pool)


def exact(event, given=None):
    """The exact probability over the 36 equally likely outcomes."""
    pool = [(a, b) for a in range(1, 7) for b in range(1, 7)
            if given is None or given((a, b))]
    return Fraction(sum(1 for t in pool if event(t)), len(pool))


def monty_hall(rng, games):
    """Win rates (stick, switch) when the host always opens a goat door."""
    stick = switch = 0
    for _ in range(games):
        car, pick = rng.randrange(3), rng.randrange(3)
        opened = rng.choice([d for d in range(3) if d not in (car, pick)])
        other = next(d for d in range(3) if d not in (pick, opened))
        stick += pick == car
        switch += other == car
    return stick / games, switch / games


def second_ace_given_first(rng, draws):
    """Estimate P(second card is an ace | first is an ace), no replacement."""
    deck = ["A"] * 4 + ["x"] * 48
    both = first = 0
    for _ in range(draws):
        c1, c2 = rng.sample(deck, 2)
        first += c1 == "A"
        both += c1 == "A" and c2 == "A"
    return both / first


def main():
    rng = random.Random(1654)
    rolls = roll_pairs(rng, 60000)
    pairs = [
        ("first even | total 7", lambda t: t[0] % 2 == 0,
         lambda t: t[0] + t[1] == 7),
        ("first is 6 | total >= 10", lambda t: t[0] == 6,
         lambda t: t[0] + t[1] >= 10),
        ("first is 1 | first is 6", lambda t: t[0] == 1, lambda t: t[0] == 6),
    ]
    print("60,000 rolls of two dice      P(A)            P(A | B)")
    print("                              sim    exact    sim    exact")
    for name, a, b in pairs:
        line = (f"  {name:26} {estimate(rolls, a):.3f}  {str(exact(a)):5}    "
                f"{estimate(rolls, a, b):.3f}  {exact(a, b)}")
        print(line)
    print("Independent: P(A | B) = P(A). Not independent: knowing B")
    print("changes the chance of A (to 1/2 in row 2, to 0 in row 3).")
    print()
    stick, switch = monty_hall(rng, 30000)
    print(f"Monty Hall, 30,000 games: stick wins {stick:.3f} (exact 1/3), "
          f"switch {switch:.3f} (2/3)")
    est = second_ace_given_first(rng, 60000)
    print(f"Two cards, 60,000 draws: P(2nd ace | 1st ace) = {est:.3f}")
    print(f"  (exact 3/51 = {3 / 51:.3f}, while P(ace) = 4/52 = "
          f"{4 / 52:.3f})")
    print()
    print("Epistemic status: statistical evidence from one seeded run of a")
    print("pseudo-random generator; another seed gives slightly different")
    print("estimates. The exact values come from counting equally likely")
    print("outcomes, and the lesson proves the rules that connect them.")


if __name__ == "__main__":
    main()
