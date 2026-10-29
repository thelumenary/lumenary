"""The twin paradox with exact arithmetic.

Speeds such as 3/5, 4/5, 5/13 and 12/13 (from Pythagorean triples) have
rational Lorentz factors, so proper times can be computed exactly with
fractions. A twin who travels out and back at speed v for a total Earth time
T ages T/gamma. We check the reverse triangle inequality
tau(v) + tau(w) <= tau(v + w) on many rational timelike vectors (comparing
squares exactly, so no square roots are needed), compose velocities with
the relativistic addition law and confirm gamma(u (+) v) = gamma(u) gamma(v)
(1 + u v).
"""

import math
import random
from fractions import Fraction

EXPERIMENT = {
    "id": "relativity_twin_paradox",
    "title": "The twin paradox and velocity addition, exactly",
    "evidence": ["exact"],
    "lessons": ["relativity"],
    "summary": (
        "Computes with exact fractions the proper time of twins travelling at "
        "speeds with rational Lorentz factors (3/5, 4/5, 5/13, 12/13, 20/29), "
        "checks the reverse triangle inequality for 2000 seeded pairs of "
        "rational future timelike vectors in 1+3 dimensions by comparing exact "
        "squares, and verifies velocity addition identities exactly. Finite "
        "exact checks of theorems proved in the lesson."
    ),
    "packages": [],
}


def gamma_rational(v):
    """Exact Lorentz factor 1/sqrt(1 - v^2) when it is rational, else None."""
    v = Fraction(v)
    if not -1 < v < 1:
        raise ValueError("need |v| < 1")
    q = 1 - v * v
    num, den = q.numerator, q.denominator
    rn, rd = math.isqrt(num), math.isqrt(den)
    if rn * rn == num and rd * rd == den:
        return Fraction(rd, rn)
    return None


def interval_sq(t, xs):
    """Proper time squared t^2 - |x|^2 of the vector (t, x)."""
    return t * t - sum(x * x for x in xs)


def reverse_triangle_holds(v, w):
    """Exact check of tau(v) + tau(w) <= tau(v + w) for future timelike v, w.

    With a = tau(v)^2, b = tau(w)^2, c = tau(v + w)^2 the claim is
    sqrt(a) + sqrt(b) <= sqrt(c), i.e. c - a - b >= 0 and (c - a - b)^2 >= 4ab.
    """
    a, b = interval_sq(*v), interval_sq(*w)
    s = (v[0] + w[0], [p + q for p, q in zip(v[1], w[1])])
    c = interval_sq(*s)
    d = c - a - b
    return d >= 0 and d * d >= 4 * a * b


def add_velocities(u, v):
    """Relativistic velocity addition (u + v) / (1 + u v)."""
    return (Fraction(u) + Fraction(v)) / (1 + Fraction(u) * Fraction(v))


def random_future_timelike(rng):
    """A rational vector (t, x) with |x| < t, in 1 + 3 dimensions."""
    xs = [Fraction(rng.randint(-20, 20), rng.randint(1, 9)) for _ in range(3)]
    t = Fraction(sum(abs(x) for x in xs) + rng.randint(1, 5), 1)
    return t, xs


def main():
    print("Twins: Earth time 10 years, traveller out and back at speed v")
    print("      v     gamma   traveller ages")
    for v in [Fraction(3, 5), Fraction(4, 5), Fraction(5, 13),
              Fraction(12, 13), Fraction(20, 29)]:
        g = gamma_rational(v)
        print(f"  {str(v):>6}   {str(g):>6}   {str(10 / g):>6} years")
    print()
    rng = random.Random(1908)
    pairs = [(random_future_timelike(rng), random_future_timelike(rng))
             for _ in range(2000)]
    ok = sum(reverse_triangle_holds(v, w) for v, w in pairs)
    print(f"reverse triangle inequality holds for {ok} of {len(pairs)}"
          " random pairs")
    straight = reverse_triangle_holds((Fraction(5), [Fraction(3), 0, 0]),
                                      (Fraction(10), [Fraction(6), 0, 0]))
    print("equality case (parallel vectors) still satisfies it:", straight)
    print()
    print("Velocity addition (u (+) v) = (u + v)/(1 + uv):")
    for u, v in [(Fraction(3, 5), Fraction(3, 5)), (Fraction(4, 5), Fraction(5, 13)),
                 (Fraction(12, 13), Fraction(3, 5))]:
        w = add_velocities(u, v)
        lhs = gamma_rational(w)
        rhs = gamma_rational(u) * gamma_rational(v) * (1 + u * v)
        print(f"  {u} (+) {v} = {w};  gamma: {lhs} = {rhs}: {lhs == rhs}")
    print()
    print("Epistemic status: exact rational arithmetic on finitely many cases.")
    print("It confirms specific instances of theorems proved in the lesson")
    print("(and formalised in Lean for all vectors); it is not a proof.")


if __name__ == "__main__":
    main()
