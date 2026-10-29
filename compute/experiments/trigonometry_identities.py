"""Testing trigonometric identities: numbers, triangles and symbols.

Three kinds of evidence. (1) Numerical: evaluate both sides of an identity
at many seeded random angles and record the largest difference; a false
"identity" such as sin(a + b) = sin a + sin b is caught at once. (2) The laws
of cosines and sines, checked on random triangles built from coordinates.
(3) Symbolic: SymPy expands sin(a + b) and simplifies differences to 0. We
also show the classic trap of passing degrees to a function that expects
radians.
"""

import math
import random

import sympy

EXPERIMENT = {
    "id": "trigonometry_identities",
    "title": "Trigonometric identities: numbers, triangles, symbols",
    "evidence": ["numerical", "symbolic", "counterexample"],
    "lessons": ["trigonometry"],
    "summary": (
        "Evaluates sin^2 + cos^2 = 1, the addition and double-angle formulas "
        "and the false rule sin(a + b) = sin a + sin b at 1,000 random angle "
        "pairs, checks the laws of cosines and sines on 1,000 random triangles, "
        "and lets SymPy verify the identities symbolically. Floating-point and "
        "symbolic evidence; the proofs are in the lesson."
    ),
    "packages": ["sympy"],
}

IDENTITIES = {
    "sin^2 a + cos^2 a = 1":
        lambda a, b: (math.sin(a) ** 2 + math.cos(a) ** 2, 1.0),
    "sin(a+b) = sin a cos b + cos a sin b":
        lambda a, b: (math.sin(a + b),
                      math.sin(a) * math.cos(b) + math.cos(a) * math.sin(b)),
    "cos(a+b) = cos a cos b - sin a sin b":
        lambda a, b: (math.cos(a + b),
                      math.cos(a) * math.cos(b) - math.sin(a) * math.sin(b)),
    "cos 2a = 1 - 2 sin^2 a":
        lambda a, b: (math.cos(2 * a), 1 - 2 * math.sin(a) ** 2),
    "sin(a+b) = sin a + sin b  (false!)":
        lambda a, b: (math.sin(a + b), math.sin(a) + math.sin(b)),
}


def max_error(identity, pairs):
    """Largest |lhs - rhs| of an identity over a list of angle pairs."""
    return max(abs(lhs - rhs) for lhs, rhs in (identity(a, b) for a, b in pairs))


def random_pairs(count, seed):
    """Seeded random angle pairs in [-2 pi, 2 pi]."""
    rng = random.Random(seed)
    return [(rng.uniform(-2 * math.pi, 2 * math.pi),
             rng.uniform(-2 * math.pi, 2 * math.pi)) for _ in range(count)]


def triangle(p, q, r):
    """Side lengths (a, b, c) opposite p, q, r and the angles at p, q, r."""
    a, b, c = math.dist(q, r), math.dist(r, p), math.dist(p, q)

    def angle(u, v, w):  # angle at v
        x1, y1, x2, y2 = u[0] - v[0], u[1] - v[1], w[0] - v[0], w[1] - v[1]
        return math.atan2(abs(x1 * y2 - y1 * x2), x1 * x2 + y1 * y2)

    return (a, b, c), (angle(q, p, r), angle(p, q, r), angle(p, r, q))


def law_errors(sides, angles):
    """Relative errors of the law of cosines (at r) and the law of sines."""
    (a, b, c), (pa, pb, pc) = sides, angles
    cosines = abs(c * c - (a * a + b * b - 2 * a * b * math.cos(pc))) / (c * c)
    ratios = [a / math.sin(pa), b / math.sin(pb), c / math.sin(pc)]
    sines = (max(ratios) - min(ratios)) / max(ratios)
    return cosines, sines


def symbolic_difference(lhs, rhs):
    """SymPy's simplification of lhs - rhs (0 means SymPy proves equality)."""
    return sympy.simplify(sympy.expand_trig(lhs - rhs))


def main():
    print(f"math.sin(30)               = {math.sin(30):+.6f}  (30 radians!)")
    print(f"math.sin(math.radians(30)) = {math.sin(math.radians(30)):+.6f}")
    pairs = random_pairs(1000, 2024)
    print("Largest |lhs - rhs| over 1000 random angle pairs:")
    for name, identity in IDENTITIES.items():
        print(f"  {name:<38} {max_error(identity, pairs):.1e}")
    rng = random.Random(7)
    worst_cos = worst_sin = 0.0
    for _ in range(1000):
        pts = [(rng.uniform(-5, 5), rng.uniform(-5, 5)) for _ in range(3)]
        sides, angles = triangle(*pts)
        if min(angles) < 1e-3:  # skip nearly flat triangles
            continue
        e_cos, e_sin = law_errors(sides, angles)
        worst_cos, worst_sin = max(worst_cos, e_cos), max(worst_sin, e_sin)
    print("Random triangles, worst relative error:")
    print(f"  law of cosines {worst_cos:.1e}, law of sines {worst_sin:.1e}")
    a, b = sympy.symbols("a b")
    print("SymPy:")
    print(f"  expand_trig(sin(a+b)) = {sympy.expand_trig(sympy.sin(a + b))}")
    for lhs, rhs in [(sympy.sin(a) ** 2 + sympy.cos(a) ** 2, 1),
                     (sympy.cos(2 * a), 1 - 2 * sympy.sin(a) ** 2),
                     (sympy.sin(a + b), sympy.sin(a) + sympy.sin(b))]:
        print(f"  simplify({lhs} - ({rhs})) = {symbolic_difference(lhs, rhs)}")
    print()
    print("Epistemic status: the numerical checks are evidence at finitely many")
    print("points, accurate to rounding (1e-15 to 1e-13). One large error is")
    print("enough to refute the false rule: that is a counterexample.")
    print("SymPy's zeros are symbolic verifications that rely on its built-in")
    print("rules. The proofs in the lesson explain why the identities hold.")


if __name__ == "__main__":
    main()
