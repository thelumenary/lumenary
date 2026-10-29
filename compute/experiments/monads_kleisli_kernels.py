"""The distribution monad: Kleisli arrows are Markov kernels.

D X is the set of finitely supported probability distributions on X; the unit
sends x to the point mass at x and the multiplication averages a distribution
of distributions. A Kleisli arrow X -> D Y is a Markov kernel (a stochastic
matrix), and the experiment computes Kleisli composition *from the monad
structure* (push forward, then flatten) and compares it with the product of
stochastic matrices - the Chapman-Kolmogorov equation. It also checks the
Kleisli identity and associativity laws, and that expectation E : D(R) -> R is
an Eilenberg-Moore algebra whose associativity law is the tower property of
conditional expectation. Exact rational arithmetic; random kernels are seeded.
"""

import random
from fractions import Fraction

EXPERIMENT = {
    "id": "monads_kleisli_kernels",
    "title": "Kleisli composition for the distribution monad",
    "evidence": ["exact", "experimental"],
    "lessons": ["monads"],
    "summary": (
        "Computes Kleisli composition for the finite distribution monad from "
        "eta and mu, and checks with exact fractions that it equals the "
        "product of stochastic matrices, that the Kleisli laws hold, and that "
        "expectation satisfies the algebra laws (the tower property) - on 200 "
        "seeded random kernels, which is evidence, not proof."
    ),
    "packages": [],
}


def unit(x):
    """eta: the point mass at x, as a dict {outcome: probability}."""
    return {x: Fraction(1)}


def flatten(dist_of_dists):
    """mu: average a list of (probability, distribution) pairs."""
    out = {}
    for p, dist in dist_of_dists:
        for y, q in dist.items():
            out[y] = out.get(y, Fraction(0)) + p * q
    return {y: q for y, q in out.items() if q != 0}


def push(dist, kernel):
    """D k: apply a kernel to every outcome, giving a distribution of dists."""
    return [(p, kernel(x)) for x, p in dist.items()]


def kleisli(f, g):
    """Kleisli composite x |-> mu(D g (f x)) of kernels f, then g."""
    return lambda x: flatten(push(f(x), g))


def kernel_from_matrix(matrix):
    """The kernel i |-> row i of a stochastic matrix."""
    return lambda i: {j: p for j, p in enumerate(matrix[i]) if p != 0}


def matrix_from_kernel(kernel, rows, cols):
    """The stochastic matrix of a kernel on {0..rows-1} -> {0..cols-1}."""
    return [[kernel(i).get(j, Fraction(0)) for j in range(cols)]
            for i in range(rows)]


def mat_mul(a, b):
    """Product of matrices with Fraction entries."""
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), Fraction(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def random_stochastic(rows, cols, rng):
    """A random stochastic matrix with small rational entries."""
    matrix = []
    for _ in range(rows):
        weights = [rng.randint(0, 4) for _ in range(cols)]
        if sum(weights) == 0:
            weights[rng.randrange(cols)] = 1
        total = sum(weights)
        matrix.append([Fraction(w, total) for w in weights])
    return matrix


def expectation(dist):
    """The algebra map E : D(Q) -> Q."""
    return sum((p * x for x, p in dist.items()), Fraction(0))


def tower_property_holds(dist_of_dists):
    """E(D E (P)) == E(mu P): the algebra associativity law for E."""
    outer = {}
    for p, dist in dist_of_dists:
        m = expectation(dist)
        outer[m] = outer.get(m, Fraction(0)) + p
    return expectation(outer) == expectation(flatten(dist_of_dists))


def random_mixture(size, rng):
    """A random distribution (list of weighted pairs) of distributions."""
    out = []
    for p in random_stochastic(1, size, rng)[0]:
        dist = {}
        for q in random_stochastic(1, 3, rng)[0]:
            v = Fraction(rng.randint(-9, 9))
            dist[v] = dist.get(v, Fraction(0)) + q
        out.append((p, dist))
    return out


def run_trials(trials, rng):
    """Count failures of each law on random kernels between small sets."""
    fails = {"matrix": 0, "assoc": 0, "unit": 0, "tower": 0}
    for _ in range(trials):
        a, b, c, d = (rng.randint(1, 4) for _ in range(4))
        m1, m2, m3 = (random_stochastic(a, b, rng),
                      random_stochastic(b, c, rng),
                      random_stochastic(c, d, rng))
        f, g, h = map(kernel_from_matrix, (m1, m2, m3))
        if matrix_from_kernel(kleisli(f, g), a, c) != mat_mul(m1, m2):
            fails["matrix"] += 1
        left = matrix_from_kernel(kleisli(kleisli(f, g), h), a, d)
        right = matrix_from_kernel(kleisli(f, kleisli(g, h)), a, d)
        fails["assoc"] += left != right
        ident = (matrix_from_kernel(kleisli(unit, f), a, b) == m1
                 == matrix_from_kernel(kleisli(f, unit), a, b))
        fails["unit"] += not ident
        fails["tower"] += not tower_property_holds(random_mixture(b, rng))
    return fails


def main():
    rain = [[Fraction(7, 10), Fraction(3, 10)],
            [Fraction(2, 5), Fraction(3, 5)]]
    weather = kernel_from_matrix(rain)
    two_days = matrix_from_kernel(kleisli(weather, weather), 2, 2)
    print("A two-state weather chain (0 = dry, 1 = rainy) as a Kleisli arrow")
    print(f"  one day:   {[[str(p) for p in row] for row in rain]}")
    print(f"  two days via mu . D k . k: "
          f"{[[str(p) for p in row] for row in two_days]}")
    print(f"  equals the matrix square:  {two_days == mat_mul(rain, rain)}")
    rng = random.Random(2024)
    fails = run_trials(200, rng)
    print("200 seeded random kernels between sets of size 1 to 4:")
    print(f"  Kleisli composite != matrix product:     {fails['matrix']}")
    print(f"  associativity failures:                  {fails['assoc']}")
    print(f"  identity-law failures (eta = Dirac):     {fails['unit']}")
    print(f"  tower-property failures for E:           {fails['tower']}")
    print()
    print("Epistemic status: exact rational arithmetic, so each check is a "
          "true\nstatement about the kernels tested; but 200 random cases "
          "are evidence,\nnot proof. The general facts (Kleisli composition "
          "is matrix product,\nE is a D-algebra) follow from linearity, as "
          "the lesson explains.")


if __name__ == "__main__":
    main()
