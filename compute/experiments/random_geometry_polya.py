"""Polya's theorem by exact return probabilities.

Simple random walk on Z^d is recurrent exactly when the expected number of
returns to the origin, G = sum_n u_2n with u_2n = P(S_2n = 0), is infinite.
We compute u_2n exactly or to floating-point accuracy:

    d = 1:  u_2n = C(2n, n) / 4^n
    d = 2:  u_2n = (C(2n, n) / 4^n)^2          (the 45-degree rotation trick)
    d = 3:  condition on the number 2j of vertical steps:
            u_2n = sum_j C(2n, 2j) (1/3)^(2j) (2/3)^(2n-2j) u1_2j u2_(2n-2j)

and watch the partial sums G(N): they grow like sqrt(N) in d = 1, like
log(N)/pi in d = 2, and converge in d = 3, to Watson's constant
G = sqrt(6)/(32 pi^3) Gamma(1/24) Gamma(5/24) Gamma(7/24) Gamma(11/24),
so the walk returns with probability 1 - 1/G = 0.3405... We also check the
rotation trick exhaustively for short walks.

Evidence: exact counting for short walks (exhaustive-finite) and
floating-point summation of exact formulas (numerical). Finite partial sums
cannot prove divergence; the proofs are in the lesson and in Lean.
"""

import itertools
import math

EXPERIMENT = {
    "id": "random_geometry_polya",
    "title": "Polya's theorem: return probabilities in dimensions 1, 2 and 3",
    "evidence": ["exhaustive-finite", "numerical"],
    "lessons": ["random-geometry"],
    "summary": (
        "Checks by exhaustive enumeration that the number of closed walks of "
        "length 2n on Z^2 is C(2n, n)^2, then sums exact return probabilities "
        "of simple random walk on Z, Z^2 and Z^3: the expected number of "
        "returns grows like sqrt(N), like log(N)/pi, and converges to Watson's "
        "constant 1.5164 (return probability 0.3405). Partial sums are "
        "evidence; divergence and convergence are proved in the lesson."
    ),
    "packages": [],
}

STEPS2 = [(1, 0), (-1, 0), (0, 1), (0, -1)]


def closed_walks_2d(n):
    """Number of walks of length 2n on Z^2 that end at the origin (brute force)."""
    count = 0
    for walk in itertools.product(STEPS2, repeat=2 * n):
        if sum(s[0] for s in walk) == 0 and sum(s[1] for s in walk) == 0:
            count += 1
    return count


def u1(n_max):
    """[u_0, u_2, ..., u_2n_max] for d = 1, via u_2n+2 = u_2n (2n+1)/(2n+2)."""
    u = [1.0]
    for n in range(n_max):
        u.append(u[-1] * (2 * n + 1) / (2 * n + 2))
    return u


def u3(n_max, one=None):
    """Return probabilities u_2n of simple random walk on Z^3, n <= n_max."""
    one = one if one is not None else u1(n_max)
    two = [x * x for x in one]
    out = []
    for n in range(n_max + 1):
        total = 0.0
        # term for j vertical pairs: C(2n,2j) (1/3)^2j (2/3)^(2n-2j) one[j] two[n-j]
        log_c = 0.0  # log C(2n, 2j), updated multiplicatively
        for j in range(n + 1):
            if j > 0:
                a = 2 * n - 2 * j + 2
                log_c += math.log(a * (a - 1) / ((2 * j) * (2 * j - 1)))
            weight = math.exp(log_c + 2 * j * math.log(1 / 3)
                              + (2 * n - 2 * j) * math.log(2 / 3))
            total += weight * one[j] * two[n - j]
        out.append(total)
    return out


def watson_constant():
    """G(Z^3) = sqrt(6)/(32 pi^3) Gamma(1/24)Gamma(5/24)Gamma(7/24)Gamma(11/24)."""
    g = math.gamma
    return (math.sqrt(6) / (32 * math.pi ** 3)
            * g(1 / 24) * g(5 / 24) * g(7 / 24) * g(11 / 24))


def partial_sums(u, checkpoints):
    """{N: sum_{n=0}^{N} u_2n} at the given N."""
    out, s = {}, 0.0
    for n, x in enumerate(u):
        s += x
        if n in checkpoints:
            out[n] = s
    return out


def main():
    print("Exhaustive check of the rotation trick on Z^2:")
    for n in range(1, 5):
        print(f"  closed walks of length {2 * n}: {closed_walks_2d(n):>5}"
              f"   C({2 * n},{n})^2 = {math.comb(2 * n, n) ** 2:>5}")
    big, small = 100000, 1200
    one = u1(big)
    g1 = partial_sums(one, {100, 1000, 10000, 100000})
    g2 = partial_sums([x * x for x in one], {100, 1000, 10000, 100000})
    g3 = partial_sums(u3(small, one), {100, 300, 1200})
    print()
    print("Expected number of visits to 0 up to time 2N, G(N) = sum u_2n:")
    print(f"{'N':>8}{'d = 1':>11}{'2 sqrt(N/pi)':>14}{'d = 2':>9}"
          f"{'log(N)/pi':>11}")
    for n in sorted(g1):
        print(f"{n:>8}{g1[n]:>11.2f}{2 * math.sqrt(n / math.pi):>14.2f}"
              f"{g2[n]:>9.3f}{math.log(n) / math.pi:>11.3f}")
    c3 = 4 * (3 / (4 * math.pi)) ** 1.5  # tail ~ c3 / sqrt(N)
    print(f"{'N':>8}{'d = 3':>11}{'+ tail est.':>14}")
    for n in sorted(g3):
        print(f"{n:>8}{g3[n]:>11.5f}{g3[n] + c3 / math.sqrt(n):>14.5f}")
    w = watson_constant()
    print(f"Watson's exact value G = {w:.7f}; return probability "
          f"1 - 1/G = {1 - 1 / w:.6f}")
    print()
    print("Epistemic status: the first table is an exhaustive count (exact);")
    print("the others sum exact formulas in floating point. Partial sums that")
    print("grow, or seem to settle, cannot by themselves prove divergence or")
    print("convergence; the d = 1, 2 divergence is proved in the lesson and in")
    print("Lean, and d = 3 convergence in the lesson (by an estimate).")


if __name__ == "__main__":
    main()
