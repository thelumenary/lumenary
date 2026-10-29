"""Weierstrass's function: difference quotients at 0 that run away.

W(x) = sum over k >= 0 of a^k cos(b^k pi x), with a = 1/2 and b = 13, is a
uniform limit of smooth functions (Weierstrass M-test), hence continuous. At
the points h_m = 13^(-m) we can evaluate W exactly in closed form: for k >= m
the number b^k h_m = 13^(k-m) is an odd integer, so cos(b^k pi h_m) = -1 and
the infinite tail sums to -a^m/(1 - a). Only the first m terms need floating
point. The difference quotients D_m = (W(h_m) - W(0))/h_m then grow like
(ab)^m = 6.5^m, so W is not differentiable at 0. Every partial sum W_K is
smooth, and its quotients settle down to W_K'(0) = 0 instead.

Evidence: exact closed forms for the tail plus floating-point arithmetic for
finitely many terms; one point (x = 0) is examined, not every point.
"""

import math

EXPERIMENT = {
    "id": "real_analysis_weierstrass_function",
    "title": "Weierstrass's function: difference quotients that run away",
    "evidence": ["exact", "numerical"],
    "lessons": ["real-analysis"],
    "summary": (
        "Evaluates Weierstrass's function W(x) = sum (1/2)^k cos(13^k pi x) at "
        "x = 0 and x = 13^-m, summing the infinite tail exactly in closed form. "
        "The difference quotients at 0 grow like 6.5^m, while those of every "
        "smooth partial sum settle to 0. This examines a single point; "
        "nowhere-differentiability needs Weierstrass's proof for every x."
    ),
    "packages": [],
}

A = 0.5
B = 13


def partial_sum(x, terms, a=A, b=B):
    """W_K(x): the first `terms` terms of the series (floating point)."""
    return sum(a ** k * math.cos(b ** k * math.pi * x) for k in range(terms))


def w_at_zero(a=A):
    """W(0) = sum of a^k = 1/(1 - a), exactly."""
    return 1 / (1 - a)


def w_at_power(m, a=A, b=B):
    """W(b^-m) for an odd integer b: m float terms plus the exact tail."""
    if b % 2 == 0:
        raise ValueError("b must be odd for the closed-form tail")
    head = sum(a ** k * math.cos(math.pi / b ** (m - k)) for k in range(m))
    tail = -(a ** m) / (1 - a)  # cos(odd multiple of pi) = -1
    return head + tail


def quotient(m, a=A, b=B):
    """D_m = (W(h) - W(0)) / h with h = b^-m."""
    return (w_at_power(m, a, b) - w_at_zero(a)) * b ** m


def partial_quotient(m, terms, a=A, b=B):
    """Difference quotient of the smooth partial sum W_K at 0, h = b^-m."""
    h = 1 / b ** m
    return (partial_sum(h, terms, a, b) - partial_sum(0, terms, a, b)) / h


def main():
    print("W(x) = sum (1/2)^k cos(13^k pi x);  ab = 6.5 > 1 + 3pi/2")
    print("Difference quotients at 0 with h = 13^-m:")
    print("  m          h            D_m   D_m / 6.5^m   W_3 quotient")
    for m in range(1, 9):
        d = quotient(m)
        p = partial_quotient(m, 3)
        print(f"{m:3d}   {B ** -m:10.3e}   {d:12.4e}   {d / 6.5 ** m:11.5f}"
              f"   {p:12.4e}")
    print()
    print("D_m / 6.5^m tends to a negative constant, so |D_m| -> infinity:")
    print("W has no derivative at 0. The smooth partial sum W_3 behaves")
    print("as calculus predicts: its quotients shrink to W_3'(0) = 0.")
    print()
    print("Epistemic status: the tail of the series is summed exactly, and")
    print("only m cosines are computed in floating point, so these numbers are")
    print("reliable; together with the lesson's estimate they prove that W is")
    print("not differentiable at 0. They say nothing about other points:")
    print("nowhere-differentiability needs Weierstrass's argument for every x.")


if __name__ == "__main__":
    main()
