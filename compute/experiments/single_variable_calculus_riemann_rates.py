"""How fast do Riemann sums converge? Left, midpoint, trapezoid and Simpson.

For the integral of e^x over [0, 1] (exact value e - 1) we compute four
approximations with n = 4, 8, ..., 64 strips and measure the observed order
of convergence: if the error behaves like C / n^p, doubling n divides it by
2^p, so p = log2(error(n) / error(2n)). Theory (proved with Taylor's theorem)
predicts p = 1 for the left rule, 2 for the midpoint and trapezoid rules and
4 for Simpson's rule, for smooth integrands.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import math

EXPERIMENT = {
    "id": "single_variable_calculus_riemann_rates",
    "title": "Riemann sums and Simpson's rule: measured rates of convergence",
    "evidence": ["numerical"],
    "lessons": ["single-variable-calculus"],
    "summary": (
        "Approximates the integral of e^x over [0, 1] by left, midpoint, "
        "trapezoid and Simpson sums with 4 to 64 strips, prints the errors "
        "against e - 1 and the observed orders log2(E(n)/E(2n)), which come out "
        "close to 1, 2, 2 and 4 as the error theorems predict. Floating-point "
        "evidence for one smooth function, not a proof of the error bounds."
    ),
    "packages": [],
}


def left_sum(f, a, b, n):
    """Left Riemann sum with n equal strips."""
    h = (b - a) / n
    return h * sum(f(a + i * h) for i in range(n))


def midpoint_sum(f, a, b, n):
    """Midpoint rule with n equal strips."""
    h = (b - a) / n
    return h * sum(f(a + (i + 0.5) * h) for i in range(n))


def trapezoid_sum(f, a, b, n):
    """Trapezoid rule with n equal strips."""
    h = (b - a) / n
    inner = sum(f(a + i * h) for i in range(1, n))
    return h * (0.5 * f(a) + inner + 0.5 * f(b))


def simpson_sum(f, a, b, n):
    """Composite Simpson's rule with n equal strips (n must be even)."""
    if n <= 0 or n % 2:
        raise ValueError("Simpson's rule needs a positive even number of strips")
    h = (b - a) / n
    odd = sum(f(a + i * h) for i in range(1, n, 2))
    even = sum(f(a + i * h) for i in range(2, n, 2))
    return h / 3 * (f(a) + 4 * odd + 2 * even + f(b))


def observed_order(error_n, error_2n):
    """Estimate p from errors with n and 2n strips, assuming error ~ C / n^p."""
    return math.log2(abs(error_n) / abs(error_2n))


RULES = [
    ("left", left_sum),
    ("midpoint", midpoint_sum),
    ("trapezoid", trapezoid_sum),
    ("Simpson", simpson_sum),
]


def error_table(f, a, b, exact, ns):
    """Map each rule name to its list of signed errors (approximation - exact)."""
    return {name: [rule(f, a, b, n) - exact for n in ns] for name, rule in RULES}


def main():
    exact = math.e - 1
    ns = [4, 8, 16, 32, 64]
    table = error_table(math.exp, 0.0, 1.0, exact, ns)
    print("Integral of e^x over [0, 1] = e - 1; signed errors (approx - exact)")
    print("   n        left       midpoint     trapezoid      Simpson")
    for i, n in enumerate(ns):
        row = "  ".join(f"{table[name][i]:+.3e}" for name, _ in RULES)
        print(f"  {n:2d}  {row}")
    print("Observed order p = log2(E(n) / E(2n)):")
    for name, _ in RULES:
        errs = table[name]
        orders = [observed_order(errs[i], errs[i + 1]) for i in range(len(ns) - 1)]
        shown = ", ".join(f"{p:.2f}" for p in orders)
        print(f"  {name:<9} {shown}")
    ratio = table["midpoint"][-1] / table["trapezoid"][-1]
    print(f"Midpoint error / trapezoid error at n = 64: {ratio:+.4f}")
    print("(about -1/2, so (2M + T)/3 - Simpson with 2n strips - cancels them)")
    print()
    print("Epistemic status: floating-point evidence for one smooth integrand.")
    print("The orders 1, 2, 2, 4 agree with the error theorems for these rules,")
    print("which are proved with Taylor's theorem and need f to be smooth enough;")
    print("for a function with a kink or a singularity the rates can be worse.")


if __name__ == "__main__":
    main()
