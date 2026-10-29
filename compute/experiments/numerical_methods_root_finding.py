"""Bisection, Newton and secant: measuring orders of convergence.

We solve x^2 = 2 with 50-digit decimal arithmetic, so that rounding does not
hide the behaviour, and print the errors e_n = |x_n - sqrt 2|. Bisection
halves its error bound each step (order 1, rate 1/2); Newton's method roughly
doubles the number of correct digits (order 2); the secant method is in
between (order (1 + sqrt 5)/2 = 1.618...). The estimated order is
log(e_{n+1}/e_n) / log(e_n/e_{n-1}). Then two warnings: at the double root of
(x - 1)^2 Newton converges only linearly, and for x^3 - 2x + 2 started at 0
it never converges, cycling 0, 1, 0, 1, ...
"""

import math
from decimal import Decimal, getcontext

EXPERIMENT = {
    "id": "numerical_methods_root_finding",
    "title": "Bisection, Newton and secant: orders of convergence",
    "evidence": ["numerical", "counterexample"],
    "lessons": ["numerical-methods"],
    "summary": (
        "Solves x^2 = 2 in 50-digit decimal arithmetic by bisection, Newton's "
        "method and the secant method, printing the errors and estimated orders "
        "of convergence (about 1, 2 and 1.618). Then shows Newton's method "
        "converging only linearly at a double root and cycling forever for "
        "x^3 - 2x + 2 started at 0."
    ),
    "packages": [],
}

getcontext().prec = 50


def bisection(f, a, b, steps):
    """Midpoints of the bisection intervals, assuming f(a) < 0 < f(b)."""
    mids = []
    for _ in range(steps):
        m = (a + b) / 2
        mids.append(m)
        if f(m) <= 0:
            a = m
        else:
            b = m
    return mids


def newton(f, df, x, steps):
    """Newton iterates x_{n+1} = x_n - f(x_n)/f'(x_n), starting value included."""
    xs = [x]
    for _ in range(steps):
        x = x - f(x) / df(x)
        xs.append(x)
    return xs


def secant(f, x0, x1, steps):
    """Secant iterates, starting values included; stops if f values coincide."""
    xs = [x0, x1]
    for _ in range(steps):
        f0, f1 = f(xs[-2]), f(xs[-1])
        if f1 == f0:
            break
        xs.append(xs[-1] - f1 * (xs[-1] - xs[-2]) / (f1 - f0))
    return xs


def orders(errors):
    """Estimated orders log(e2/e1)/log(e1/e0) for consecutive triples."""
    out = []
    for e0, e1, e2 in zip(errors, errors[1:], errors[2:]):
        if min(e0, e1, e2) > 0 and e1 != e0:
            out.append(math.log(e2 / e1) / math.log(e1 / e0))
    return out


def main():
    root = Decimal(2).sqrt()
    f = lambda x: x * x - 2
    df = lambda x: 2 * x
    mids = bisection(f, Decimal(1), Decimal(2), 8)
    errs = [float(abs(x - root)) for x in mids]
    print("bisection errors: " + " ".join(f"{e:.0e}" for e in errs))
    print("          bounds: " + " ".join(f"{0.5 ** (n + 1):.0e}"
                                         for n in range(len(mids))))
    runs = [
        ("Newton", newton(f, df, Decimal(2), 6)[1:]),
        ("secant", secant(f, Decimal(2), Decimal(1), 7)[2:]),
    ]
    for name, xs in runs:
        errs = [float(abs(x - root)) for x in xs]
        shown = " ".join(f"{e:.0e}" for e in errs)
        est = orders(errs)
        print(f"{name:9s} errors: {shown}")
        print(f"{'':9s} estimated orders: "
              + ", ".join(f"{p:.2f}" for p in est[:5]))
    print()
    g = lambda x: (x - 1) ** 2
    dg = lambda x: 2 * (x - 1)
    xs = newton(g, dg, Decimal(2), 6)
    print("Newton at the double root of (x - 1)^2, errors:")
    print("  " + " ".join(f"{float(x - 1):g}" for x in xs))
    h = lambda x: x ** 3 - 2 * x + 2
    dh = lambda x: 3 * x * x - 2
    cyc = newton(h, dh, Decimal(0), 6)
    print("Newton for x^3 - 2x + 2 from 0:", [int(x) for x in cyc])
    print()
    print("Epistemic status: numerical evidence for one equation; the orders")
    print("1, 2 and 1.618 are theorems for simple roots of smooth functions")
    print("(proved for bisection and Newton in the lesson). The last two runs")
    print("are exact counterexamples showing that the hypotheses matter.")


if __name__ == "__main__":
    main()
