"""Picard iteration, computed exactly with SymPy.

The initial value problem x' = f(t, x), x(t0) = x0 is equivalent to the
integral equation x(t) = x0 + integral from t0 to t of f(s, x(s)) ds. Picard's
iteration starts from the constant x0 and repeatedly substitutes into the
right-hand side. For x' = x it produces the Taylor polynomials of e^t; for
x' = t + x the iterates converge to 2e^t - t - 1; for x' = x^2, x(0) = 1 they
reproduce, term by term, the series 1 + t + t^2 + ... of the solution
1/(1 - t), which only converges for |t| < 1 - a shadow of the blow-up at t = 1.

Runs in the browser (Pyodide) with the sympy package loaded.
"""

import sympy

EXPERIMENT = {
    "id": "ordinary_differential_equations_picard_iteration",
    "title": "Picard iteration: exact successive approximations",
    "evidence": ["symbolic", "exact"],
    "lessons": ["ordinary-differential-equations"],
    "summary": (
        "Computes Picard iterates exactly with SymPy for x' = x, x' = t + x and "
        "x' = x^2 (all with x(0) = 1), compares them with the exact solutions, "
        "and shows the iterates for x' = x^2 agreeing with the series of "
        "1/(1 - t) to higher and higher order. Exact symbolic computation of "
        "finitely many iterates; convergence is the Picard-Lindelof theorem."
    ),
    "packages": ["sympy"],
}

t, s = sympy.symbols("t s", real=True)


def picard_iterates(f, x0, count, t0=0):
    """Return [x_0, x_1, ..., x_count] with x_0 = x0 and
    x_{k+1}(t) = x0 + integral_{t0}^{t} f(s, x_k(s)) ds."""
    iterates = [sympy.Integer(x0) if isinstance(x0, int) else sympy.sympify(x0)]
    for _ in range(count):
        prev = iterates[-1]
        integrand = f(s, prev.subs(t, s))
        nxt = x0 + sympy.integrate(integrand, (s, t0, t))
        iterates.append(sympy.expand(nxt))
    return iterates


def agreement_order(approx, exact, max_order=20):
    """Largest n such that approx and exact agree up to and including t^n."""
    diff = sympy.series(approx - exact, t, 0, max_order + 1).removeO()
    poly = sympy.Poly(sympy.expand(diff), t)
    nonzero = [m[0] for m, c in zip(poly.monoms(), poly.coeffs()) if c != 0]
    return (min(nonzero) - 1) if nonzero else max_order


def main():
    print(f"Picard iteration with SymPy {sympy.__version__}, all with x(0) = 1")
    xs = picard_iterates(lambda u, x: x, 1, 5)
    print("x' = x:")
    for k in [1, 2, 3, 5]:
        print(f"   x_{k}(t) = {xs[k]}")
    print("   these are the Taylor polynomials of the solution e^t")
    ys = picard_iterates(lambda u, x: u + x, 1, 6)
    exact = 2 * sympy.exp(t) - t - 1
    print("x' = t + x (exact solution 2 e^t - t - 1):")
    for k in [2, 4, 6]:
        order = agreement_order(ys[k], exact)
        value = float(ys[k].subs(t, 1))
        print(f"   x_{k}(1) = {value:.6f}, agrees with the solution up to t^{order}")
    print(f"   exact value at t = 1: {float(exact.subs(t, 1)):.6f}")
    zs = picard_iterates(lambda u, x: x**2, 1, 4)
    sol = 1 / (1 - t)
    print("x' = x^2 (exact solution 1/(1 - t), which blows up at t = 1):")
    for k in range(1, 5):
        order = agreement_order(zs[k], sol)
        degree = int(sympy.degree(zs[k], t))
        print(f"   x_{k}: degree {degree:2d}, agrees with 1/(1 - t) up to t^{order}")
    print("   the series 1 + t + t^2 + ... converges only for |t| < 1;")
    print(f"   x_4(0.5) = {float(zs[4].subs(t, 0.5)):.6f} vs 1/(1 - 0.5) = 2,")
    print(f"   x_4(1.5) = {float(zs[4].subs(t, 1.5)):.1f}, but the solution ends at t = 1")
    print()
    print("Epistemic status: exact symbolic computation of a few iterates (as")
    print("reliable as SymPy's integration). That the iterates converge to the")
    print("unique solution on a short interval is the Picard-Lindelof theorem,")
    print("proved in the lesson; the computation only illustrates it.")


if __name__ == "__main__":
    main()
