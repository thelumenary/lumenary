"""Linear or exponential? Fitting world population and testing the forecast.

We fit two models to approximate world population for 1950-1980 (UN
estimates, rounded to 0.1 billion): a straight line, and an exponential
P = A e^(r t) fitted as a straight line through (t, ln P). Then we compare
each model's forecasts for 1990-2020 with the later estimates. This is how a
model is validated: by predictions it was not built from.
"""

import math

EXPERIMENT = {
    "id": "modelling_with_functions_population",
    "title": "Linear or exponential? Forecasting world population",
    "evidence": ["numerical"],
    "lessons": ["modelling-with-functions"],
    "summary": (
        "Fits linear and exponential models by least squares to approximate UN "
        "estimates of world population for 1950-1980, forecasts 1990-2020 and "
        "compares with the later estimates. Neither model survives validation: "
        "the growth rate itself changed. Numerical evidence about one data set."
    ),
    "packages": [],
}

#: World population in billions, approximate UN estimates rounded to 0.1.
YEARS = [1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020]
POPULATION = [2.5, 3.0, 3.7, 4.4, 5.3, 6.1, 7.0, 7.8]


def fit_line(xs, ys):
    """Least-squares line y = m x + c; returns (m, c)."""
    n = len(xs)
    if n < 2 or len(set(xs)) < 2:
        raise ValueError("need at least two different x-values")
    mx, my = sum(xs) / n, sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    m = sxy / sxx
    return m, my - m * mx


def fit_exponential(ts, ps):
    """Fit P = A e^(r t) by a least-squares line through (t, ln P).

    Returns (A, r).
    """
    r, log_a = fit_line(ts, [math.log(p) for p in ps])
    return math.exp(log_a), r


def doubling_time(r):
    """Time for e^(r t) to double: ln 2 / r."""
    if r <= 0:
        raise ValueError("growth rate must be positive")
    return math.log(2) / r


def main():
    k = 4  # fit on 1950-1980 only
    ts = [y - 1950 for y in YEARS]
    m, c = fit_line(ts[:k], POPULATION[:k])
    a, r = fit_exponential(ts[:k], POPULATION[:k])
    print("Models fitted to 1950-1980 (t = years after 1950, P in billions):")
    print(f"  linear:      P = {c:.3f} + {m:.4f} t")
    print(f"  exponential: P = {a:.3f} e^({r:.4f} t)")
    print(f"  (growth {100 * r:.2f}% a year: doubling every"
          f" {doubling_time(r):.0f} years)")
    print()
    print("year  estimate    linear   error  exponential   error")
    for year, t, p in zip(YEARS, ts, POPULATION):
        lin, expo = c + m * t, a * math.exp(r * t)
        tag = "fitted" if year <= 1980 else "forecast"
        print(f"{year}  {p:7.1f}  {lin:8.2f}  {lin - p:+6.2f}  {expo:10.2f}"
              f"   {expo - p:+6.2f}  {tag}")
    print()
    rates = [math.log(POPULATION[i + 1] / POPULATION[i]) / 10
             for i in range(len(YEARS) - 1)]
    print("average growth rate in each decade (% a year):")
    print("  " + "  ".join(f"{YEARS[i]}s {100 * g:.1f}" for i, g in
                           enumerate(rates[:4])))
    print("  " + "  ".join(f"{YEARS[i]}s {100 * g:.1f}" for i, g in
                           enumerate(rates[4:], start=4)))
    print("The exponential model assumes a constant rate. The rate peaked in the")
    print("1960s and has fallen since (decade rates from rounded data are rough),")
    print("so its forecast overshoots. The line (a fixed yearly increase)")
    print("undershoots.")
    print()
    print("Epistemic status: numerical computation on rounded estimates (which")
    print("are themselves revised between UN editions). The comparison shows how")
    print("two models fitted to the same past data can forecast differently; it")
    print("is not a demographic projection.")


if __name__ == "__main__":
    main()
