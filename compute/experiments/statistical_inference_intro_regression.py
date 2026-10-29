"""Least squares, correlation and their limits: Anscombe's quartet and more.

Francis Anscombe's four data sets (1973) share their means, their variances,
their correlation r = 0.816 and their least-squares line y = 3.00 + 0.500x to
two or three decimals, yet look completely different when plotted - so a
summary is no substitute for a picture. All statistics are computed exactly
with fractions from the lesson's formulas Sxx, Sxy, Syy. Then y = x^2 on a
symmetric range has r = 0 although y is a function of x, and a simulated
town shows ice-cream sales and sea rescues correlated only because both
follow the temperature: the correlation of what is left after removing
temperature's linear effect is close to zero.
"""

import math
import random
from fractions import Fraction

EXPERIMENT = {
    "id": "statistical_inference_intro_regression",
    "title": "Least squares and correlation: Anscombe's quartet and confounding",
    "evidence": ["exact", "experimental"],
    "lessons": ["statistical-inference-intro"],
    "summary": (
        "Computes exactly, with fractions, the means, variances, correlation and "
        "least-squares line of Anscombe's quartet: four data sets with the same "
        "summaries (r = 0.816, y = 3.00 + 0.500x) but very different shapes. "
        "Shows r = 0 for y = x^2 on a symmetric range, and simulates (seeded) a "
        "confounded correlation between ice-cream sales and sea rescues that "
        "vanishes once temperature is accounted for."
    ),
    "packages": [],
}

X123 = [10, 8, 13, 9, 11, 14, 6, 4, 12, 7, 5]
ANSCOMBE = {
    "I": (X123, ["8.04", "6.95", "7.58", "8.81", "8.33", "9.96", "7.24",
                 "4.26", "10.84", "4.82", "5.68"]),
    "II": (X123, ["9.14", "8.14", "8.74", "8.77", "9.26", "8.10", "6.13",
                  "3.10", "9.13", "7.26", "4.74"]),
    "III": (X123, ["7.46", "6.77", "12.74", "7.11", "7.81", "8.84", "6.08",
                   "5.39", "8.15", "6.42", "5.73"]),
    "IV": ([8, 8, 8, 8, 8, 8, 8, 19, 8, 8, 8],
           ["6.58", "5.76", "7.71", "8.84", "8.47", "7.04", "5.25", "12.50",
            "5.56", "7.91", "6.89"]),
}


def sums(x, y):
    """(mean x, mean y, Sxx, Sxy, Syy), exactly if the data are Fractions."""
    n = len(x)
    mx, my = sum(x, Fraction(0)) / n, sum(y, Fraction(0)) / n
    sxx = sum((a - mx) ** 2 for a in x)
    sxy = sum((a - mx) * (b - my) for a, b in zip(x, y))
    syy = sum((b - my) ** 2 for b in y)
    return mx, my, sxx, sxy, syy


def least_squares(x, y):
    """(intercept, slope) of the least-squares line: b = Sxy/Sxx."""
    mx, my, sxx, sxy, _ = sums(x, y)
    slope = sxy / sxx
    return my - slope * mx, slope


def correlation(x, y):
    """r = Sxy / sqrt(Sxx Syy) (a float: the square root is irrational)."""
    _, _, sxx, sxy, syy = sums(x, y)
    return float(sxy) / math.sqrt(float(sxx) * float(syy))


def residuals(x, y):
    """y minus the least-squares prediction, for each point."""
    a, b = least_squares(x, y)
    return [v - (a + b * u) for u, v in zip(x, y)]


def confounded_town(rng, days):
    """Temperatures and two quantities that each depend only on them."""
    temp = [rng.uniform(15, 35) for _ in range(days)]
    ice = [20 * t + rng.gauss(0, 60) for t in temp]
    rescues = [0.3 * t + rng.gauss(0, 1.5) for t in temp]
    return temp, ice, rescues


def main():
    print("Anscombe's quartet (exact arithmetic, rounded for printing)")
    print("  set   mean x  mean y   var x   var y      r     line")
    for name, (x, ys) in ANSCOMBE.items():
        y = [Fraction(v) for v in ys]
        mx, my, sxx, _, syy = sums(x, y)
        a, b = least_squares(x, y)
        print(f"  {name:>3}   {float(mx):6.2f}  {float(my):6.2f}  "
              f"{float(sxx / 10):6.2f}  {float(syy / 10):6.2f}  "
              f"{correlation(x, y):6.3f}   y = {float(a):.2f} + "
              f"{float(b):.3f}x")
    print("Same summaries; plotted, they look nothing alike.")
    print()
    xs = list(range(-3, 4))
    sxy = sums(xs, [v * v for v in xs])[3]
    print(f"y = x^2 for x = -3..3: Sxy = {sxy}, so r = 0 exactly.")
    print("  No linear association, yet y is completely determined by x.")
    print()
    temp, ice, rescues = confounded_town(random.Random(1973), 730)
    print("A simulated town, 730 days:")
    print(f"  r(ice-cream sales, sea rescues) = {correlation(ice, rescues):.2f}")
    r_left = correlation(residuals(temp, ice), residuals(temp, rescues))
    print(f"  after removing temperature's linear effect from both: "
          f"r = {r_left:.2f}")
    print()
    print("Epistemic status: the quartet's statistics are exact computations")
    print("from the published data; the town is a simulation built so that")
    print("temperature causes both quantities. Correlation alone could not")
    print("have told us that.")


if __name__ == "__main__":
    main()
