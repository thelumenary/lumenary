"""Least squares by the normal equations, and why you must look at residuals.

Part 1 fits a straight line to a small (illustrative) data set of spring
extensions by solving the normal equations X^T X b = X^T y exactly in
rational arithmetic, and checks the answer against numpy's least-squares
solver. Part 2 uses Anscombe's quartet (1973): four data sets with the same
means, variances, correlation and fitted line, but completely different
residual patterns - curvature, an outlier, and a single point of high
leverage.
"""

from fractions import Fraction

import numpy as np

EXPERIMENT = {
    "id": "statistics_regression_residuals",
    "title": "Normal equations and Anscombe's quartet: fit, then check residuals",
    "evidence": ["exact", "numerical"],
    "lessons": ["statistics"],
    "summary": (
        "Solves the normal equations for a straight-line fit exactly with fractions and "
        "compares with numpy.linalg.lstsq; residuals sum to zero and are orthogonal to x. "
        "Then fits Anscombe's four data sets: identical slope, intercept, correlation and "
        "R^2 to two decimals, yet residual diagnostics reveal curvature, an outlier and "
        "a high-leverage point."
    ),
    "packages": ["numpy"],
}

#: Illustrative data: mass on a spring (hundreds of grams) and extension (cm).
MASS = [0, 1, 2, 3, 4, 5]
EXTENSION = ["0.1", "2.0", "4.1", "5.9", "8.2", "9.9"]

#: Anscombe, "Graphs in statistical analysis", The American Statistician (1973).
ANSCOMBE_X = [10, 8, 13, 9, 11, 14, 6, 4, 12, 7, 5]
ANSCOMBE = {
    "I": (ANSCOMBE_X, [8.04, 6.95, 7.58, 8.81, 8.33, 9.96, 7.24, 4.26, 10.84,
                       4.82, 5.68]),
    "II": (ANSCOMBE_X, [9.14, 8.14, 8.74, 8.77, 9.26, 8.10, 6.13, 3.10, 9.13,
                        7.26, 4.74]),
    "III": (ANSCOMBE_X, [7.46, 6.77, 12.74, 7.11, 7.81, 8.84, 6.08, 5.39,
                         8.15, 6.42, 5.73]),
    "IV": ([8, 8, 8, 8, 8, 8, 8, 19, 8, 8, 8],
           [6.58, 5.76, 7.71, 8.84, 8.47, 7.04, 5.25, 12.50, 5.56, 7.91, 6.89]),
}


def normal_equations_line(xs, ys):
    """Exact (intercept, slope) solving X^T X b = X^T y for X = [1, x].

    The 2 x 2 system [[n, Sx], [Sx, Sxx]] b = [Sy, Sxy] is solved by
    Cramer's rule in rational arithmetic.
    """
    xs = [Fraction(x) for x in xs]
    ys = [Fraction(y) for y in ys]
    n = len(xs)
    sx, sy = sum(xs), sum(ys)
    sxx = sum(x * x for x in xs)
    sxy = sum(x * y for x, y in zip(xs, ys))
    det = n * sxx - sx * sx
    if det == 0:
        raise ValueError("all x values are equal: the slope is not determined")
    return (sxx * sy - sx * sxy) / det, (n * sxy - sx * sy) / det


def residuals(xs, ys, intercept, slope):
    """y_i - (intercept + slope x_i)."""
    return [Fraction(y) - (intercept + slope * Fraction(x))
            for x, y in zip(xs, ys)]


def summary(xs, ys):
    """Mean of x, mean of y, slope, intercept, correlation r and R^2."""
    x, y = np.asarray(xs, float), np.asarray(ys, float)
    design = np.column_stack([np.ones_like(x), x])
    (b0, b1), *_ = np.linalg.lstsq(design, y, rcond=None)
    r = float(np.corrcoef(x, y)[0, 1])
    return float(x.mean()), float(y.mean()), float(b1), float(b0), r, r * r


def diagnostics(xs, ys):
    """Largest |residual|, its index, and the largest leverage h_ii."""
    x, y = np.asarray(xs, float), np.asarray(ys, float)
    design = np.column_stack([np.ones_like(x), x])
    hat = design @ np.linalg.inv(design.T @ design) @ design.T
    b = np.linalg.solve(design.T @ design, design.T @ y)
    res = y - design @ b
    i = int(np.argmax(np.abs(res)))
    return float(abs(res[i])), i, float(np.max(np.diag(hat)))


def curvature(xs, ys):
    """Correlation between residuals and (x - mean x)^2: large if curved."""
    x, y = np.asarray(xs, float), np.asarray(ys, float)
    _, _, b1, b0, _, _ = summary(xs, ys)
    res = y - (b0 + b1 * x)
    sq = (x - x.mean()) ** 2
    if np.std(sq) == 0:
        return 0.0
    return float(np.corrcoef(res, sq)[0, 1])


def main():
    b0, b1 = normal_equations_line(MASS, EXTENSION)
    res = residuals(MASS, EXTENSION, b0, b1)
    print("Part 1: spring extension (cm) against mass (100 g)")
    print(f"  exact normal-equation fit: y = {b0} + {b1} x"
          f" = {float(b0):.4f} + {float(b1):.4f} x")
    _, _, nb1, nb0, _, r2 = summary(MASS, [float(e) for e in EXTENSION])
    print(f"  numpy lstsq:               y = {nb0:.4f} + {nb1:.4f} x,"
          f" R^2 = {r2:.4f}")
    print(f"  sum of residuals = {sum(res)}, sum of x * residual ="
          f" {sum(Fraction(x) * e for x, e in zip(MASS, res))}")
    print()
    print("Part 2: Anscombe's quartet")
    print(" set  mean x  mean y  slope  intercept     r   R^2 | max|res|"
          " leverage curve")
    for name, (xs, ys) in ANSCOMBE.items():
        mx, my, s, c, r, r2 = summary(xs, ys)
        big, _, lev = diagnostics(xs, ys)
        print(f" {name:>3} {mx:7.2f} {my:7.2f} {s:6.3f} {c:10.2f} {r:5.3f}"
              f" {r2:5.2f} | {big:8.2f} {lev:8.2f} {curvature(xs, ys):5.2f}")
    print("Same summary statistics; different stories. II is curved (residuals")
    print("track (x - mean)^2), III has one outlier, and in IV a single point")
    print("with leverage 1 determines the slope by itself.")
    print()
    print("Epistemic status: part 1 is exact rational arithmetic, confirmed")
    print("numerically; part 2 is floating-point computation on published data.")
    print("The diagnostics illustrate what residual plots show; they are not")
    print("formal tests, and the spring data are illustrative, not measured.")


if __name__ == "__main__":
    main()
