"""Centre and spread, and what one extreme value does to them.

For the lesson's data (minutes taken to get to school by 15 students) this
experiment computes the mean, median, mode, range, quartiles and
interquartile range exactly, using the lesson's convention for quartiles
(medians of the lower and upper halves, leaving out the median when the
number of values is odd). It then makes the largest value more and more
extreme and records which summaries move. Two side notes: other quartile
conventions (Python's own) give slightly different answers on some data,
and two bus routes with the same mean can have very different spreads.
"""

import statistics
from fractions import Fraction

EXPERIMENT = {
    "id": "statistics_intro_outliers",
    "title": "Mean, median and spread: what an outlier changes",
    "evidence": ["exact"],
    "lessons": ["statistics-intro"],
    "summary": (
        "Computes mean, median, mode, range, quartiles and IQR exactly for a "
        "class's travel times, then makes the largest value ever more extreme: "
        "the mean and range move, the median and IQR do not. Also compares "
        "quartile conventions (they can disagree) and two bus routes with the "
        "same mean but different spreads. Exact calculations on small, "
        "illustrative data sets."
    ),
    "packages": [],
}

CLASS_A = [5, 8, 10, 10, 12, 12, 12, 15, 15, 18, 20, 20, 25, 30, 45]
ROUTE_1 = [9, 10, 10, 11, 9, 10, 11, 10, 9, 11]
ROUTE_2 = [2, 18, 5, 15, 10, 1, 19, 8, 12, 10]


def mean(values):
    """Exact mean as a Fraction."""
    if not values:
        raise ValueError("no data")
    return Fraction(sum(values), len(values))


def median(values):
    """Middle value of the sorted data, or the mean of the two middle ones."""
    s = sorted(values)
    n = len(s)
    if n == 0:
        raise ValueError("no data")
    if n % 2 == 1:
        return Fraction(s[n // 2])
    return Fraction(s[n // 2 - 1] + s[n // 2], 2)


def quartiles(values):
    """(Q1, Q3): medians of the lower and upper halves (median excluded)."""
    s = sorted(values)
    n = len(s)
    if n < 2:
        raise ValueError("need at least two values")
    return median(s[: n // 2]), median(s[(n + 1) // 2:])


def summary(values):
    """Dictionary of the lesson's summaries of centre and spread."""
    q1, q3 = quartiles(values)
    return {
        "mean": mean(values),
        "median": median(values),
        "modes": statistics.multimode(values),
        "range": max(values) - min(values),
        "Q1": q1,
        "Q3": q3,
        "IQR": q3 - q1,
    }


def outliers(values):
    """Values more than 1.5 IQR below Q1 or above Q3 (Tukey's rule)."""
    q1, q3 = quartiles(values)
    spread = q3 - q1
    low, high = q1 - Fraction(3, 2) * spread, q3 + Fraction(3, 2) * spread
    return [v for v in values if v < low or v > high]


def show(x):
    """A Fraction as an integer, or a decimal to 2 places."""
    x = Fraction(x)
    return str(x.numerator) if x.denominator == 1 else f"{float(x):.2f}"


def main():
    s = summary(CLASS_A)
    print("Minutes to school, 15 students:", " ".join(map(str, CLASS_A)))
    print(f"  mean {show(s['mean'])}  median {show(s['median'])}  mode "
          f"{s['modes']}  range {s['range']}")
    print(f"  Q1 {show(s['Q1'])}  Q3 {show(s['Q3'])}  IQR {show(s['IQR'])}"
          f"  outliers (1.5 IQR rule): {outliers(CLASS_A)}")
    print()
    print("Make the largest value more extreme:")
    print("  largest   mean    median   range   IQR")
    for big in (45, 90, 180, 900):
        data = CLASS_A[:-1] + [big]
        t = summary(data)
        print(f"  {big:7d}  {show(t['mean']):>6}   {show(t['median']):>5}"
              f"   {t['range']:5d}   {show(t['IQR']):>3}")
    print()
    r2 = sorted(ROUTE_2)
    py_ex = statistics.quantiles(r2, n=4, method="exclusive")
    py_in = statistics.quantiles(r2, n=4, method="inclusive")
    q1, q3 = quartiles(r2)
    print("Quartile conventions differ. Route 2, sorted:")
    print("  " + " ".join(map(str, r2)))
    print(f"  halves (this lesson): Q1 = {show(q1)}, Q3 = {show(q3)}")
    print(f"  Python 'exclusive':   Q1 = {py_ex[0]:g}, Q3 = {py_ex[2]:g}")
    print(f"  Python 'inclusive':   Q1 = {py_in[0]:g}, Q3 = {py_in[2]:g}")
    print()
    print("Two bus routes, waiting times over 10 days (minutes):")
    for name, data in (("route 1", ROUTE_1), ("route 2", ROUTE_2)):
        t = summary(data)
        print(f"  {name}: mean {show(t['mean'])}, median {show(t['median'])},"
              f" range {t['range']}, IQR {show(t['IQR'])}")
    print("  Same centre, very different reliability.")
    print()
    print("Epistemic status: exact arithmetic on small illustrative data sets.")
    print("That the median ignores the largest value is proved in the lesson")
    print("(for three or more values); this run only illustrates it, and the")
    print("IQR's behaviour here depends on the data. Quartiles also depend on")
    print("a chosen convention.")


if __name__ == "__main__":
    main()
