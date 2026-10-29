"""Two "best centres": the mean and the median as answers to different questions.

Pick a number c to stand for the whole data set. If we measure the error
by the total squared distance  sum (x - c)^2,  the best c is the mean. If we
measure it by the total distance  sum |x - c|,  the best c is the median.
This experiment scans c over a fine grid (exact fractions) for the lesson's
data, finds where each total is smallest, and checks the identity
sum (x - c)^2 = sum (x - mean)^2 + n (mean - c)^2 at every grid point.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "statistics_intro_best_centre",
    "title": "The mean and the median as best centres",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["statistics-intro"],
    "summary": (
        "Scans every candidate centre c from 0 to 50 in steps of 1/4 for the "
        "lesson's data, with exact fractions: the total squared distance is "
        "smallest at the grid point nearest the mean, the total distance is "
        "smallest exactly at the median, and the identity sum (x - c)^2 = "
        "sum (x - mean)^2 + n (mean - c)^2 holds at all 201 points. A finite "
        "scan; the lesson proves both facts for every c."
    ),
    "packages": [],
}

DATA = [5, 8, 10, 10, 12, 12, 12, 15, 15, 18, 20, 20, 25, 30, 45]


def total_distance(values, c):
    """Sum of |x - c|."""
    return sum(abs(Fraction(x) - c) for x in values)


def total_squared_distance(values, c):
    """Sum of (x - c)^2."""
    return sum((Fraction(x) - c) ** 2 for x in values)


def grid(low, high, step):
    """Exact grid low, low + step, ..., high."""
    count = int((Fraction(high) - Fraction(low)) / Fraction(step))
    return [Fraction(low) + k * Fraction(step) for k in range(count + 1)]


def minimisers(values, cost, candidates):
    """The candidates at which cost(values, c) is smallest."""
    costs = [(cost(values, c), c) for c in candidates]
    best = min(k for k, _ in costs)
    return [c for k, c in costs if k == best]


def identity_holds(values, candidates):
    """Check sum (x-c)^2 == sum (x-m)^2 + n (m-c)^2 at every candidate."""
    n = len(values)
    m = Fraction(sum(values), n)
    base = total_squared_distance(values, m)
    return all(total_squared_distance(values, c) == base + n * (m - c) ** 2
               for c in candidates)


def show(x):
    """A Fraction as an integer or a decimal to 2 places."""
    x = Fraction(x)
    return str(x.numerator) if x.denominator == 1 else f"{float(x):.2f}"


def main():
    m = Fraction(sum(DATA), len(DATA))
    print("Data (minutes to school):", " ".join(map(str, DATA)))
    print(f"mean = {m} = {show(m)}, median = 15")
    print()
    print("     c    total distance   total squared distance")
    for c in (10, 15, m, 20, 25):
        print(f"  {show(c):>5}   {show(total_distance(DATA, c)):>14}   "
              f"{show(total_squared_distance(DATA, c)):>22}")
    print()
    cands = grid(0, 50, Fraction(1, 4))
    print(f"Scanning c = 0, 1/4, 1/2, ..., 50 ({len(cands)} values):")
    best_abs = minimisers(DATA, total_distance, cands)
    best_sq = minimisers(DATA, total_squared_distance, cands)
    print(f"  smallest total distance at c = {[show(c) for c in best_abs]}")
    print(f"  smallest total squared distance at c = "
          f"{[show(c) for c in best_sq]}")
    print("    (the grid point nearest to the mean)")
    print(f"  identity checked at every grid point: "
          f"{identity_holds(DATA, cands)}")
    even = [1, 2, 6, 10]
    flat = minimisers(even, total_distance, grid(0, 12, Fraction(1, 2)))
    print(f"For {even} (even count) every c from {show(flat[0])} to "
          f"{show(flat[-1])} ties:")
    print("  the total distance is flat between the two middle values.")
    print()
    print("Epistemic status: exact arithmetic, exhaustive over a finite grid")
    print("of candidates. The lesson proves that the mean minimises the total")
    print("squared distance for every real c (the identity above), and why")
    print("the median minimises the total distance.")


if __name__ == "__main__":
    main()
