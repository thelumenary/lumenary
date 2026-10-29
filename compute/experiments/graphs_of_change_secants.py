"""A curved graph: average speeds of a falling capsule over shrinking intervals.

In the idealised model of a research capsule released from rest in a drop
tower's evacuated tube (no air resistance), it has fallen d(t) = 4.9 t^2
metres after t seconds. Its distance-time graph is curved, so the average
rate of change depends on the interval. The experiment computes, with exact
fractions, the average speed in each of the first four seconds, then the
average speed over intervals [2, 2 + h] for shrinking h (and for intervals
ending at 2), and compares the results with the exact formula 19.6 + 4.9h
proved in the lesson. As h shrinks the average speeds approach 19.6 m/s: a
preview of the instantaneous speed (derivative).
"""

from fractions import Fraction as F

EXPERIMENT = {
    "id": "graphs_of_change_secants",
    "title": "A falling capsule: average speeds over shrinking intervals",
    "evidence": ["exact"],
    "lessons": ["graphs-of-change"],
    "summary": (
        "For the idealised falling-capsule model d(t) = 4.9 t^2, computes exact "
        "average speeds second by second, then over the intervals [2, 2 + h] "
        "for h = 1, 1/10, 1/100, 1/1000 and their negatives, checking each "
        "against the formula 19.6 + 4.9h. The values approach 19.6 m/s, a "
        "preview of instantaneous speed; finitely many h prove no limit."
    ),
    "packages": [],
}

G_HALF = F(49, 10)  # 4.9 m/s^2, half the acceleration due to gravity


def fallen(t):
    """Distance fallen after t seconds in the model d(t) = 4.9 t^2."""
    return G_HALF * F(t) ** 2


def avg_speed(a, b):
    """Average rate of change of d between times a and b (a != b)."""
    if a == b:
        raise ValueError("the two times must differ")
    return (fallen(b) - fallen(a)) / (F(b) - F(a))


def formula(h):
    """The lesson's exact formula for the average speed over [2, 2 + h]."""
    return F(98, 5) + G_HALF * F(h)


def show(x):
    """A fraction with a decimal beside it, e.g. '1029/50 (= 20.58)'."""
    x = F(x)
    if x.denominator == 1:
        return str(x)
    return f"{x} (= {float(x):.4f})"


def main():
    print("1. Second by second (exact values; all are whole tenths)")
    for t in range(1, 5):
        print(f"   after {t} s: fallen {float(fallen(t)):5.1f} m;"
              f" average speed during second {t}:"
              f" {float(avg_speed(t - 1, t)):4.1f} m/s")
    print("   The rate grows each second: a curved, steepening graph.")
    print()
    print("2. Average speed over the interval from t = 2 to t = 2 + h")
    hs = [F(1), F(1, 10), F(1, 100), F(1, 1000)]
    for h in hs + [-h for h in hs]:
        rate = avg_speed(2, 2 + h)
        mark = "matches" if rate == formula(h) else "DIFFERS"
        print(f"   h = {str(h):>7}: {show(rate):<26} {mark} 19.6 + 4.9h")
    print("   As h shrinks (from either side) the values close in on 19.6.")
    print()
    print("Epistemic status: exact arithmetic in an idealised model (no air")
    print("resistance). Each value agrees with the formula 19.6 + 4.9h, which")
    print("the lesson proves by algebra for every h other than 0; that formula,")
    print("not these eight values, shows the averages approach 19.6 m/s.")


if __name__ == "__main__":
    main()
