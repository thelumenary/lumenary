"""A perfect fit that predicts nonsense: overfitting a cooling cup of tea.

We generate SYNTHETIC data from Newton's law of cooling,
T(t) = 25 + 60 e^(-0.1 t) degrees C, add small seeded random "measurement
errors", and fit three models to the eight readings at t = 0, 2, ..., 14
minutes: a straight line, Newton's model (fitted through ln(T - 25)), and the
degree-7 polynomial that passes through every reading exactly. Then we ask
each model about t = 20 and t = 30 minutes, where the true curve is known.
"""

import math
import random

EXPERIMENT = {
    "id": "modelling_with_functions_overfitting",
    "title": "A perfect fit that predicts nonsense",
    "evidence": ["experimental", "numerical"],
    "lessons": ["modelling-with-functions"],
    "summary": (
        "Fits a line, Newton's cooling law and an exact-fit degree-7 polynomial "
        "to eight synthetic, slightly noisy temperature readings, then compares "
        "their predictions beyond the data with the known true curve. The exact "
        "fit has zero error on the data and absurd forecasts. One seeded example."
    ),
    "packages": [],
}

ROOM = 25.0


def true_temperature(t):
    """The synthetic 'truth': Newton's law with T0 = 85 C, room 25 C, k = 0.1."""
    return ROOM + 60.0 * math.exp(-0.1 * t)


def synthetic_readings(seed=7, noise=0.4):
    """Eight readings at t = 0, 2, ..., 14 with seeded Gaussian noise."""
    rng = random.Random(seed)
    ts = list(range(0, 16, 2))
    return ts, [true_temperature(t) + rng.gauss(0, noise) for t in ts]


def fit_line(xs, ys):
    """Least-squares line y = m x + c; returns (m, c)."""
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    m = (sum((x - mx) * (y - my) for x, y in zip(xs, ys))
         / sum((x - mx) ** 2 for x in xs))
    return m, my - m * mx


def fit_newton(ts, temps):
    """Fit T = ROOM + D e^(-k t) via a line through (t, ln(T - ROOM))."""
    slope, intercept = fit_line(ts, [math.log(T - ROOM) for T in temps])
    return math.exp(intercept), -slope


def lagrange(xs, ys, x):
    """Value at x of the polynomial of degree < len(xs) through all points."""
    total = 0.0
    for i, (xi, yi) in enumerate(zip(xs, ys)):
        term = yi
        for j, xj in enumerate(xs):
            if j != i:
                term *= (x - xj) / (xi - xj)
        total += term
    return total


def rms(errors):
    """Root-mean-square of a list of errors."""
    return math.sqrt(sum(e * e for e in errors) / len(errors))


def main():
    ts, temps = synthetic_readings()
    m, c = fit_line(ts, temps)
    d, k = fit_newton(ts, temps)
    models = {
        "line": lambda t: m * t + c,
        "Newton": lambda t: ROOM + d * math.exp(-k * t),
        "degree 7": lambda t: lagrange(ts, temps, t),
    }
    print("SYNTHETIC readings (minutes, degrees C):")
    print("  " + "  ".join(f"{t}:{T:.1f}" for t, T in zip(ts, temps)))
    print(f"Newton fit: T = 25 + {d:.1f} e^(-{k:.4f} t)  (truth: 60, 0.1)")
    print()
    print(f"{'model':>9}  {'RMS error on data':>17}  {'T(20)':>8}  {'T(30)':>8}")
    for name, f in models.items():
        err = rms([f(t) - T for t, T in zip(ts, temps)])
        print(f"{name:>9}  {err:17.3f}  {f(20):8.1f}  {f(30):8.1f}")
    print(f"{'truth':>9}  {'':17}  {true_temperature(20):8.1f}"
          f"  {true_temperature(30):8.1f}")
    print()
    print("The degree-7 polynomial fits the data perfectly (error 0) and")
    print("forecasts temperatures no cup of tea could reach. The line looks")
    print("reasonable on the data but predicts the tea will cool below room")
    print("temperature. Newton's model, which encodes why tea cools, has small")
    print("errors on the data and forecasts well.")
    print()
    print("Epistemic status: one experiment on synthetic data with a known")
    print("truth and a fixed random seed. It illustrates overfitting and")
    print("extrapolation risk; it does not measure how often such models fail,")
    print("and real cooling also depends on things this model ignores.")


if __name__ == "__main__":
    main()
