"""Measuring with different units, and what gaps and overlaps do.

Part 1 measures six objects (whole centimetres, as in the lesson's ruler
widget) with three units: small paper clips (3 cm), large paper clips
(5 cm) and a child's hand span (12 cm). Each result is "exactly k" or
"between k and k + 1" units, and the smaller unit always gives the bigger
number. Part 2 simulates careless measuring: clips laid along a 15 cm pencil
with small random gaps, or with small random overlaps, counting the clips
that fit before the end. Gaps can only make the count too small, and overlaps
can only make it too big (or, by luck, right).

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from collections import Counter
import random
import textwrap

EXPERIMENT = {
    "id": "measurement_units_and_gaps",
    "title": "Units, gaps and overlaps: measuring a pencil in paper clips",
    "evidence": ["exact", "exhaustive-finite", "experimental"],
    "lessons": ["measurement"],
    "summary": (
        "Measures six objects in three units exactly, checks that a smaller "
        "unit never gives a smaller count for every whole length up to 100 cm "
        "and every pair of units up to 20 cm, then simulates 1,000 careless "
        "measurements of a 15 cm pencil with seeded random gaps or overlaps. "
        "The simulation is experimental evidence; the lesson explains why gaps "
        "can never raise the count and overlaps can never lower it."
    ),
    "packages": [],
}

#: Object lengths in whole centimetres (the same as the ruler widget).
OBJECTS = {"key": 5, "leaf": 7, "crayon": 9, "feather": 11, "spoon": 13,
           "pencil": 15}
#: Units, in centimetres.
UNITS = {"small clip": 3, "large clip": 5, "hand span": 12}


def measure(length, unit):
    """Return (whole units that fit, centimetres left over)."""
    if unit <= 0:
        raise ValueError("a unit must have a positive length")
    return divmod(length, unit)


def describe(length, unit):
    """Say the measurement in words, honestly: 'exactly 3' or '3 to 4'."""
    whole, left = measure(length, unit)
    if left == 0:
        return f"exactly {whole}"
    if whole == 0:
        return "less than 1"
    return f"{whole} to {whole + 1}"


def smaller_unit_never_smaller_count(max_length=100, max_unit=20):
    """Check: if unit u < v then length // u >= length // v, for all cases."""
    return all(
        n // u >= n // v
        for n in range(max_length + 1)
        for u in range(1, max_unit + 1)
        for v in range(u + 1, max_unit + 1)
    )


def clips_that_fit(length, unit, spacings):
    """Lay clips from 0; after each clip move on by the next spacing.

    A positive spacing is a gap, a negative one an overlap. Return how many
    whole clips fit before the end of the object.
    """
    start, count = 0.0, 0
    for space in spacings:
        if start + unit > length + 1e-9:
            break
        count += 1
        start += unit + space
    return count


def simulate(length, unit, low, high, trials, seed):
    """Count clips for many measurers whose spacings are random in [low, high]."""
    rng = random.Random(seed)
    results = Counter()
    for _ in range(trials):
        spacings = [rng.uniform(low, high) for _ in range(4 * length)]
        results[clips_that_fit(length, unit, spacings)] += 1
    return dict(sorted(results.items()))


def main():
    print("1. Six objects measured in three units (exact):")
    print("   object    cm   " + "".join(f"{u:<13}" for u in UNITS).rstrip())
    for name, cm in OBJECTS.items():
        cells = "".join(f"{describe(cm, u):<13}" for u in UNITS.values())
        print(f"   {name:<8} {cm:3d}   {cells.rstrip()}")
    ok = smaller_unit_never_smaller_count()
    print("   A smaller unit never gives a smaller count, for every length")
    print(f"   0..100 cm and every pair of units 1..20 cm: {ok}")
    print()
    print("2. A 15 cm pencil measured with 3 cm clips by 1,000 measurers:")
    careful = clips_that_fit(15, 3, [0.0] * 10)
    print(f"   careful, no gaps or overlaps: {careful} clips")
    for label, low, high in [("gaps of 0.2-1 cm", 0.2, 1.0),
                             ("overlaps of 0.2-1 cm", -1.0, -0.2)]:
        counts = simulate(15, 3, low, high, 1000, seed=2024)
        shown = ", ".join(f"{k} clips: {n}" for k, n in counts.items())
        print(f"   {label:<21} {shown}")
    print()
    print(textwrap.fill(
        "Epistemic status: part 1 is exact arithmetic, and the check that a "
        "smaller unit never gives a smaller count is exhaustive for the "
        "lengths and units listed (not for all numbers). Part 2 is a seeded "
        "simulation, experimental evidence only; why gaps can never raise the "
        "count and overlaps can never lower it is explained in the lesson.",
        width=78,
    ))


if __name__ == "__main__":
    main()
