"""Rebuild Aryabhata's sine table (499 CE) and compare it with modern values.

The Aryabhatiya lists 24 sine differences for steps of 3 3/4 degrees on a
circle of radius R = 3438 (about the number of arc-minutes in a radian), so
that R sin(3.75 n deg) is the sum of the first n differences. We rebuild the
table from scratch the way a table maker could: start from sin 30 = 1/2,
halve the angle three times with sin(x/2)^2 = (1 - cos x)/2, then step along
with the exact recurrence sin((n+1)h) = 2 cos h sin(nh) - sin((n-1)h).
"""

import math

EXPERIMENT = {
    "id": "trigonometry_aryabhata_table",
    "title": "Aryabhata's sine table, rebuilt",
    "evidence": ["numerical"],
    "lessons": ["trigonometry"],
    "summary": (
        "Rebuilds R sin(3.75 n deg) for R = 3438 and n = 1..24 from sin 30 = 1/2 "
        "using only half-angle formulas and the recurrence sin((n+1)h) = "
        "2 cos h sin(nh) - sin((n-1)h), and compares the result with the table "
        "of sine differences in the Aryabhatiya (499 CE) and with math.sin. "
        "Floating-point evidence about one historical table."
    ),
    "packages": [],
}

#: The 24 sine differences of the Aryabhatiya (Gitikapada), radius 3438.
ARYABHATA_DIFFERENCES = [225, 224, 222, 219, 215, 210, 205, 199, 191, 183,
                         174, 164, 154, 143, 131, 119, 106, 93, 79, 65, 51,
                         37, 22, 7]
RADIUS = 3438


def half_angle(sin_x, cos_x):
    """Return (sin(x/2), cos(x/2)) for 0 <= x <= 180 degrees."""
    return math.sqrt((1 - cos_x) / 2), math.sqrt((1 + cos_x) / 2)


def step_sine_and_cosine():
    """sin and cos of 3.75 deg, from sin 30 = 1/2 by three half-angle steps."""
    s, c = 0.5, math.sqrt(3) / 2  # 30 degrees
    for _ in range(3):  # 15, 7.5, 3.75 degrees
        s, c = half_angle(s, c)
    return s, c


def sine_table(radius, steps):
    """[R sin(n h) for n = 0..steps] with h = 3.75 deg, by the recurrence."""
    s1, c1 = step_sine_and_cosine()
    table = [0.0, radius * s1]
    for _ in range(steps - 1):
        table.append(2 * c1 * table[-1] - table[-2])
    return table


def cumulative(differences):
    """Running sums: the table entries encoded by a list of differences."""
    out, total = [], 0
    for d in differences:
        total += d
        out.append(total)
    return out


def main():
    rebuilt = sine_table(RADIUS, 24)
    ancient = cumulative(ARYABHATA_DIFFERENCES)
    print("R sin(3.75 n deg), R = 3438: rebuilt / Aryabhata / difference")
    for n in range(1, 13):
        left = f"{3.75 * n:6.2f} {rebuilt[n]:7.1f} {ancient[n - 1]:5d}"
        left += f" {ancient[n - 1] - rebuilt[n]:+5.1f}"
        m = n + 12
        right = f"{3.75 * m:6.2f} {rebuilt[m]:7.1f} {ancient[m - 1]:5d}"
        right += f" {ancient[m - 1] - rebuilt[m]:+5.1f}"
        print(f"{left}  |{right}")
    worst = max(abs(a - r) for a, r in zip(ancient, rebuilt[1:]))
    drift = max(abs(rebuilt[n] - RADIUS * math.sin(math.radians(3.75 * n)))
                for n in range(25))
    exact = sum(a == round(r) for a, r in zip(ancient, rebuilt[1:]))
    print(f"Largest gap between Aryabhata's table and ours: {worst:.2f}")
    print(f"Entries equal to our value rounded to a whole number: {exact}/24")
    print(f"Largest gap between the recurrence and math.sin: {drift:.1e}")
    print(f"R sin 90 deg should be R = {RADIUS}: rebuilt {rebuilt[24]:.4f}")
    print()
    print("Epistemic status: numerical. The recurrence and half-angle steps")
    print("are exact identities; our only errors are floating-point rounding")
    print("(shown above). Of Aryabhata's 24 whole-number entries, 19 are our")
    print("values rounded and the other 5 are one unit away: errors below")
    print("0.03% of R. How Aryabhata computed his table is a question for")
    print("historians, which this program does not answer.")


if __name__ == "__main__":
    main()
