"""In high dimensions, two random vectors are almost perpendicular.

We draw pairs of random vectors in R^n (each coordinate an independent
standard normal number, seeded) and measure the angle between them with the
dot product formula cos(theta) = u.v / (|u| |v|). In the plane the angle is
spread evenly between 0 and 180 degrees; as n grows it piles up near 90
degrees. Theory says cos(theta) has mean 0 and variance exactly 1/n, so its
standard deviation is 1/sqrt(n): we compare the sample with that prediction.
"""

import math
import random
import statistics

EXPERIMENT = {
    "id": "vectors_random_angles",
    "title": "Random vectors in high dimensions are nearly perpendicular",
    "evidence": ["statistical"],
    "lessons": ["vectors"],
    "summary": (
        "Samples 300 pairs of random Gaussian vectors in dimensions 2, 3, 10, "
        "100 and 1000 (seeded), computes their angles with the dot product, and "
        "compares the spread of cos(theta) with the exact value 1/sqrt(n) of its "
        "standard deviation. Statistical evidence from finite samples."
    ),
    "packages": [],
}


def random_vector(n, rng):
    """A vector of n independent standard normal coordinates."""
    return [rng.gauss(0.0, 1.0) for _ in range(n)]


def cos_angle(u, v):
    """cos of the angle between non-zero vectors u and v."""
    dot = sum(a * b for a, b in zip(u, v))
    return dot / math.sqrt(sum(a * a for a in u) * sum(b * b for b in v))


def sample_cosines(n, pairs, rng):
    """cos(theta) for `pairs` independent random pairs in R^n."""
    return [cos_angle(random_vector(n, rng), random_vector(n, rng))
            for _ in range(pairs)]


def main():
    rng = random.Random(2024)
    print("   n   mean angle   share within 10 deg of 90   sd(cos)  1/sqrt(n)")
    for n in (2, 3, 10, 100, 1000):
        cosines = sample_cosines(n, 300, rng)
        angles = [math.degrees(math.acos(c)) for c in cosines]
        near = sum(abs(a - 90) <= 10 for a in angles) / len(angles)
        sd = statistics.pstdev(cosines)
        print(f"{n:4d}   {statistics.mean(angles):7.2f} deg   "
              f"{near:24.0%}   {sd:7.4f}  {1 / math.sqrt(n):9.4f}")
    print("In the plane a random angle is equally likely anywhere in [0, 180];")
    print("in 1000 dimensions almost every pair is within a few degrees of 90.")
    print()
    print("Epistemic status: statistical evidence from 300 random pairs per")
    print("dimension, so each sample statistic has its own random error (a few")
    print("per cent for sd(cos)). The value 1/sqrt(n) is exact: cos(theta) is")
    print("distributed like one coordinate of a random unit vector, whose")
    print("squares average to 1/n because the n squares add up to 1.")


if __name__ == "__main__":
    main()
