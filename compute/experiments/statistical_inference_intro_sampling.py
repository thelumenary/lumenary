"""Sampling variability, margins of error and bias, by simulation.

A town has 20,000 households, of which exactly 7,600 (38%) collect rainwater
in a tank. We pretend not to know this and estimate it from samples. For
simple random samples of size n = 25, 100, 400 and 1,600, two thousand
samples each are drawn (the number of tanks in a simple random sample has a
hypergeometric distribution, which NumPy samples directly). The spread of
the estimates shrinks like 1/sqrt(n), about 95% of the intervals
"estimate +/- margin of error" catch the true value, and a huge voluntary-
response sample is worse than a small random one.
"""

import math

import numpy as np

EXPERIMENT = {
    "id": "statistical_inference_intro_sampling",
    "title": "Sampling variability, margins of error and bias",
    "evidence": ["statistical", "exact"],
    "lessons": ["statistical-inference-intro"],
    "summary": (
        "Draws 2,000 simple random samples of each size 25, 100, 400 and 1,600 "
        "from a town of 20,000 households with a known 38% rate (seeded). The "
        "standard deviation of the estimates matches the formula and halves "
        "when n quadruples; about 95% of 95% intervals contain the truth; a "
        "voluntary-response sample of 5,000 misses badly. Statistical evidence "
        "from one simulated run, compared with exact formulas."
    ),
    "packages": ["numpy"],
}

POPULATION, WITH_TANK = 20000, 7600
P_TRUE = WITH_TANK / POPULATION


def standard_error(p, n, population=POPULATION):
    """SD of the sample proportion for a simple random sample of size n."""
    fpc = (population - n) / (population - 1)  # finite population correction
    return math.sqrt(p * (1 - p) / n * fpc)


def srs_estimates(rng, n, repeats):
    """Sample proportions from `repeats` simple random samples of size n."""
    hits = rng.hypergeometric(WITH_TANK, POPULATION - WITH_TANK, n, repeats)
    return hits / n


def coverage(estimates, n, z=1.96):
    """Fraction of intervals p_hat +/- z sqrt(p_hat(1-p_hat)/n) containing P."""
    margin = z * np.sqrt(estimates * (1 - estimates) / n)
    return float(np.mean(np.abs(estimates - P_TRUE) <= margin))


def voluntary_response(rng, responses, p_reply_tank, p_reply_none):
    """Estimate from the first `responses` replies when replying is biased."""
    w_tank = P_TRUE * p_reply_tank
    w_none = (1 - P_TRUE) * p_reply_none
    tanks = rng.binomial(responses, w_tank / (w_tank + w_none))
    return tanks / responses


def main():
    rng = np.random.default_rng(2024)
    print(f"True proportion with a tank: {P_TRUE:.2f} "
          f"({WITH_TANK:,} of {POPULATION:,} households)")
    print("2,000 simple random samples of each size:")
    print("     n   mean of estimates   SD of estimates   formula   "
          "95% coverage")
    for n in (25, 100, 400, 1600):
        est = srs_estimates(rng, n, 2000)
        print(f"  {n:4d}   {est.mean():17.4f}   {est.std():15.4f}   "
              f"{standard_error(P_TRUE, n):7.4f}   {coverage(est, n):12.3f}")
    print("Four times the sample size: half the spread.")
    print()
    one = srs_estimates(rng, 400, 1)[0]
    margin = 1.96 * math.sqrt(one * (1 - one) / 400)
    print(f"One survey of 400: estimate {one:.3f}, margin of error "
          f"{margin:.3f},")
    print(f"  interval {one - margin:.3f} to {one + margin:.3f}")
    print()
    biased = voluntary_response(rng, 5000, 0.6, 0.2)
    print("Voluntary response (tank owners reply 3 times as often):")
    print(f"  5,000 replies estimate {biased:.3f}; the truth is {P_TRUE:.3f}.")
    print("  More data does not cure a biased way of collecting it.")
    print()
    print("Epistemic status: statistical evidence from one seeded run;")
    print("other seeds give slightly different numbers. The formula column")
    print("is exact for simple random samples; the coverage of about 95% is")
    print("a long-run property of the method, not of any one interval.")


if __name__ == "__main__":
    main()
