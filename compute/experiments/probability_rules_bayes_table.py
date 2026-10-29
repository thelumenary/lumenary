"""Bayes' theorem with natural frequencies: tests, base rates and courtrooms.

A diagnostic test is imagined on 100,000 people and every count is exact.
The two-way table shows why P(condition | positive) and P(positive |
condition) are different numbers, and the same test is re-run with base
rates from 0.1% to 50% to show how strongly the answer depends on them. A
second independent positive test is handled by using the first posterior as
the new prior. Finally the prosecutor's fallacy: a DNA profile shared by one
person in a million, in a city of two million.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "probability_rules_bayes_table",
    "title": "Bayes' theorem with natural frequencies and base rates",
    "evidence": ["exact"],
    "lessons": ["probability-rules"],
    "summary": (
        "Builds the exact two-way table for a test with 95% sensitivity and 95% "
        "specificity on 100,000 people with a 1% base rate: only 19/118 (about "
        "16%) of positives have the condition. Recomputes P(condition | "
        "positive) for base rates from 0.1% to 50%, updates after a second "
        "positive test, and shows the prosecutor's fallacy with a one-in-a-"
        "million DNA match in a city of two million. Exact arithmetic."
    ),
    "packages": [],
}


def two_way_table(population, prevalence, sensitivity, specificity):
    """Counts (true pos, false neg, false pos, true neg) as exact Fractions."""
    sick = population * prevalence
    well = population - sick
    return (sick * sensitivity, sick * (1 - sensitivity),
            well * (1 - specificity), well * specificity)


def posterior(prior, p_pos_given_d, p_pos_given_not_d):
    """P(D | positive) by Bayes' theorem with total probability below."""
    top = p_pos_given_d * prior
    return top / (top + p_pos_given_not_d * (1 - prior))


def fmt(q):
    """An exact count as a whole number with thousands separators."""
    assert q.denominator == 1
    return f"{q.numerator:,}"


def main():
    sens, spec = Fraction(95, 100), Fraction(95, 100)
    tp, fn, fp, tn = two_way_table(Fraction(100000), Fraction(1, 100),
                                   sens, spec)
    print("Test: sensitivity 95%, specificity 95%; base rate 1%.")
    print("Imagine 100,000 people:")
    print("                  test +     test -      total")
    print(f"  condition    {fmt(tp):>9}  {fmt(fn):>9}  {fmt(tp + fn):>9}")
    print(f"  no condition {fmt(fp):>9}  {fmt(tn):>9}  {fmt(fp + tn):>9}")
    print(f"  total        {fmt(tp + fp):>9}  {fmt(fn + tn):>9}  "
          f"{fmt(tp + fn + fp + tn):>9}")
    ppv = tp / (tp + fp)
    print(f"P(condition | +) = {fmt(tp)}/{fmt(tp + fp)} = {ppv} "
          f"= {float(ppv):.3f}")
    print(f"P(+ | condition) = {fmt(tp)}/{fmt(tp + fn)} = "
          f"{float(tp / (tp + fn)):.3f}   (a different question!)")
    print()
    print("Same test, different base rates:")
    print("  base rate   P(condition | +)   P(no condition | -)")
    for rate in ("1/1000", "1/100", "1/10", "1/2"):
        prior = Fraction(rate)
        ppv_r = posterior(prior, sens, 1 - spec)
        npv_r = posterior(1 - prior, spec, 1 - sens)
        print(f"  {float(prior):9.1%}   {float(ppv_r):16.4f}"
              f"   {float(npv_r):19.5f}")
    second = posterior(ppv, sens, 1 - spec)
    print(f"After a second, independent positive test: {float(ppv):.3f} -> "
          f"{float(second):.3f}")
    print()
    match = posterior(Fraction(1, 2_000_000), Fraction(1), Fraction(1, 10**6))
    print("DNA profile shared by 1 person in 1,000,000; city of 2,000,000;")
    print("no other evidence. P(match | innocent) = 0.000001, but")
    print(f"P(innocent | match) = {float(1 - match):.4f}")
    print()
    print("Epistemic status: exact arithmetic in a model whose inputs (base")
    print("rate, sensitivity, specificity, independence of the two tests)")
    print("are assumptions. Change them and the answers change; the")
    print("structure of the calculation (Bayes' theorem) does not.")


if __name__ == "__main__":
    main()
