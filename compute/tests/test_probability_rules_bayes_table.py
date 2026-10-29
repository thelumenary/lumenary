from fractions import Fraction

import pytest

import probability_rules_bayes_table as pb


def test_two_way_table_counts():
    tp, fn, fp, tn = pb.two_way_table(Fraction(100000), Fraction(1, 100),
                                      Fraction(95, 100), Fraction(95, 100))
    assert (tp, fn, fp, tn) == (950, 50, 4950, 94050)
    assert tp + fn + fp + tn == 100000


def test_posterior_matches_table():
    ppv = pb.posterior(Fraction(1, 100), Fraction(95, 100), Fraction(5, 100))
    assert ppv == Fraction(19, 118)
    tp, fn, fp, tn = pb.two_way_table(Fraction(100000), Fraction(1, 100),
                                      Fraction(95, 100), Fraction(95, 100))
    assert ppv == tp / (tp + fp)


@pytest.mark.parametrize("prior", [Fraction(1, 1000), Fraction(1, 10),
                                   Fraction(1, 2)])
def test_posterior_properties(prior):
    # a test that says nothing leaves the prior unchanged
    assert pb.posterior(prior, Fraction(1, 3), Fraction(1, 3)) == prior
    # a positive result from an informative test raises the probability
    assert pb.posterior(prior, Fraction(9, 10), Fraction(1, 10)) > prior
    # a perfect test (no false positives) gives certainty
    assert pb.posterior(prior, Fraction(9, 10), Fraction(0)) == 1


def test_base_rate_monotone_and_second_test():
    sens, fpr = Fraction(95, 100), Fraction(5, 100)
    values = [pb.posterior(Fraction(r), sens, fpr)
              for r in ("1/1000", "1/100", "1/10", "1/2")]
    assert values == sorted(values)
    assert values[-1] == Fraction(95, 100)
    second = pb.posterior(values[1], sens, fpr)
    assert abs(float(second) - 0.785) < 0.001


def test_prosecutors_fallacy_numbers():
    guilty = pb.posterior(Fraction(1, 2_000_000), Fraction(1),
                          Fraction(1, 10**6))
    assert abs(float(1 - guilty) - 2 / 3) < 1e-6
    assert pb.fmt(Fraction(1234567)) == "1,234,567"
