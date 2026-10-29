from itertools import product

import pytest

import incompleteness_diagonal_lemma as dl


def test_alphabet_has_distinct_symbols():
    assert len(set(dl.ALPHABET)) == len(dl.ALPHABET) == dl.BASE


def test_encoding_is_a_bijection_on_short_strings():
    codes = set()
    for length in range(3):
        for chars in product(dl.ALPHABET, repeat=length):
            text = "".join(chars)
            code = dl.encode(text)
            assert dl.decode(code) == text
            codes.add(code)
    # Bijective base-k numbering: strings of length < 3 fill an initial segment.
    assert codes == set(range(1 + dl.BASE + dl.BASE ** 2))
    with pytest.raises(ValueError):
        dl.encode("#")
    with pytest.raises(ValueError):
        dl.decode(-1)


def test_decode_inverts_encode_on_large_codes():
    for code in [0, 1, 37, 10**20 + 7, 12345678901234567890123]:
        assert dl.encode(dl.decode(code)) == code


def test_diagonal_identity_for_every_template():
    for template in ["~P(diag(x))", "Even(diag(x))", "Long(diag(x))", "x=x", "S(x)"]:
        g = dl.fixed_point(template)
        assert dl.diag(dl.encode(template)) == dl.encode(g)
        assert "x" not in g


def test_fixed_points_of_decidable_properties():
    for template in ["Even(diag(x))", "~Even(diag(x))", "Long(diag(x))", "~Long(diag(x))"]:
        g = dl.fixed_point(template)
        negated, name, target = dl.parse(g)
        assert target == dl.encode(g)
        own = dl.PREDICATES[name](dl.encode(g))
        assert dl.evaluate(g) == ((not own) if negated else own)


def test_liar_and_truth_teller():
    assert dl.self_reference_values(dl.fixed_point("True(diag(x))")) == [True, False]
    assert dl.self_reference_values(dl.fixed_point("~True(diag(x))")) == []
    with pytest.raises(ValueError):
        dl.self_reference_values("True(diag(5))")


def test_parse_rejects_malformed_sentences():
    with pytest.raises(ValueError):
        dl.parse("Even(5)")
