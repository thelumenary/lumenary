import random
from fractions import Fraction

import systematic_listing_guessing as sg


def test_outfits():
    assert len(sg.OUTFITS) == 12
    assert len(set(sg.OUTFITS)) == 12


def test_guess_until_bored_finds_only_real_outfits():
    rng = random.Random(1)
    for patience in (1, 3, 10):
        found = sg.guess_until_bored(rng, patience)
        assert 1 <= len(found) <= 12
        assert found <= set(sg.OUTFITS)


def test_more_patience_finds_more_on_average():
    rng = random.Random(5)
    impatient = sum(len(sg.guess_until_bored(rng, 2)) for _ in range(500)) / 500
    patient = sum(len(sg.guess_until_bored(rng, 20)) for _ in range(500)) / 500
    assert impatient < patient <= 12


def test_never_giving_up_finds_everything():
    rng = random.Random(3)
    for _ in range(50):
        g = sg.guesses_to_find_all(rng)
        assert g >= 12


def test_expected_guesses_exact():
    assert sg.expected_guesses(1) == 1
    assert sg.expected_guesses(2) == 3
    assert sg.expected_guesses(12) == Fraction(86021, 2310)


def test_simulation_close_to_exact():
    rng = random.Random(11)
    runs = 3000
    mean = sum(sg.guesses_to_find_all(rng) for _ in range(runs)) / runs
    assert abs(mean - float(sg.expected_guesses(12))) < 1.5
