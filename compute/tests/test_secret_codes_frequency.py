import math

import secret_codes_frequency as sf


def test_key_is_a_scrambled_alphabet():
    key = sf.random_key(1586)
    assert sorted(key) == list(sf.ALPHABET)
    assert key == sf.random_key(1586)  # seeded: always the same key
    assert key != sf.ALPHABET


def test_substitution_can_be_undone():
    key = sf.random_key(7)
    secret = sf.substitute(sf.PLAIN, key)
    # inverse[i] is the plain letter whose code letter is ALPHABET[i]
    inverse = "".join(sf.ALPHABET[key.index(c)] for c in sf.ALPHABET)
    assert sf.substitute(secret, inverse) == sf.PLAIN


def test_counts_survive_substitution():
    key = sf.random_key(1586)
    secret = sf.substitute(sf.PLAIN, key)
    plain_counts = sorted(n for _, n in sf.letter_counts(sf.PLAIN))
    secret_counts = sorted(n for _, n in sf.letter_counts(secret))
    assert plain_counts == secret_counts


def test_most_common_code_letter_is_e():
    key = sf.random_key(1586)
    secret = sf.substitute(sf.PLAIN, key)
    top = sf.letter_counts(secret)[0][0]
    assert key[sf.ALPHABET.index("E")] == top
    assert sf.rank_guess(secret)[top] == "E"


def test_number_of_keys():
    assert math.factorial(26) == 403291461126605635584000000
