"""Breaking a substitution cipher by counting letters.

A substitution cipher replaces each letter by another letter, using a
scrambled alphabet as the key. There are 26 x 25 x ... x 1 keys - far too
many to try - but the cipher keeps the pattern of how often each letter is
used. The program encodes a paragraph of English with a random key (from a
seeded random number generator), counts the letters of the secret message,
and compares the most common ones with the most common letters of English.
Then it tries the simplest possible attack - match the letters by rank -
and reports how much of the message that alone gets right.
"""

import math
import random
import textwrap
from collections import Counter

EXPERIMENT = {
    "id": "secret_codes_frequency",
    "title": "Breaking a substitution cipher by counting letters",
    "evidence": ["experimental", "exact"],
    "lessons": ["secret-codes"],
    "summary": (
        "Encodes a paragraph with a seeded random substitution key (one of "
        "26! keys), counts the letters of the coded text, and shows that the "
        "most common code letter stands for E. Matching letters by frequency "
        "rank alone decodes only part of the text, which is why code "
        "breakers also use word patterns. One paragraph, one key: an "
        "experiment, not a general law."
    ),
    "packages": [],
}

ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
ENGLISH_ORDER = "ETAOINSHRDLCUMWFGYPBVKJXQZ"

PLAIN = (
    "PEOPLE HAVE SENT SECRET MESSAGES FOR THOUSANDS OF YEARS. A SIMPLE WAY "
    "TO HIDE A MESSAGE IS TO REPLACE EVERY LETTER WITH ANOTHER LETTER. THE "
    "MESSAGE THEN LOOKS LIKE NONSENSE, BUT A CLEVER READER CAN STILL BREAK "
    "THE CODE. IN ENGLISH THE LETTER E APPEARS MORE OFTEN THAN ANY OTHER "
    "LETTER, AND THE WORD THE IS VERY COMMON. SO THE CODE BREAKER COUNTS "
    "THE LETTERS IN THE SECRET MESSAGE AND GUESSES THAT THE MOST COMMON ONE "
    "STANDS FOR E. THEN SHE LOOKS FOR SHORT WORDS AND REPEATED PATTERNS, "
    "AND THE HIDDEN MESSAGE SLOWLY APPEARS."
)


def random_key(seed):
    """A scrambled alphabet: plain letter ALPHABET[i] becomes key[i]."""
    letters = list(ALPHABET)
    random.Random(seed).shuffle(letters)
    return "".join(letters)


def substitute(text, key):
    """Replace each capital letter using the key; keep other characters."""
    table = dict(zip(ALPHABET, key))
    return "".join(table.get(c, c) for c in text)


def letter_counts(text):
    """How many times each capital letter appears, most common first."""
    return Counter(c for c in text if c in ALPHABET).most_common()


def rank_guess(secret):
    """Guess a decoding key by matching letters by frequency rank."""
    ranked = [letter for letter, _ in letter_counts(secret)]
    unused = [c for c in ALPHABET if c not in ranked]
    return dict(zip(ranked + unused, ENGLISH_ORDER))


def main():
    key = random_key(1586)
    secret = substitute(PLAIN, key)
    print(f"Possible keys: 26! = {math.factorial(26):,}")
    print("Secret message (start): " + secret[:52] + "...")
    counts = letter_counts(secret)
    total = sum(n for _, n in counts)
    decode = {code: plain for plain, code in zip(ALPHABET, key)}
    print(f"Most common letters in the secret message ({total} letters):")
    print("  code letter  count  share  really stands for  English rank")
    for rank, (code, n) in enumerate(counts[:6]):
        line = (f"  {code:^11}  {n:>5}  {100 * n / total:>4.0f}%"
                f"  {decode[code]:^17}  {ENGLISH_ORDER[rank]:^12}")
        print(line.rstrip())
    guess = rank_guess(secret)
    attempt = "".join(guess.get(c, c) for c in secret)
    right = sum(1 for p, a in zip(PLAIN, attempt) if p in ALPHABET and p == a)
    print(f"Matching letters by rank alone gets {right} of {total} letters"
          f" right ({100 * right / total:.0f}%):")
    print("  " + attempt[:60] + "...")
    print("A code breaker then fixes it using words such as THE and patterns.")
    print()
    print(textwrap.fill(
        "Epistemic status: exact counting, but one experiment - one "
        "paragraph and one random key. Long English texts usually have E as "
        "their most common letter, but short or unusual texts may not, so "
        "frequency analysis gives good guesses, not certainties. Here the "
        "guesses are checked against the real key.",
        width=78,
    ))


if __name__ == "__main__":
    main()
