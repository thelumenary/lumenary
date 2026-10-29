"""Caesar shifts: encoding, wrapping round, and breaking by trying every key.

Letters are numbered A = 0, ..., Z = 25, and a Caesar shift by k sends
letter n to (n + k) mod 26, so Z wraps round to A. The program encodes and
decodes the lesson's examples, then breaks a secret message by trying all
26 shifts. To pick out the right one automatically, it gives each attempt a
score that measures how far its letter counts are from typical English
letter frequencies (smaller is more English-like).
"""

import textwrap

EXPERIMENT = {
    "id": "secret_codes_caesar",
    "title": "Caesar shifts: encode, decode, and try every key",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["secret-codes"],
    "summary": (
        "Encodes and decodes messages with Caesar shifts (letter n goes to "
        "n + k mod 26), shows the wrap-around from Z to A, and breaks a coded "
        "message by trying all 26 shifts, scoring each against typical "
        "English letter frequencies. Trying every key is exhaustive; the "
        "score is a heuristic that a reader still checks by eye."
    ),
    "packages": [],
}

ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

# Typical percentages of each letter in long English texts (A to Z).
ENGLISH = [8.2, 1.5, 2.8, 4.3, 12.7, 2.2, 2.0, 6.1, 7.0, 0.15, 0.8, 4.0, 2.4,
           6.7, 7.5, 1.9, 0.1, 6.0, 6.3, 9.1, 2.8, 1.0, 2.4, 0.15, 2.0, 0.07]

SECRET = "ESP ECPLDFCP TD FYOPC ESP XLYRZ ECPP"


def shift_letter(letter, k):
    """Shift one capital letter k places along the alphabet, wrapping round."""
    return ALPHABET[(ALPHABET.index(letter) + k) % 26]


def caesar(message, k):
    """Shift every capital letter of the message; leave other characters."""
    return "".join(shift_letter(c, k) if c in ALPHABET else c
                   for c in message)


def english_score(text):
    """How far the letter counts are from English (chi-squared statistic)."""
    letters = [c for c in text if c in ALPHABET]
    total = len(letters)
    score = 0.0
    for i, letter in enumerate(ALPHABET):
        expected = total * ENGLISH[i] / 100
        observed = letters.count(letter)
        score += (observed - expected) ** 2 / expected
    return score


def best_shift(secret):
    """The decoding shift whose result has the most English-like letters."""
    return min(range(26), key=lambda k: english_score(caesar(secret, k)))


def main():
    for message, k, note in [("MEET AT NOON", 3, ""),
                             ("ZEBRA", 3, "  (Z wraps round to C)"),
                             ("PHHW DW QRRQ", 23, "  (23 undoes 3)")]:
        label = f"{message}, shift {k}:"
        print(f"{label:<25}{caesar(message, k)}{note}")
    print()
    print(f"Secret message: {SECRET}")
    print("Every possible decoding (shift forward by k):")
    best = best_shift(SECRET)
    for k in range(26):
        attempt = caesar(SECRET, k)
        mark = "  <- most English-like" if k == best else ""
        print(f"  k = {k:>2}: {attempt}{mark}")
    print(f"The sender shifted by {(26 - best) % 26};"
          f" shifting by {best} undoes it.")
    print()
    print(textwrap.fill(
        "Epistemic status: exact and exhaustive - every one of the 26 shifts "
        "was tried, so the message cannot hide from this search. The "
        "'English-like' score is only a heuristic: for very short or unusual "
        "messages it can point to the wrong shift, so a person still reads "
        "the answer to check that it makes sense.",
        width=78,
    ))


if __name__ == "__main__":
    main()
