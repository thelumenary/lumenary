"""Which typing errors do check digits catch? Every typo of 300 codes, counted.

For four schemes - ISBN-10 (weights 1..10, mod 11), ISBN-13 (weights 1, 3,
mod 10), Luhn (bank cards and phone IMEIs) and a naive "digit sum mod 10" -
the experiment makes 300 valid code numbers from seeded random digits, then
applies every possible single-digit error, every swap of neighbouring digits
and every swap of digits two apart ("jump" swaps, abc -> cba), and counts how
many of the damaged numbers are rejected. The counts are exact for this sample
of codes; the lesson proves which errors are always caught.
"""

import random

EXPERIMENT = {
    "id": "check_digits_error_rates",
    "title": "Every typo of 300 code numbers, caught or missed",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["check-digits"],
    "summary": (
        "Builds 300 valid ISBN-10, ISBN-13, Luhn and digit-sum codes from seeded "
        "random digits, applies every single-digit error, neighbour swap and jump "
        "swap, and counts how many damaged codes each scheme rejects: ISBN-10 "
        "catches all three kinds, ISBN-13 misses neighbour swaps of digits five "
        "apart, Luhn misses 09/90, and the digit sum misses every swap."
    ),
    "packages": [],
}


def isbn10_check(first9):
    """ISBN-10 check digit (10 means X) for nine digits, weights 1..9."""
    return sum((i + 1) * d for i, d in enumerate(first9)) % 11


def isbn10_valid(code):
    """Ten digits (last may be 10) with 1*d1 + ... + 10*d10 = 0 mod 11."""
    return len(code) == 10 and sum((i + 1) * d for i, d in enumerate(code)) % 11 == 0


def isbn13_valid(code):
    """Thirteen digits with d1 + 3*d2 + d3 + 3*d4 + ... = 0 mod 10."""
    total = sum(d * (1 if i % 2 == 0 else 3) for i, d in enumerate(code))
    return len(code) == 13 and total % 10 == 0


def isbn13_check(first12):
    """The ISBN-13 check digit for twelve digits."""
    total = sum(d * (1 if i % 2 == 0 else 3) for i, d in enumerate(first12))
    return (-total) % 10


def luhn_double(d):
    """Double a digit and add the digits of the result."""
    return 2 * d if d < 5 else 2 * d - 9


def luhn_sum(code):
    """Luhn sum: from the right, every second digit is doubled."""
    return sum(luhn_double(d) if i % 2 == 1 else d
               for i, d in enumerate(reversed(code)))


def luhn_valid(code):
    """A number passes the Luhn test when its Luhn sum is a multiple of 10."""
    return luhn_sum(code) % 10 == 0


def luhn_check(payload):
    """The digit to append so that payload + [digit] passes the Luhn test."""
    return (-luhn_sum(list(payload) + [0])) % 10


def digitsum_valid(code):
    """Naive scheme: the plain digit sum is a multiple of 10."""
    return sum(code) % 10 == 0


def make_codes(scheme, count, seed=2026):
    """``count`` valid codes for ``scheme`` from seeded random digits."""
    rng = random.Random(seed)
    codes = []
    for _ in range(count):
        if scheme == "ISBN-10":
            body = [rng.randrange(10) for _ in range(9)]
            codes.append(body + [isbn10_check(body)])
        elif scheme == "ISBN-13":
            body = [rng.randrange(10) for _ in range(12)]
            codes.append(body + [isbn13_check(body)])
        elif scheme == "Luhn":
            body = [rng.randrange(10) for _ in range(15)]
            codes.append(body + [luhn_check(body)])
        else:
            body = [rng.randrange(10) for _ in range(9)]
            codes.append(body + [(-sum(body)) % 10])
    return codes


VALID = {"ISBN-10": isbn10_valid, "ISBN-13": isbn13_valid,
         "Luhn": luhn_valid, "digit sum": digitsum_valid}


def errors(code, kind, isbn10=False):
    """All damaged versions of ``code`` with one error of the given kind."""
    out = []
    n = len(code)
    if kind == "single":
        for i in range(n):
            top = 11 if (isbn10 and i == n - 1) else 10
            out += [code[:i] + [v] + code[i + 1:] for v in range(top)
                    if v != code[i]]
    else:
        gap = 1 if kind == "neighbour swap" else 2
        for i in range(n - gap):
            if code[i] != code[i + gap]:
                c = list(code)
                c[i], c[i + gap] = c[i + gap], c[i]
                out.append(c)
    return out


def detection(scheme, kind, codes):
    """(caught, total) over every error of ``kind`` applied to ``codes``."""
    valid = VALID[scheme]
    caught = total = 0
    for code in codes:
        for bad in errors(code, kind, isbn10=(scheme == "ISBN-10")):
            total += 1
            caught += not valid(bad)
    return caught, total


def main():
    kinds = ["single", "neighbour swap", "jump swap"]
    print("Share of damaged codes rejected (300 valid codes per scheme)")
    print(f"{'scheme':<10}" + "".join(f"{k:>22}" for k in kinds))
    for scheme in VALID:
        codes = make_codes(scheme, 300)
        assert all(VALID[scheme](c) for c in codes)
        cells = []
        for kind in kinds:
            caught, total = detection(scheme, kind, codes)
            cells.append(f"{100 * caught / total:6.1f}% of {total:>5}")
        print(f"{scheme:<10}" + "".join(f"{c:>22}" for c in cells))
    print()
    print("Swaps count only when the two digits differ. A 'jump swap' exchanges")
    print("digits two places apart: in ISBN-13 and Luhn those positions have the")
    print("same weight, so such swaps are never caught; ISBN-10 catches them all.")
    print()
    print("Epistemic status: exact counts for every error of three kinds applied")
    print("to these 300 codes per scheme. The percentages for ISBN-13 and Luhn")
    print("swaps depend on which digit pairs occur; that ISBN-10 catches every")
    print("single error and every neighbour swap is a theorem, proved in the")
    print("lesson for all ISBN-10s, not just these.")


if __name__ == "__main__":
    main()
