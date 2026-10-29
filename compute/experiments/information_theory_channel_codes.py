"""Coding over a noisy channel: repetition codes, the Hamming code and capacity.

A binary symmetric channel flips each bit with probability p. Its capacity is
C = 1 - H(p) bits per use. Repetition codes make errors rare only by sending
the rate R = 1/n to zero. The Hamming (7, 4) code sends 4 message bits in 7
channel bits (R = 4/7) and corrects any single flip. We compute exact block
error probabilities, then simulate the Hamming code with syndrome decoding.
"""

import math
import random

EXPERIMENT = {
    "id": "information_theory_channel_codes",
    "title": "Repetition codes, the Hamming code and channel capacity",
    "evidence": ["exact", "statistical"],
    "lessons": ["information-theory"],
    "summary": (
        "Computes the capacity 1 - H(p) of binary symmetric channels and the exact "
        "error probabilities of repetition codes (rate 1/n) and of the Hamming (7, 4) "
        "code (rate 4/7), then simulates 20,000 Hamming blocks with syndrome decoding. "
        "Shows the trade-off that Shannon's theorem resolves: good codes need not have "
        "rate tending to zero."
    ),
    "packages": [],
}

#: Generator matrix rows (systematic form): codeword = message . G (mod 2).
G = [[1, 0, 0, 0, 1, 1, 0],
     [0, 1, 0, 0, 1, 0, 1],
     [0, 0, 1, 0, 0, 1, 1],
     [0, 0, 0, 1, 1, 1, 1]]
#: Parity-check matrix: H . codeword = 0 (mod 2) for every codeword.
H = [[1, 1, 0, 1, 1, 0, 0],
     [1, 0, 1, 1, 0, 1, 0],
     [0, 1, 1, 1, 0, 0, 1]]


def h2(p):
    """Binary entropy in bits."""
    if p in (0, 1):
        return 0.0
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def capacity(p):
    """Capacity of the binary symmetric channel, 1 - H(p) bits per use."""
    return 1 - h2(p)


def repetition_error(n, p):
    """Exact error probability of majority decoding for odd n repetitions."""
    if n % 2 == 0:
        raise ValueError("use an odd number of repetitions")
    return sum(math.comb(n, k) * p ** k * (1 - p) ** (n - k)
               for k in range(n // 2 + 1, n + 1))


def hamming_block_error(p):
    """Exact probability that a Hamming (7, 4) block is decoded wrongly.

    Syndrome decoding corrects every pattern of at most one flip and no
    other, so the block is right exactly when at most one bit flips.
    """
    return 1 - (1 - p) ** 7 - 7 * p * (1 - p) ** 6


def encode(message):
    """7-bit codeword of a 4-bit message."""
    return [sum(m * g for m, g in zip(message, col)) % 2 for col in zip(*G)]


def syndrome(word):
    """H . word (mod 2), as a tuple."""
    return tuple(sum(h * w for h, w in zip(row, word)) % 2 for row in H)


def decode(word):
    """Correct at most one flip: the syndrome equals the column of H at the
    flipped position. Return the 4 message bits."""
    s = syndrome(word)
    word = list(word)
    if any(s):
        columns = [tuple(row[j] for row in H) for j in range(7)]
        word[columns.index(s)] ^= 1
    return word[:4]


def simulate_hamming(p, blocks, rng):
    """Fraction of blocks decoded wrongly over a simulated channel."""
    errors = 0
    for _ in range(blocks):
        message = [rng.randrange(2) for _ in range(4)]
        received = [b ^ (rng.random() < p) for b in encode(message)]
        errors += decode(received) != message
    return errors / blocks


def main():
    p = 0.05
    print(f"Binary symmetric channel with p = {p}:"
          f" capacity C = 1 - H(p) = {capacity(p):.4f} bits/use")
    print()
    print("Repetition codes (majority vote):")
    print("    n    rate   error probability")
    for n in [1, 3, 5, 9, 15, 25]:
        print(f"  {n:>3} {1 / n:>7.3f} {repetition_error(n, p):>13.2e}")
    print("Errors vanish only as the rate 1/n goes to 0.")
    print()
    rng = random.Random(1948)
    sim = simulate_hamming(p, 20000, rng)
    print(f"Hamming (7, 4): rate 4/7 = {4 / 7:.3f} < C;"
          f" block error exact {hamming_block_error(p):.4f},"
          f" simulated {sim:.4f}")
    messages = [[(m >> i) & 1 for i in range(4)] for m in range(16)]
    checks = all(not any(syndrome(encode(m))) for m in messages)
    print(f"  all 16 codewords pass the parity checks: {checks}")
    print()
    print("Capacity of the BSC for several p (bits per use):")
    print("  " + "  ".join(f"p={q}: {capacity(q):.3f}"
                           for q in [0.0, 0.01, 0.1, 0.5, 0.9]))
    print()
    print("Epistemic status: the error probabilities and capacities are exact")
    print("formulas evaluated in floating point; the Hamming simulation is")
    print("statistical evidence (standard error about 0.001). That longer codes")
    print("at any fixed rate below C achieve arbitrarily small error is")
    print("Shannon's theorem, which these finite examples do not prove.")


if __name__ == "__main__":
    main()
