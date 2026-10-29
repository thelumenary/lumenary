"""Huffman coding against the entropy bound, on a real sentence.

We take Article 1 of the Universal Declaration of Human Rights, count its
characters, and treat it as a source emitting characters independently with
those frequencies. We compute the entropy H, build a Huffman code, and check
Kraft's equality and the source coding bounds H <= L < H + 1, compared with a
fixed-length code and with Shannon's lengths ceil(-log2 p). Coding pairs of
characters (under the same independence model) brings the cost per character
closer to H.
"""

import heapq
import math
from collections import Counter
from fractions import Fraction

EXPERIMENT = {
    "id": "information_theory_huffman",
    "title": "Huffman coding and the entropy bound on a real sentence",
    "evidence": ["exact"],
    "lessons": ["information-theory"],
    "summary": (
        "Builds a Huffman code for the character frequencies of Article 1 of the "
        "Universal Declaration of Human Rights, checks Kraft's equality and the bounds "
        "H <= L < H + 1, compares fixed-length and Shannon codes, and shows that coding "
        "pairs of characters reduces the overhead per character. Exact rational "
        "arithmetic (entropies shown rounded) for this one text and its i.i.d. model."
    ),
    "packages": [],
}

TEXT = ("All human beings are born free and equal in dignity and rights. They "
        "are endowed with reason and conscience and should act towards one "
        "another in a spirit of brotherhood.")


def frequencies(text):
    """Dictionary symbol -> exact probability (Fraction)."""
    counts = Counter(text)
    total = len(text)
    return {s: Fraction(c, total) for s, c in counts.items()}


def entropy_bits(probs):
    """H = -sum p log2 p, in bits."""
    return -sum(float(p) * math.log2(p) for p in probs.values() if p > 0)


def huffman_lengths(probs):
    """Codeword lengths of a Huffman code for the given probabilities.

    Repeatedly merge the two least likely subtrees; every merge adds one bit
    to the codewords of all symbols inside the two merged subtrees.
    """
    if len(probs) == 1:
        return {s: 1 for s in probs}
    heap = [(p, i, [s]) for i, (s, p) in enumerate(sorted(probs.items(),
                                                          key=str))]
    heapq.heapify(heap)
    lengths = {s: 0 for s in probs}
    counter = len(heap)
    while len(heap) > 1:
        p1, _, group1 = heapq.heappop(heap)
        p2, _, group2 = heapq.heappop(heap)
        for s in group1 + group2:
            lengths[s] += 1
        heapq.heappush(heap, (p1 + p2, counter, group1 + group2))
        counter += 1
    return lengths


def expected_length(probs, lengths):
    """L = sum p(x) l(x), exact."""
    return sum(probs[s] * lengths[s] for s in probs)


def kraft_sum(lengths):
    """sum 2^(-l(x)), exact."""
    return sum(Fraction(1, 2 ** n) for n in lengths.values())


def shannon_lengths(probs):
    """Shannon's lengths ceil(-log2 p(x)), computed exactly for rationals."""
    out = {}
    for s, p in probs.items():
        n = 0
        while Fraction(1, 2 ** n) > p:
            n += 1
        out[s] = n
    return out


def pair_probs(probs):
    """Probabilities of ordered pairs under the independence model."""
    return {(a, b): pa * pb for a, pa in probs.items() for b, pb in probs.items()}


def main():
    probs = frequencies(TEXT)
    k = len(probs)
    h = entropy_bits(probs)
    huff = huffman_lengths(probs)
    shan = shannon_lengths(probs)
    l_huff = expected_length(probs, huff)
    l_shan = expected_length(probs, shan)
    print(f"Text: UDHR Article 1, {len(TEXT)} characters, {k} distinct symbols")
    print(f"  entropy H                    = {h:.4f} bits/char")
    print(f"  fixed-length code            = {math.ceil(math.log2(k))} bits/char")
    print(f"  Shannon code ceil(-log2 p)   = {float(l_shan):.4f} bits/char,"
          f" Kraft sum {float(kraft_sum(shan)):.4f}")
    print(f"  Huffman code                 = {float(l_huff):.4f} bits/char,"
          f" Kraft sum {kraft_sum(huff)}")
    print(f"  H <= L_Huffman < H + 1: {h <= l_huff < h + 1};"
          f" L_Huffman <= L_Shannon: {l_huff <= l_shan}")
    print()
    print("Most and least frequent symbols with their Huffman lengths:")
    ranked = sorted(probs, key=lambda s: (-probs[s], s))
    for s in ranked[:4] + ranked[-2:]:
        name = "space" if s == " " else repr(s)
        print(f"  {name:>7}: p = {str(probs[s]):>7}, length {huff[s]}")
    pairs = pair_probs(probs)
    l_pairs = expected_length(pairs, huffman_lengths(pairs)) / 2
    print()
    print(f"Huffman on pairs (i.i.d. model): {float(l_pairs):.4f} bits/char,"
          f" overhead {float(l_pairs) - h:.4f}")
    print(f"Huffman on single characters:    overhead {float(l_huff) - h:.4f}")
    print()
    print("Epistemic status: exact computation for one sentence and the model")
    print("that draws characters independently with these frequencies. Real")
    print("text has dependence between letters, so its true entropy rate is")
    print("lower than H; the theorems H <= L < H + 1 are proved in the lesson.")


if __name__ == "__main__":
    main()
