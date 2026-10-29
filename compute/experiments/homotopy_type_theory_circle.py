"""Encode-decode for the circle, in a combinatorial model, and winding numbers.

In homotopy type theory the circle S^1 has a point base and a path loop. Loops
at base built from loop and its inverse are modelled here by words in +1
(loop) and -1 (loop inverse); concatenation of paths is concatenation of
words, and the groupoid laws p . p^-1 = refl let us cancel adjacent +1, -1.
The universal cover is the type family code with code(base) = Z, where
transport along loop is the successor. So:

* encode(w) = transport of 0 along w = apply succ for +1 and pred for -1;
* decode(n) = loop^n, the word of |n| copies of the sign of n.

We check exhaustively, for all words of length <= 12, that decode(encode(w))
is the free reduction of w (so two words are equal up to the groupoid laws
exactly when they have the same winding number) and that encode turns
concatenation into addition; then compute winding numbers of parametrised
loops in the plane numerically, the classical counterpart. This is a model and
finite evidence, not the HoTT proof, which is about the higher inductive type.
"""

import cmath
import math
from itertools import product

EXPERIMENT = {
    "id": "homotopy_type_theory_circle",
    "title": "Encode-decode for the circle: words, winding numbers, Z",
    "evidence": ["exact", "exhaustive-finite", "numerical"],
    "lessons": ["homotopy-type-theory"],
    "summary": (
        "Models loops in the circle as words in loop and its inverse. Encoding by "
        "transport in the universal cover (successor and predecessor on Z) and "
        "decoding n as loop^n, it checks exhaustively for all 8190 non-empty words "
        "of length <= 12 that decode(encode(w)) is the free reduction of w and "
        "that encode is additive, then computes winding numbers of plane loops "
        "numerically. A finite model, not the type-theoretic proof."
    ),
    "packages": [],
}


def encode(word):
    """Transport 0 along the path ``word`` in the universal cover of S^1.

    Transport along loop is succ, along its inverse pred; transport along a
    concatenation is the composite of the transports.
    """
    position = 0
    for step in word:
        if step not in (1, -1):
            raise ValueError("a word consists of +1 (loop) and -1 (loop^-1)")
        position = position + 1 if step == 1 else position - 1
    return position


def decode(n):
    """The loop loop^n as a word: |n| copies of +1 (n > 0) or -1 (n < 0)."""
    return (1,) * n if n >= 0 else (-1,) * (-n)


def reduce_word(word):
    """Free reduction: cancel adjacent loop . loop^-1 and loop^-1 . loop."""
    stack = []
    for step in word:
        if stack and stack[-1] == -step:
            stack.pop()
        else:
            stack.append(step)
    return tuple(stack)


def inverse(word):
    """The inverse path: reverse the word and invert each letter."""
    return tuple(-s for s in reversed(word))


def all_words(max_length):
    """Every word of length 1..max_length in the letters +1 and -1."""
    for length in range(1, max_length + 1):
        yield from product((1, -1), repeat=length)


def winding_number(curve, samples=2000):
    """Numerical winding number of a closed curve t -> curve(t) around 0,
    t in [0, 1], by summing the changes of argument between samples."""
    total = 0.0
    previous = curve(0.0)
    for i in range(1, samples + 1):
        current = curve(i / samples)
        total += cmath.phase(current / previous)
        previous = current
    return total / (2 * math.pi)


def wobbly_loop(turns, wobble=0.6, frequency=7):
    """A loop that winds ``turns`` times round 0 with a radial wobble."""
    def curve(t):
        radius = 1 + wobble * math.cos(2 * math.pi * frequency * t)
        return radius * cmath.exp(2j * math.pi * turns * t)
    return curve


def main():
    words = list(all_words(12))
    decoded_ok = all(decode(encode(w)) == reduce_word(w) for w in words)
    print(f"Words of length 1..12: {len(words)}")
    print(f"decode(encode(w)) == reduce(w) for every word: {decoded_ok}")
    print("encode(decode(n)) == n for -50 <= n <= 50:",
          all(encode(decode(n)) == n for n in range(-50, 51)))
    short = list(all_words(6))
    additive = all(encode(u + v) == encode(u) + encode(v)
                   for u in short for v in short)
    print(f"encode(u . v) == encode(u) + encode(v) for words up to 6: "
          f"{additive}")
    print("encode(w^-1) == -encode(w) for all words up to 12:",
          all(encode(inverse(w)) == -encode(w) for w in words))
    null = [w for w in product((1, -1), repeat=10) if encode(w) == 0]
    print(f"Words of length 10 with winding number 0: {len(null)} "
          f"(= C(10,5) = {math.comb(10, 5)});")
    print("   all of them reduce to refl:",
          all(reduce_word(w) == () for w in null))
    print()
    print("Classical counterpart: winding numbers of plane loops (numerical)")
    for turns in (1, 3, -2, 0):
        w = winding_number(wobbly_loop(turns))
        print(f"   loop winding {turns:>2} times with a wobble: "
              f"computed {w:+.6f}, |error| < 1e-9: {abs(w - turns) < 1e-9}")
    print()
    print("Epistemic status: exact, exhaustive checks of a combinatorial model")
    print("(words up to length 12), plus floating-point winding numbers. They")
    print("illustrate the encode-decode equivalence of loops with Z but do not")
    print("prove the HoTT theorem, which concerns the higher inductive circle.")


if __name__ == "__main__":
    main()
