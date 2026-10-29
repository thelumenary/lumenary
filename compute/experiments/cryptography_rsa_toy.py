"""Toy RSA from scratch: key generation, fast powering, and why toy keys break.

The experiment finds two random 18-bit primes with the Miller-Rabin
test (seeded, so the run is reproducible), builds an RSA key with
e = 65537 and d = e^(-1) mod (p - 1)(q - 1), and encrypts and decrypts a few
messages with modular exponentiation by repeated squaring, counting the
multiplications. It then shows two weaknesses of textbook RSA: encryption is
deterministic and multiplicative (malleable), and a modulus this small is
factored at once by trial division, which reveals the private key. Exact
arithmetic throughout; a toy, not a secure implementation, and no evidence
about the security of real RSA.
"""

import math
import random

EXPERIMENT = {
    "id": "cryptography_rsa_toy",
    "title": "Toy RSA: keys, fast powering and a broken small key",
    "evidence": ["exact", "experimental"],
    "lessons": ["cryptography"],
    "summary": (
        "Generates a seeded 36-bit toy RSA key with Miller-Rabin primes, encrypts "
        "and decrypts with repeated squaring (counting multiplications), shows "
        "that textbook RSA is deterministic and malleable, and breaks the key by "
        "trial division. Correctness is checked exactly on examples; nothing here "
        "measures the security of real RSA."
    ),
    "packages": [],
}


def pow_mod(b, e, n):
    """Right-to-left repeated squaring; returns (b^e mod n, multiplications)."""
    result, base, mults = 1 % n, b % n, 0
    while e > 0:
        if e & 1:
            result = result * base % n
            mults += 1
        e >>= 1
        if e:
            base = base * base % n
            mults += 1
    return result, mults


def is_probable_prime(n, rng, rounds=20):
    """Miller-Rabin with random bases; never wrong when it says 'composite'."""
    if n < 4:
        return n in (2, 3)
    if n % 2 == 0:
        return False
    d, s = n - 1, 0
    while d % 2 == 0:
        d, s = d // 2, s + 1
    for _ in range(rounds):
        x = pow(rng.randrange(2, n - 1), d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def random_prime(bits, rng):
    """A random probable prime with exactly the given number of bits."""
    while True:
        n = rng.getrandbits(bits) | (1 << (bits - 1)) | 1
        if is_probable_prime(n, rng):
            return n


def make_key(bits, rng, e=65537):
    """Return (n, e, d, p, q) with ed = 1 (mod (p - 1)(q - 1))."""
    while True:
        p, q = random_prime(bits, rng), random_prime(bits, rng)
        phi = (p - 1) * (q - 1)
        if p != q and math.gcd(e, phi) == 1:
            return p * q, e, pow(e, -1, phi), p, q


def smallest_factor(n):
    """Trial division up to sqrt(n)."""
    for f in range(2, math.isqrt(n) + 1):
        if n % f == 0:
            return f
    return n


def main():
    rng = random.Random(2024)
    n, e, d, p, q = make_key(18, rng)
    print(f"p = {p}, q = {q}")
    print(f"n = {n} ({n.bit_length()} bits), e = {e}")
    print(f"d = {d}")
    for m in (42, 31337, 2026):
        c, k = pow_mod(m, e, n)
        back, k2 = pow_mod(c, d, n)
        print(f"m = {m:>5} -> c = {c:>11} -> {back:>5}"
              f" ({k} + {k2} mults)")
    print(f"naive powering would need {e - 1} and {d - 1} multiplications")
    print()
    vote = rng.choice([1, 2])  # 1 = "no", 2 = "yes", sent encrypted
    intercepted = pow(vote, e, n)
    guess = [m for m in (1, 2) if pow(m, e, n) == intercepted]
    print("deterministic: an eavesdropper encrypts both possible votes and")
    print(f"  matches the ciphertext: recovers vote {guess[0]}"
          f" (correct: {guess == [vote]})")
    c1, c2 = pow(6, e, n), pow(7, e, n)
    print("malleable: E(6) * E(7) = E(42) (mod n):",
          c1 * c2 % n == pow(42, e, n))
    print()
    f = smallest_factor(n)
    phi = (f - 1) * (n // f - 1)
    print(f"trial division factors n: {f} * {n // f}")
    print("private key recovered from the factors:", pow(e, -1, phi) == d)
    print()
    print("Epistemic status: exact computations on one seeded toy key. They")
    print("check RSA's correctness on examples (the lesson proves it for all")
    print("messages) and show weaknesses of textbook RSA with tiny keys. They")
    print("say nothing about the security of 2048-bit RSA, which is unproved.")


if __name__ == "__main__":
    main()
