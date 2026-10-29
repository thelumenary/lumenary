"""Set-builder notation as Python set comprehensions, and why N is infinite.

{n in A : P(n)} becomes {n for n in A if P(n)}, and {2k : k in A} becomes
{2 * k for k in A}. The experiment checks that two descriptions of the even
numbers agree on a finite range, lists a few small sets, then plays the
"infinite set" game: whatever finite list of natural numbers you give, one
more than its largest element is missing, and twice that is a missing even
number. Exact computation on finite ranges and sample lists; the lesson
proves the general statements.
"""

EXPERIMENT = {
    "id": "quantifiers_set_builder",
    "title": "Set-builder notation in Python, and lists that miss numbers",
    "evidence": ["exact"],
    "lessons": ["quantifiers"],
    "summary": (
        "Writes set-builder descriptions as Python set comprehensions: two "
        "descriptions of the even numbers agree on 0..999, and small sets such "
        "as {x in Z : x*x < 10} are listed. Then, for sample finite lists of "
        "natural numbers, it finds a missing natural number (largest "
        "+ 1) and a missing even number. Exact on the cases shown; the "
        "lesson's proofs cover every list."
    ),
    "packages": [],
}


def evens_by_property(limit):
    """{n in {0..limit-1} : n is even}."""
    return {n for n in range(limit) if n % 2 == 0}


def evens_by_formula(limit):
    """{2k : k in N, 2k < limit}."""
    return {2 * k for k in range((limit + 1) // 2)}


def small_squares():
    """{x in Z : x * x < 10}. Searching -10..10 is enough, because
    |x| >= 4 gives x * x >= 16."""
    return sorted(x for x in range(-10, 11) if x * x < 10)


def primes_below(n):
    """{p in N : p is prime and p < n}."""
    return [p for p in range(2, n) if all(p % d for d in range(2, p))]


def missing_natural(numbers):
    """A natural number not in the finite list: one more than the largest."""
    return max(numbers, default=-1) + 1


def missing_even(numbers):
    """An even natural number not in the finite list."""
    return 2 * (max(numbers, default=-1) + 1)


def main():
    print("1. Set-builder notation as set comprehensions")
    same = evens_by_property(1000) == evens_by_formula(1000)
    print("   {n < 1000 : n even} == {2k : 2k < 1000}:", same)
    print("   {x in Z : x*x < 10} =", small_squares())
    print("   {p prime : p < 30} =", primes_below(30))
    print("   {n in 0..99 : n < 0} =", {n for n in range(100) if n < 0},
          "(the empty set)")
    print()
    print("2. No finite list contains every natural number")
    lists = [[], [0, 1, 2, 3], [7, 3, 12], [2, 4, 6, 8, 10, 12],
             [5, 10 ** 6, 41]]
    for nums in lists:
        n, e = missing_natural(nums), missing_even(nums)
        assert n not in nums and e not in nums and e % 2 == 0
        print(f"   {str(nums):<22} misses {n:>7} and the even number {e:>7}")
    print("   Whatever finite list you write, the recipe finds a number it")
    print("   misses - so N and the even numbers are infinite.")
    print()
    print("Epistemic status: exact computations. Part 1 compares two")
    print("descriptions only on 0..999, and part 2 tries five lists; neither")
    print("is a proof about all numbers. The lesson proves that largest + 1")
    print("is missing from every finite list (and Lean checks the proof).")


if __name__ == "__main__":
    main()
