"""A census of every binary operation on a three-element set, and of Z/nZ.

There are 3^9 = 19 683 binary operations on S = {0, 1, 2}: one for each way of
filling in a 3 x 3 operation table. The experiment checks every one of them for
associativity, identities and inverses, counts the monoids and groups, and
confirms on all of them the lesson's theorems that an identity is unique and
that inverses in a monoid are unique. Then it decides, for n = 2, ..., 40,
whether Z/nZ is a field by searching for inverses. Everything is exact and
exhaustive for these finite cases - evidence about small cases, not a proof
of the general theorems.
"""

import itertools
import math

EXPERIMENT = {
    "id": "algebraic_structures_census",
    "title": "A census of binary operations and of Z/nZ",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["algebraic-structures"],
    "summary": (
        "Checks all 19,683 operation tables on a 3-element set: counts the "
        "associative ones (113), the monoids and the groups, and confirms that "
        "no table has two identities and no monoid element has two inverses. "
        "Then finds for which n up to 40 every non-zero class of Z/nZ has an "
        "inverse (exactly the primes). Exhaustive for these cases only."
    ),
    "packages": [],
}

S = (0, 1, 2)


def all_tables(size=3):
    """Yield every operation table on {0, ..., size-1} as a dict (a, b) -> a*b."""
    elems = range(size)
    pairs = [(a, b) for a in elems for b in elems]
    for values in itertools.product(elems, repeat=len(pairs)):
        yield dict(zip(pairs, values))


def is_associative(op, elems=S):
    """True if (ab)c = a(bc) for all a, b, c."""
    return all(op[op[a, b], c] == op[a, op[b, c]]
               for a in elems for b in elems for c in elems)


def identities(op, elems=S):
    """All two-sided identity elements e (ea = a = ae for every a)."""
    return [e for e in elems
            if all(op[e, a] == a and op[a, e] == a for a in elems)]


def inverses(op, a, e, elems=S):
    """All two-sided inverses of a with respect to the identity e."""
    return [b for b in elems if op[a, b] == e and op[b, a] == e]


def is_commutative(op, elems=S):
    """True if ab = ba for all a, b."""
    return all(op[a, b] == op[b, a] for a in elems for b in elems)


def census(size=3):
    """Count operations by kind, and record any failure of uniqueness."""
    elems = tuple(range(size))
    counts = {"tables": 0, "associative": 0, "with identity": 0,
              "monoids": 0, "commutative monoids": 0, "groups": 0}
    max_ids, max_invs = 0, 0
    for op in all_tables(size):
        counts["tables"] += 1
        ids = identities(op, elems)
        max_ids = max(max_ids, len(ids))
        counts["with identity"] += bool(ids)
        if not is_associative(op, elems):
            continue
        counts["associative"] += 1
        if not ids:
            continue
        counts["monoids"] += 1
        counts["commutative monoids"] += is_commutative(op, elems)
        invs = [inverses(op, a, ids[0], elems) for a in elems]
        max_invs = max(max_invs, max(len(i) for i in invs))
        counts["groups"] += all(invs)
    return counts, max_ids, max_invs


def units_mod(n):
    """The classes a in Z/nZ with some b such that ab = 1 (mod n)."""
    return [a for a in range(n) if any(a * b % n == 1 % n for b in range(n))]


def is_field_mod(n):
    """Z/nZ is a field: 0 != 1 and every non-zero class has an inverse."""
    return n > 1 and len(units_mod(n)) == n - 1


def is_prime(n):
    """Trial division."""
    return n > 1 and all(n % d for d in range(2, math.isqrt(n) + 1))


def main():
    counts, max_ids, max_invs = census()
    print("All binary operations on S = {0, 1, 2}:")
    for kind, number in counts.items():
        print(f"  {kind:<22}{number:>6}")
    print(f"  most identities in one table:          {max_ids}")
    print(f"  most inverses of one element (monoid): {max_invs}")
    print("  (Groups: S has 3 choices of identity, each giving a copy of Z/3.)")
    print()
    fields = [n for n in range(2, 41) if is_field_mod(n)]
    primes = [n for n in range(2, 41) if is_prime(n)]
    print("Z/nZ is a field for n in 2..40 exactly when n is in:")
    print("  " + ", ".join(map(str, fields)))
    print(f"  same as the primes up to 40: {fields == primes}")
    for n in (12, 13):
        print(f"  units of Z/{n}Z: {units_mod(n)}")
    print()
    print("Epistemic status: exact, exhaustive checks of finitely many cases.")
    print("They agree with the theorems (an identity is unique, inverses in a")
    print("monoid are unique, Z/nZ is a field iff n is prime) but prove them only")
    print("for |S| = 3 and n <= 40; the proofs in the lesson cover every case.")


if __name__ == "__main__":
    main()
