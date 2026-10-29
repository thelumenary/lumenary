"""Checking statements about sets and functions on every small example.

Before proving a statement in Lean it pays to test it. Here we check, on all
functions between sets of size at most 3:

* f(S & T) = f(S) & f(T) for all subsets S, T holds exactly when f is
  injective (Mathlib's Set.image_inter needs that hypothesis);
* if g o f is injective then f is injective - and g need not be;
* for every relation P on small sets, "exists x, for all y, P(x, y)" implies
  "for all y, exists x, P(x, y)", but not conversely.

An exhaustive search over a finite universe can refute a general claim (one
counterexample suffices) but can never prove it for all sets.
"""

import itertools

EXPERIMENT = {
    "id": "formal_proof_lean_finite_models",
    "title": "Images, composites and quantifiers on all small examples",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["formal-proof-lean"],
    "summary": (
        "Checks on every function between sets of size at most 3 that images "
        "preserve intersections exactly for injective functions, that g o f "
        "injective forces f (but not g) to be injective, and on every relation "
        "between sets of size at most 3 that exists-forall implies forall-exists "
        "but not conversely, printing the smallest counterexamples."
    ),
    "packages": [],
}


def functions(a, b):
    """All functions from range(a) to range(b), as tuples of values."""
    return list(itertools.product(range(b), repeat=a))


def subsets(n):
    """All subsets of range(n), as frozensets."""
    return [frozenset(c) for k in range(n + 1)
            for c in itertools.combinations(range(n), k)]


def image(f, s):
    """The image f(s) of a set s under a function given as a tuple."""
    return frozenset(f[x] for x in s)


def is_injective(f):
    """True if no two inputs share an output."""
    return len(set(f)) == len(f)


def preserves_intersections(f):
    """True if f(S & T) == f(S) & f(T) for all subsets S, T of the domain."""
    subs = subsets(len(f))
    return all(image(f, s & t) == image(f, s) & image(f, t)
               for s in subs for t in subs)


def compose(g, f):
    """The composite g o f of functions given as tuples."""
    return tuple(g[y] for y in f)


def exists_forall(rel, a, b):
    """Exists x in range(a) such that for all y in range(b), (x, y) in rel."""
    return any(all((x, y) in rel for y in range(b)) for x in range(a))


def forall_exists(rel, a, b):
    """For all y in range(b) there exists x in range(a) with (x, y) in rel."""
    return all(any((x, y) in rel for x in range(a)) for y in range(b))


def relations(a, b):
    """All relations between range(a) and range(b), as frozensets of pairs."""
    pairs = [(x, y) for x in range(a) for y in range(b)]
    return [frozenset(p for p, keep in zip(pairs, bits) if keep)
            for bits in itertools.product([False, True], repeat=len(pairs))]


def main():
    total = agree = 0
    for a in range(4):
        for b in range(1, 4):
            for f in functions(a, b):
                total += 1
                agree += preserves_intersections(f) == is_injective(f)
    print("1. f(S & T) = f(S) & f(T) for all S, T  <=>  f injective")
    print(f"   checked on all {total} functions between sets of size <= 3:"
          f" agrees in {agree}")
    f = (0, 0)
    s, t = frozenset({0}), frozenset({1})
    print(f"   smallest counterexample: f = {f}, S = {{0}}, T = {{1}}:")
    print(f"   f(S & T) = {set(image(f, s & t))},"
          f" f(S) & f(T) = {set(image(f, s) & image(f, t))}")
    print()
    bad_f = bad_g = 0
    example = None
    for a, b, c in itertools.product(range(1, 4), repeat=3):
        for f in functions(a, b):
            for g in functions(b, c):
                if is_injective(compose(g, f)):
                    bad_f += not is_injective(f)
                    if not is_injective(g):
                        bad_g += 1
                        example = example or (f, g)
    print("2. g o f injective: cases where f is not injective:", bad_f)
    print("   cases where g is not injective:", bad_g,
          f"(e.g. f = {example[0]}, g = {example[1]})")
    print()
    imp = conv = count = 0
    for a in range(1, 4):
        for b in range(1, 4):
            for rel in relations(a, b):
                count += 1
                ef, fe = exists_forall(rel, a, b), forall_exists(rel, a, b)
                imp += ef and not fe
                conv += fe and not ef
    print(f"3. all {count} relations between sets of size 1 to 3:")
    print(f"   exists-forall true but forall-exists false: {imp}")
    print(f"   forall-exists true but exists-forall false: {conv}")
    print("   e.g. P = equality on {0, 1}: every y has x = y, no x fits all")
    print()
    print("Epistemic status: exhaustive checks over finitely many small sets.")
    print("The counterexamples refute the general claims for good; the")
    print("agreements are evidence only. The general theorems are proved in")
    print("the lesson and in Lean (image_inter_of_injective, injective_of_comp,")
    print("exists_forall_imp).")


if __name__ == "__main__":
    main()
