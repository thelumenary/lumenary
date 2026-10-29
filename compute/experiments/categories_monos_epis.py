"""Monomorphisms and epimorphisms in finite sets, decided by brute force.

A function f : A -> B is a monomorphism if f . g = f . h forces g = h for
all maps g, h : T -> A, and an epimorphism if g . f = h . f forces g = h
for all maps g, h : B -> T. Both definitions quantify over *every* test
set T. This experiment enumerates every function between sets with at most
three elements, tests the definitions against all test sets with at most
two elements, and compares the answers with injectivity and surjectivity.
It also shows which test sets are needed: a one-element T already detects
monos, but epis need a two-element T. The evidence is exhaustive for these
small sets; the lesson's proof covers all sets.
"""

from itertools import product

EXPERIMENT = {
    "id": "categories_monos_epis",
    "title": "Monos and epis in finite sets, by brute force",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["categories"],
    "summary": (
        "Enumerates every function between sets of size 0 to 3, decides "
        "whether it is a monomorphism or an epimorphism straight from the "
        "cancellation definitions (testing against every map from or to a set "
        "of size at most 2), and checks that monos are exactly the injections "
        "and epis exactly the surjections. Exhaustive for these sizes only; "
        "the proof in the lesson covers all sets."
    ),
    "packages": [],
}


def functions(m, n):
    """All functions {0..m-1} -> {0..n-1}, each as a tuple of values."""
    return list(product(range(n), repeat=m))


def compose(g, f):
    """The composite g . f of tuples: first f, then g."""
    return tuple(g[x] for x in f)


def is_mono(f, n, test_sizes):
    """Is f : m -> n left-cancellable against maps from sets of these sizes?"""
    m = len(f)
    for t in test_sizes:
        maps = functions(t, m)
        for g in maps:
            for h in maps:
                if g != h and compose(f, g) == compose(f, h):
                    return False
    return True


def is_epi(f, n, test_sizes):
    """Is f : m -> n right-cancellable against maps to sets of these sizes?"""
    for t in test_sizes:
        maps = functions(n, t)
        for g in maps:
            for h in maps:
                if g != h and compose(g, f) == compose(h, f):
                    return False
    return True


def is_injective(f):
    """No two inputs share an output."""
    return len(set(f)) == len(f)


def is_surjective(f, n):
    """Every element of {0..n-1} is a value."""
    return set(f) == set(range(n))


def tally(m, n, test_sizes=(0, 1, 2)):
    """Counts (functions, monos, injections, epis, surjections) for m -> n."""
    fs = functions(m, n)
    return (
        len(fs),
        sum(is_mono(f, n, test_sizes) for f in fs),
        sum(is_injective(f) for f in fs),
        sum(is_epi(f, n, test_sizes) for f in fs),
        sum(is_surjective(f, n) for f in fs),
    )


def main():
    print("|A| |B|  maps  monos  injective  epis  surjective")
    agree = True
    for m in range(4):
        for n in range(4):
            total, mono, inj, epi, surj = tally(m, n)
            agree = agree and mono == inj and epi == surj
            print(f"{m:>3} {n:>3} {total:>5} {mono:>6} {inj:>10}"
                  f" {epi:>5} {surj:>11}")
    print(f"monos = injections and epis = surjections: {agree}")
    print()
    print("Which test sets T are needed?")
    fake = sum(is_epi(f, 3, (1,)) for f in functions(2, 3))
    print(f"  with |T| = 1 only, {fake} of the 9 maps 2 -> 3 pass the epi test,")
    print("  although none of them is surjective")
    ok = all(is_mono(f, 3, (1,)) == is_injective(f) for f in functions(3, 3))
    print(f"  |T| = 1 already decides mono for all 27 maps 3 -> 3: {ok}")
    print()
    print("Epistemic status: exhaustive and exact for sets with at most three")
    print("elements, testing against all sets with at most two elements. It is")
    print("evidence, not proof, that the pattern continues; the lesson proves")
    print("mono = injective and epi = surjective for all sets, using a")
    print("one-element and a two-element test set exactly as found here.")


if __name__ == "__main__":
    main()
