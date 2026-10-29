"""The subobject classifier of a presheaf topos, computed exactly.

For presheaves on a finite poset P, the classifier Omega has Omega(p) = the
sieves on p (down-closed subsets of the principal down-set of p), and the
global truth values are the down-sets of P. This experiment

1. counts sieves on a chain (|Omega(k)| = k + 2) and on other small posets;
2. checks, for every presheaf A on {0 < 1} with |A1| <= 4 and |A0| <= 3,
   that A has exactly as many subpresheaves as natural maps A -> Omega, and
   that the characteristic map chi is a bijection between them;
3. computes the Heyting algebra of truth values and finds where excluded
   middle fails.

Evidence: exact computation and exhaustive checks of finitely many cases.
"""

import itertools
import textwrap

EXPERIMENT = {
    "id": "elementary_topoi_omega",
    "title": "Truth values in presheaf toposes",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["elementary-topoi"],
    "summary": (
        "Computes the sieves Omega(p) for presheaves on small finite posets, "
        "checks exhaustively for all presheaves on {0 < 1} with at most 4 and "
        "3 sections that the characteristic map is a bijection from "
        "subpresheaves to natural maps into Omega, and computes Heyting "
        "negation on truth values, exhibiting failures of excluded middle. "
        "Finite cases only: the general theorems are proved in the lesson."
    ),
    "packages": [],
}


def down_sets(elements, leq):
    """All down-closed subsets of the finite poset (elements, leq)."""
    found = []
    for r in range(len(elements) + 1):
        for combo in itertools.combinations(elements, r):
            s = frozenset(combo)
            if all(q in s for p in s for q in elements if leq(q, p)):
                found.append(s)
    return found


def sieves_on(p, elements, leq):
    """Sieves on p: down-closed subsets of {q | q <= p}."""
    below = [q for q in elements if leq(q, p)]
    return down_sets(below, leq)


def chain(n):
    """The chain 0 < 1 < ... < n-1 as (elements, leq)."""
    return list(range(n)), lambda a, b: a <= b


def heyting_implies(u, v, opens):
    """Largest member w of `opens` with w & u <= v (the Heyting implication)."""
    best = frozenset()
    for w in opens:
        if w & u <= v:
            best = best | w
    assert best in opens
    return best


def excluded_middle_failures(elements, leq):
    """Down-sets u with u | (not u) != everything, where not u = u => empty."""
    opens = down_sets(elements, leq)
    top = frozenset(elements)
    return [u for u in opens
            if u | heyting_implies(u, frozenset(), opens) != top]


OMEGA1 = [(a, b) for a in (False, True) for b in (False, True) if a <= b]


def subpresheaves(a1, a0, res):
    """Pairs (S1, S0) of subsets with res(S1) inside S0."""
    subs = []
    for r0 in range(a0 + 1):
        for s0 in itertools.combinations(range(a0), r0):
            for r1 in range(a1 + 1):
                for s1 in itertools.combinations(range(a1), r1):
                    if all(res[x] in s0 for x in s1):
                        subs.append((frozenset(s1), frozenset(s0)))
    return subs


def natural_maps(a1, a0, res):
    """Natural maps A -> Omega: (f1, f0) with f1(x)[1] == f0(res x)."""
    maps = []
    for f0 in itertools.product((False, True), repeat=a0):
        for f1 in itertools.product(OMEGA1, repeat=a1):
            if all(f1[x][1] == f0[res[x]] for x in range(a1)):
                maps.append((f1, f0))
    return maps


def chi(sub, a1, a0, res):
    """Characteristic map of a subpresheaf (S1, S0)."""
    s1, s0 = sub
    f1 = tuple((x in s1, res[x] in s0) for x in range(a1))
    return f1, tuple(y in s0 for y in range(a0))


def check_classifier(max1=4, max0=3):
    """Return (presheaves checked, failures) for the bijection Sub = Hom."""
    checked, failures = 0, []
    for a1 in range(max1 + 1):
        for a0 in range(max0 + 1):
            for res in itertools.product(range(a0), repeat=a1):
                subs = subpresheaves(a1, a0, res)
                maps = set(natural_maps(a1, a0, res))
                images = {chi(s, a1, a0, res) for s in subs}
                if len(images) != len(subs) or images != maps:
                    failures.append((a1, a0, res))
                checked += 1
    return checked, failures


POSETS = {
    "{0<1}": chain(2),
    "chain of 3": chain(3),
    "0 < 2 > 1": ([0, 1, 2], lambda a, b: a == b or b == 2),
    "discrete 3": ([0, 1, 2], lambda a, b: a == b),
}


def main():
    elems, leq = chain(5)
    sizes = [len(sieves_on(k, elems, leq)) for k in elems]
    print(f"Chain 0<1<2<3<4: |Omega(k)| = {sizes} (k + 2 each)")
    print()
    checked, failures = check_classifier()
    print("Presheaves A on {0<1} with |A1| <= 4, |A0| <= 3 (all restrictions):")
    print(f"  {checked} presheaves; chi : Sub(A) -> Hom(A, Omega) failed to be a")
    print(f"  bijection in {len(failures)} of them.")
    a1, a0, res = 3, 2, (0, 0, 1)
    n_sub = len(subpresheaves(a1, a0, res))
    print(f"  Example res = {res}: {n_sub} subpresheaves = (1 + 2^2)(1 + 2^1).")
    print()
    print("Global truth values = down-sets of P:")
    for name, (el, le) in POSETS.items():
        opens = down_sets(el, le)
        bad = excluded_middle_failures(el, le)
        status = "Boolean" if not bad else f"not Boolean ({len(bad)} fail LEM)"
        print(f"  {name:<12} {len(opens):>2} truth values, {status}")
    el, le = chain(2)
    opens = down_sets(el, le)
    half = frozenset({0})
    neg = heyting_implies(half, frozenset(), opens)
    negneg = heyting_implies(neg, frozenset(), opens)
    print("In {0<1}: u = {0} ('true only after restriction'):")
    print(f"  not u = {sorted(neg)}, not not u = {sorted(negneg)},"
          f" u or not u = {sorted(half | neg)}")
    print()
    print(textwrap.fill(
        "Epistemic status: exact computations and an exhaustive check of "
        f"{checked} small presheaves. They illustrate, but do not prove, the "
        "theorems that Omega classifies subobjects in every presheaf topos "
        "and that its truth values form a Heyting algebra; those are proved "
        "in the lesson, and the {0<1} case is also checked in Lean.",
        width=78,
    ))


if __name__ == "__main__":
    main()
