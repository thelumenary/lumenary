"""Russell's argument as a finite search.

Russell's paradox rests on a fact of pure logic: for any relation E on any
collection, no r has  x E r  <->  not (x E x)  for every x.  Here we test that
fact exhaustively on every relation on a set of at most 4 elements, reading
"x E y" as "x is a member of y" (or as "y shaves x"). The proof says why it
must fail: the candidate r disagrees with the Russell set at r itself.

Then we build the hereditarily finite sets V_0, ..., V_4 (sets of sets of ...
of the empty set; |V_4| = 16) and check that for every A among them the set
R_A = {x in A : x not in x} produced by the separation axiom is not an element
of A. (In fact no hereditarily finite set is a member of itself, so R_A is A.)

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from itertools import combinations, product

EXPERIMENT = {
    "id": "russell_paradox_relations",
    "title": "Russell's argument as a finite search",
    "evidence": ["exhaustive-finite"],
    "lessons": ["russell-paradox"],
    "summary": (
        "Checks every relation on sets of 1 to 4 elements (66 066 relations) and "
        "finds that no element ever has as its members exactly the elements that "
        "are not members of themselves; then builds the hereditarily finite sets "
        "up to V_4 and checks that the separated Russell set of each is not an "
        "element of it. Finite evidence for theorems the lesson proves in general."
    ),
    "packages": [],
}


def relations(n):
    """All relations on {0, ..., n-1}, as frozensets of pairs (x, y) meaning
    'x E y'."""
    pairs = [(x, y) for x in range(n) for y in range(n)]
    for mask in product([False, True], repeat=len(pairs)):
        yield frozenset(p for p, keep in zip(pairs, mask) if keep)


def russell_set(rel, n):
    """{x : not (x E x)}."""
    return frozenset(x for x in range(n) if (x, x) not in rel)


def members(rel, r, n):
    """{x : x E r}."""
    return frozenset(x for x in range(n) if (x, r) in rel)


def russell_witnesses(rel, n):
    """All r whose members are exactly the Russell set (always empty)."""
    target = russell_set(rel, n)
    return [r for r in range(n) if members(rel, r, n) == target]


def search(n):
    """(number of relations on n elements, number with a Russell witness)."""
    count = found = 0
    for rel in relations(n):
        count += 1
        found += bool(russell_witnesses(rel, n))
    return count, found


def hereditarily_finite(levels):
    """V_0 = {} and V_(k+1) = all subsets of V_k, as frozensets of frozensets.
    Returns the list [V_0, ..., V_levels]."""
    v = [frozenset()]
    for _ in range(levels):
        prev = sorted(v[-1], key=id_of)
        subsets = [frozenset(c) for k in range(len(prev) + 1)
                   for c in combinations(prev, k)]
        v.append(frozenset(subsets))
    return v


def id_of(s):
    """A canonical string for a hereditarily finite set, e.g. {{}, {{}}}."""
    return "{" + ", ".join(sorted(id_of(x) for x in s)) + "}"


def separated_russell(a):
    """R_A = {x in A : x not in x}, formed by separation inside A."""
    return frozenset(x for x in a if x not in x)


def main():
    print("n  relations on n elements  with a 'Russell element' r")
    total = 0
    for n in range(1, 5):
        count, found = search(n)
        total += count
        print(f"{n}  {count:23d}  {found:28d}")
    print(f"Checked {total} relations: no r ever has x E r <-> not x E x.")
    print()
    v = hereditarily_finite(4)
    print("Hereditarily finite sets: |V_k| for k = 0..4:",
          ", ".join(str(len(level)) for level in v))
    sets = v[4]
    self_members = sum(1 for a in sets if a in a)
    r_not_in = sum(1 for a in sets if separated_russell(a) not in a)
    equal = sum(1 for a in sets if separated_russell(a) == a)
    print(f"Sets A in V_4 with A in A: {self_members}")
    print(f"Sets A in V_4 with R_A not in A: {r_not_in} of {len(sets)}")
    print(f"... and R_A = A (nothing in A contains itself): {equal} of {len(sets)}")
    print("Example: A = " + id_of(max(sets, key=len)))
    print()
    print("Epistemic status: an exhaustive check of finitely many relations and")
    print("sets. It cannot reach infinite collections; the one-line proof in")
    print("the lesson covers every relation on every collection, finite or not.")


if __name__ == "__main__":
    main()
