"""Chaining functions given by tables, and undoing chains in the right order.

Functions on finite sets are stored as Python dictionaries, so "f, then g"
is computed by looking up g[f[a]]. The experiment chains two tables, then
runs through all 27 functions from {0, 1, 2} to itself: it checks the
identity laws, finds which functions can be undone (exactly the 6 that never
send two inputs to the same output), and tests the "socks and shoes" rule
for undoing a chain on every pair of them - and how often undoing in the
WRONG order happens to work. Last, it converts temperatures exactly with
fractions. Exact, exhaustive-finite evidence.
"""

from fractions import Fraction
from itertools import product

EXPERIMENT = {
    "id": "chaining_functions_tables",
    "title": "Chaining tables, and undoing chains in the right order",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["chaining-functions"],
    "summary": (
        "Chains functions stored as tables (people -> cities -> continents). "
        "For all 27 functions on {0, 1, 2} it checks the identity laws, finds "
        "the 6 that can be undone, confirms the socks-and-shoes rule on all 36 "
        "pairs of them, and finds that undoing in the wrong order works exactly "
        "for the 18 pairs that commute. It also converts 30 C to F and back "
        "with exact fractions. Exhaustive for this 3-element set only."
    ),
    "packages": [],
}


def then(f, g):
    """The table of 'f, then g': a -> g[f[a]]. Every output of f must be an
    input of g, otherwise the chain is not defined."""
    missing = [b for b in f.values() if b not in g]
    if missing:
        raise ValueError(f"outputs {missing} are not inputs of the second table")
    return {a: g[f[a]] for a in f}


def identity(elements):
    """The identity function on a finite set, as a table."""
    return {a: a for a in elements}


def undoes(g, f):
    """True when g undoes f: g[f[a]] == a for every input a of f."""
    return all(f[a] in g and g[f[a]] == a for a in f)


def all_functions(elements):
    """Every function from the finite set to itself (n**n of them)."""
    elements = list(elements)
    for outputs in product(elements, repeat=len(elements)):
        yield dict(zip(elements, outputs))


def undoing_function(f, elements):
    """A function g on `elements` that undoes f, or None if there is none."""
    for g in all_functions(elements):
        if undoes(g, f):
            return g
    return None


def to_fahrenheit(c):
    """Multiply by 9/5, then add 32."""
    return Fraction(9, 5) * c + 32


def to_celsius(f):
    """Subtract 32, then multiply by 5/9: the undo steps in reverse order."""
    return Fraction(5, 9) * (f - 32)


def wrong_undo(f):
    """Multiply by 5/9, then subtract 32: the undo steps in the wrong order."""
    return Fraction(5, 9) * f - 32


HOME_CITY = {"Amina": "Kano", "Bo": "Chengdu", "Carlos": "Lima",
             "Dilnoza": "Tashkent", "Emma": "Oslo"}
CONTINENT = {"Kano": "Africa", "Chengdu": "Asia", "Lima": "South America",
             "Tashkent": "Asia", "Oslo": "Europe", "Perth": "Oceania"}


def main():
    print("1. Two tables in sequence: home city, then continent")
    for person, place in then(HOME_CITY, CONTINENT).items():
        print(f"   {person:<8} -> {HOME_CITY[person]:<9} -> {place}")
    print()
    elems = [0, 1, 2]
    funcs = list(all_functions(elems))
    ident = identity(elems)
    ok = all(then(ident, f) == f and then(f, ident) == f for f in funcs)
    print(f"2. All {len(funcs)} functions from {{0, 1, 2}} to itself")
    print("   identity, then f == f == f, then identity, for all f:", ok)
    pairs = sum(then(f, g) == then(g, f) for f in funcs for g in funcs)
    print(f"   pairs (f, g) where the order does not matter: {pairs} of 729")
    undo = [(f, undoing_function(f, elems)) for f in funcs]
    undo = [(f, u) for f, u in undo if u is not None]
    print(f"   functions that can be undone: {len(undo)}")
    right, wrong, swap = 0, set(), set()
    for (i, (f, uf)), (j, (g, ug)) in product(enumerate(undo), repeat=2):
        right += undoes(then(ug, uf), then(f, g))
        if undoes(then(uf, ug), then(f, g)):
            wrong.add((i, j))
        if then(f, g) == then(g, f):
            swap.add((i, j))
    total = len(undo) ** 2
    print(f"   'f, then g' undone by 'undo g, then undo f': {right} of {total}")
    print(f"   undone by 'undo f, then undo g' (wrong order): {len(wrong)} of {total}")
    print(f"   ... and those {len(wrong)} are exactly the pairs where f and g")
    print(f"   can be swapped: {wrong == swap}")
    print()
    print("3. Temperatures, with exact fractions")
    f = to_fahrenheit(30)
    print(f"   30 C -> {f} F -> back: {to_celsius(f)} C (right order)")
    print(f"   wrong order gives {wrong_undo(f)} C, about {float(wrong_undo(f)):.1f}")
    print()
    print("Epistemic status: exact and exhaustive for the 27 functions on a")
    print("3-element set. The lesson proves the socks-and-shoes rule for all")
    print("functions. That the wrong order works exactly when f and g can be")
    print("swapped is checked here for 36 pairs only; exercise: prove it.")


if __name__ == "__main__":
    main()
