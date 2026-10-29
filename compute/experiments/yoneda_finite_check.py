"""The Yoneda lemma, checked by brute force in small finite categories.

For a finite category C, an object A and a functor F : C -> FinSet, we list
every family of functions alpha_B : Hom(A, B) -> F(B) and keep the natural
ones. The Yoneda lemma predicts exactly |F(A)| of them, and that
alpha -> alpha_A(id_A) is a bijection. We test this for directed graphs
(functors on the category E ⇉ V), for actions of the four-element monoid
of all maps {0, 1} -> {0, 1}, and for a group action. Then the one-object
case: among all 720 permutations of the six elements of S3, exactly six
commute with every right multiplication, and they are the left
multiplications (Cayley). Finally the poset case for divisibility. This is
exhaustive evidence in finitely many cases; the lemma is proved in general.
"""

import itertools

EXPERIMENT = {
    "id": "yoneda_finite_check",
    "title": "The Yoneda lemma by brute force in finite categories",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["yoneda"],
    "summary": (
        "Enumerates every family of maps Hom(A, B) -> F(B) for functors on "
        "small finite categories (directed graphs, actions of a 4-element "
        "monoid, a group action) and keeps the natural ones: there are always "
        "exactly |F(A)|, matched bijectively by alpha -> alpha_A(id_A). Also "
        "finds the 6 permutations of S3 commuting with right multiplication "
        "(Cayley) and checks Yoneda for divisibility. Exhaustive in these "
        "finite cases only."
    ),
    "packages": [],
}


class FiniteCategory:
    """Objects, named arrows with (domain, codomain), identities and a
    composition table ``comp[(g, f)] = g ∘ f`` (first f, then g)."""

    def __init__(self, arrows, identities, comp):
        self.arrows = arrows
        self.identities = identities
        self.comp = comp
        self.objects = list(identities)

    def hom(self, a, b):
        """Names of the arrows a -> b."""
        return [f for f, (d, c) in self.arrows.items() if d == a and c == b]


def natural_transformations(cat, a, obj, arr):
    """All natural transformations Hom(a, −) => F, by brute force.

    ``obj[B]`` is the set F(B) (a list), ``arr[g]`` the function F(g) (a
    dict). A candidate picks, for every B and every f : a -> B, an element of
    F(B); it is natural if alpha(g ∘ f) = F(g)(alpha(f)) for all composable
    g, f. Returns the list of natural ones (each a dict f -> element) and
    the number of candidates examined.
    """
    slots = [f for b in cat.objects for f in cat.hom(a, b)]
    choices = [obj[cat.arrows[f][1]] for f in slots]
    natural, candidates = [], 0
    for values in itertools.product(*choices):
        candidates += 1
        alpha = dict(zip(slots, values))
        if all(alpha[cat.comp[(g, f)]] == arr[g][alpha[f]]
               for f in slots for g, (d, _) in cat.arrows.items()
               if d == cat.arrows[f][1]):
            natural.append(alpha)
    return natural, candidates


def yoneda_check(cat, a, obj, arr):
    """(number of natural transformations, |F(a)|, candidates, whether
    alpha -> alpha_a(id_a) is a bijection onto F(a))."""
    nats, candidates = natural_transformations(cat, a, obj, arr)
    images = [alpha[cat.identities[a]] for alpha in nats]
    bijective = sorted(images, key=repr) == sorted(obj[a], key=repr)
    return len(nats), len(obj[a]), candidates, bijective


def parallel_pair():
    """The category E ⇉ V: a functor out of it is a directed graph."""
    arrows = {"1E": ("E", "E"), "1V": ("V", "V"), "s": ("E", "V"), "t": ("E", "V")}
    comp = {("1E", "1E"): "1E", ("1V", "1V"): "1V", ("s", "1E"): "s",
            ("t", "1E"): "t", ("1V", "s"): "s", ("1V", "t"): "t"}
    return FiniteCategory(arrows, {"E": "1E", "V": "1V"}, comp)


def monoid_category(elements, mul, one):
    """A monoid as a category with one object '*'."""
    arrows = {m: ("*", "*") for m in elements}
    comp = {(g, f): mul(g, f) for g in elements for f in elements}
    return FiniteCategory(arrows, {"*": one}, comp)


#: The monoid of all maps {0,1} -> {0,1}, written as (image of 0, image of 1).
T2 = [(0, 1), (1, 0), (0, 0), (1, 1)]


def t2_mul(g, f):
    """g ∘ f: first f, then g."""
    return (g[f[0]], g[f[1]])


def examples():
    """(description, category, object, F on objects, F on arrows)."""
    out = []
    pp = parallel_pair()
    edges = {"e1": ("a", "b"), "e2": ("b", "c"), "e3": ("c", "a"), "e4": ("a", "a")}
    g_obj = {"E": list(edges), "V": ["a", "b", "c"]}
    g_arr = {"1E": {e: e for e in edges}, "1V": {v: v for v in "abc"},
             "s": {e: st[0] for e, st in edges.items()},
             "t": {e: st[1] for e, st in edges.items()}}
    out.append(("graph, A = E (edges)", pp, "E", g_obj, g_arr))
    out.append(("graph, A = V (vertices)", pp, "V", g_obj, g_arr))
    t2 = monoid_category(T2, t2_mul, (0, 1))
    pts = [0, 1]
    out.append(("T2 acting on {0,1}", t2, "*", {"*": pts},
                {m: {x: m[x] for x in pts} for m in T2}))
    subs = [frozenset(s) for s in ([], [0], [1], [0, 1])]
    out.append(("T2 acting on subsets (image)", t2, "*", {"*": subs},
                {m: {s: frozenset(m[x] for x in s) for s in subs} for m in T2}))
    z3 = monoid_category([0, 1, 2], lambda g, f: (g + f) % 3, 0)
    six = [(i, j) for i in range(3) for j in range(2)]
    out.append(("Z/3 rotating 3 + 3 points", z3, "*", {"*": six},
                {g: {(i, j): ((i + g) % 3, j) for i, j in six} for g in range(3)}))
    return out


def cayley_check():
    """Permutations of S3 commuting with all right multiplications, and
    whether they are exactly the left multiplications."""
    s3 = list(itertools.permutations(range(3)))

    def mul(p, q):
        return tuple(p[q[i]] for i in range(3))

    commuting = []
    for images in itertools.permutations(s3):
        sigma = dict(zip(s3, images))
        if all(sigma[mul(x, h)] == mul(sigma[x], h) for x in s3 for h in s3):
            commuting.append(sigma)
    lefts = [{x: mul(g, x) for x in s3} for g in s3]
    return len(commuting), sorted(map(repr, commuting)) == sorted(map(repr, lefts))


def divisibility_check(n):
    """Yoneda for the poset ({1..n}, |): a | b iff every divisor of a
    divides b. Returns the number of pairs checked and of failures."""
    divisors = {a: {d for d in range(1, a + 1) if a % d == 0}
                for a in range(1, n + 1)}
    pairs = [(a, b) for a in range(1, n + 1) for b in range(1, n + 1)]
    failures = sum((b % a == 0) != (divisors[a] <= divisors[b]) for a, b in pairs)
    return len(pairs), failures


def main():
    print("Natural transformations Hom(A, −) => F, found by brute force")
    print(f"  {'example':<31}{'candidates':>11}{'natural':>9}{'|F(A)|':>8}"
          f"  bijection")
    for name, cat, a, obj, arr in examples():
        n_nat, size, cands, bij = yoneda_check(cat, a, obj, arr)
        print(f"  {name:<31}{cands:>11}{n_nat:>9}{size:>8}  {bij}")
    print()
    count, exact = cayley_check()
    print("One object: permutations of S3 commuting with right multiplication")
    print(f"  {count} of 720; exactly the left multiplications x -> gx: {exact}")
    pairs, failures = divisibility_check(60)
    print("Posets: a | b  <=>  every divisor of a divides b, for a, b <= 60")
    print(f"  {pairs} pairs checked, {failures} failures")
    print()
    print("Epistemic status: exhaustive and exact in these finite examples. "
          "They\nillustrate the Yoneda lemma; the proof for every locally "
          "small category\nis in the lesson, and is machine-checked in Lean.")


if __name__ == "__main__":
    main()
