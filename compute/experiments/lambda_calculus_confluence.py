"""Testing the Church-Rosser theorem on every small λ-term.

We enumerate every λ-term (de Bruijn indices, at most one free variable) up
to a given size, build its complete β-reduction graph (all redexes, all
orders) when that graph is small, and check two consequences of confluence:
every two reducts of a term have a common reduct, and no term reaches two
different normal forms. We also count terms that have a normal form but also
an infinite reduction (weakly but not strongly normalising, like K I Omega),
and compare the shortest and longest routes to a normal form. This is
exhaustive evidence for finitely many terms; the theorem is proved in the
lesson and in Lean.
"""

from collections import deque

EXPERIMENT = {
    "id": "lambda_calculus_confluence",
    "title": "Church–Rosser on every small λ-term: an exhaustive check",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["lambda-calculus"],
    "summary": (
        "Enumerates all 38,438 λ-terms with at most one free variable up to "
        "size 10, "
        "builds each term's full β-reduction graph (all redexes, all orders; "
        "graphs over 200 terms are set aside) and checks that any two reducts "
        "have a common reduct and that no term reaches two normal forms. Also "
        "counts terms that normalise yet have infinite reductions. Exhaustive "
        "for these finitely many terms only; the theorem is proved in Lean."
    ),
    "packages": [],
}

# Terms: ("var", i), ("app", s, t), ("lam", t).


def terms_of_size(size, depth, free=1, _memo=None):
    """All terms of exactly ``size`` nodes whose indices are < depth + free."""
    memo = {} if _memo is None else _memo
    key = (size, depth)
    if key in memo:
        return memo[key]
    out = []
    if size == 1:
        out = [("var", i) for i in range(depth + free)]
    elif size >= 2:
        out += [("lam", t) for t in terms_of_size(size - 1, depth + 1, free, memo)]
        for left in range(1, size - 1):
            for s in terms_of_size(left, depth, free, memo):
                for t in terms_of_size(size - 1 - left, depth, free, memo):
                    out.append(("app", s, t))
    memo[key] = out
    return out


def shift(t, d, cutoff=0):
    """Add ``d`` to every free index (those >= ``cutoff``)."""
    if t[0] == "var":
        return ("var", t[1] + d) if t[1] >= cutoff else t
    if t[0] == "app":
        return ("app", shift(t[1], d, cutoff), shift(t[2], d, cutoff))
    return ("lam", shift(t[1], d, cutoff + 1))


def subst(t, j, s):
    """Capture-avoiding substitution t[s/j]."""
    if t[0] == "var":
        return s if t[1] == j else t
    if t[0] == "app":
        return ("app", subst(t[1], j, s), subst(t[2], j, s))
    return ("lam", subst(t[1], j + 1, shift(s, 1)))


def reducts(t, _memo={}):
    """The set of all one-step β-reducts of ``t`` (every redex position)."""
    if t in _memo:
        return _memo[t]
    out = set()
    if t[0] == "lam":
        out = {("lam", b) for b in reducts(t[1])}
    elif t[0] == "app":
        f, a = t[1], t[2]
        if f[0] == "lam":
            out.add(shift(subst(f[1], 0, shift(a, 1)), -1))
        out |= {("app", f2, a) for f2 in reducts(f)}
        out |= {("app", f, a2) for a2 in reducts(a)}
    _memo[t] = frozenset(out)
    return _memo[t]


def size_of(t):
    """Number of nodes of a term."""
    if t[0] == "var":
        return 1
    if t[0] == "lam":
        return 1 + size_of(t[1])
    return 1 + size_of(t[1]) + size_of(t[2])


def reduction_graph(t, cap=200):
    """All terms reachable from ``t`` with their reducts, or None if more
    than ``cap`` terms are reachable."""
    graph, queue = {}, deque([t])
    while queue:
        u = queue.popleft()
        if u in graph:
            continue
        graph[u] = reducts(u)
        if len(graph) > cap:
            return None
        queue.extend(v for v in graph[u] if v not in graph)
    return graph


def reachable(graph, start):
    """Terms reachable from ``start`` (including itself) in a finite graph."""
    seen, stack = {start}, [start]
    while stack:
        for v in graph[stack.pop()]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return seen


def has_cycle(graph):
    """Whether the finite reduction graph contains a cycle."""
    colour = {}
    for root in graph:
        if root in colour:
            continue
        colour[root] = 1
        stack = [(root, iter(graph[root]))]
        while stack:
            node, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                colour[node] = 2
                stack.pop()
            elif colour.get(nxt) == 1:
                return True
            elif nxt not in colour:
                colour[nxt] = 1
                stack.append((nxt, iter(graph[nxt])))
    return False


def path_lengths(graph, start, target):
    """Shortest and longest path lengths from start to target (acyclic)."""
    best = {}

    def longest(u):
        if u == target:
            return 0
        if u not in best:
            options = [longest(v) for v in graph[u]]
            best[u] = 1 + max(x for x in options if x is not None) \
                if any(x is not None for x in options) else None
        return best[u]

    dist, queue = {start: 0}, deque([start])
    while queue:
        u = queue.popleft()
        for v in graph[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                queue.append(v)
    return dist.get(target), longest(start)


def analyse(t, cap=200):
    """Classify one term: returns a dict of facts about its reduction graph."""
    graph = reduction_graph(t, cap)
    if graph is None:
        return {"explored": False}
    normal = [u for u in graph if not graph[u]]
    reach = {u: reachable(graph, u) for u in graph}
    locally_confluent = all(
        reach[b] & reach[c]
        for u in graph for b in graph[u] for c in graph[u])
    return {"explored": True, "normal_forms": len(normal),
            "joinable": locally_confluent, "cycle": has_cycle(graph),
            "graph_size": len(graph)}


def survey(max_size=8, cap=200):
    """Analyse every term with at most one free variable up to ``max_size``."""
    stats = {"terms": 0, "explored": 0, "with_nf": 0, "two_nf": 0,
             "not_joinable": 0, "wn_not_sn": 0, "no_nf": 0, "largest": 0}
    memo = {}
    for size in range(1, max_size + 1):
        for t in terms_of_size(size, 0, 1, memo):
            stats["terms"] += 1
            facts = analyse(t, cap)
            if not facts["explored"]:
                continue
            stats["explored"] += 1
            stats["largest"] = max(stats["largest"], facts["graph_size"])
            stats["with_nf"] += facts["normal_forms"] >= 1
            stats["no_nf"] += facts["normal_forms"] == 0
            stats["two_nf"] += facts["normal_forms"] >= 2
            stats["not_joinable"] += not facts["joinable"]
            stats["wn_not_sn"] += facts["normal_forms"] >= 1 and facts["cycle"]
    return stats


NAMED = {
    "I": ("lam", ("var", 0)),
    "K": ("lam", ("lam", ("var", 1))),
    "omega": ("lam", ("app", ("var", 0), ("var", 0))),
    "omega3": ("lam", ("app", ("app", ("var", 0), ("var", 0)), ("var", 0))),
}


def examples():
    """Named terms illustrating the possible shapes of reduction graphs."""
    i, k, w, w3 = (NAMED[n] for n in ("I", "K", "omega", "omega3"))
    z = ("var", 0)
    return [
        ("(λx. x x)((λy. y) z)", ("app", w, ("app", i, z))),
        ("K I Omega", ("app", ("app", k, i), ("app", w, w))),
        ("Omega", ("app", w, w)),
        ("(λx. x x x)(λx. x x x)", ("app", w3, w3)),
    ]


def main():
    max_size = 10
    s = survey(max_size)
    print(f"All {s['terms']} λ-terms of size <= {max_size} with at most one"
          " free variable")
    print(f"  reduction graph built (<= 200 terms):        {s['explored']}")
    print(f"  largest graph built:                         {s['largest']}")
    print(f"  with a normal form:                          {s['with_nf']}")
    print(f"  with no normal form:                         {s['no_nf']}")
    print(f"  reaching two different normal forms:         {s['two_nf']}")
    print(f"  with two reducts that cannot be joined:      {s['not_joinable']}")
    print()
    print("Some larger terms:")
    for name, t in examples():
        g = reduction_graph(t, cap=200)
        if g is None:
            print(f"  {name:<24} more than 200 reducts: the graph keeps growing")
            continue
        nfs = [u for u in g if not g[u]]
        terms = f"{len(g)} term" + ("s" if len(g) != 1 else "")
        count = {0: "no normal form", 1: "one normal form"}.get(
            len(nfs), f"{len(nfs)} normal forms")
        line = f"  {name:<24} {terms}, {count}"
        if nfs and has_cycle(g):
            line += ", also an infinite reduction"
        elif nfs:
            short, long_ = path_lengths(g, t, nfs[0])
            line += f", routes of {short} to {long_} steps"
        else:
            line += ", every reduction is infinite"
        print(line)
    print()
    print("Epistemic status: an exhaustive check of finitely many terms (and "
          "only\nof those whose reduction graphs are small). It is evidence "
          "for the\nChurch-Rosser theorem, not a proof: the proof, by "
          "parallel reduction,\nis in the lesson and is machine-checked in "
          "Lean.")


if __name__ == "__main__":
    main()
