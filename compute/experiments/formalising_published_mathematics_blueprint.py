"""A blueprint as a dependency graph: what is ready, what is circular.

A blueprint lists the definitions and lemmas of a formalisation project and,
for each, the earlier items it uses. That makes it a directed graph, and simple
graph algorithms answer the questions a project coordinator asks every day:
which items are ready to be formalised now (everything they use is done)? In
what order can the whole project be done? What is the longest chain of
dependencies (no amount of parallel work can beat it)? And is the argument
circular somewhere (a cycle in the graph)?

The blueprint here is the one for Zagier's proof in the lesson, frozen at an
imagined moment when only some items are done. Then we break it on purpose,
letting the parity lemma "use" the oddness of |S|, and find the cycle.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap

EXPERIMENT = {
    "id": "formalising_published_mathematics_blueprint",
    "title": "A blueprint as a graph: ready items, critical path, cycles",
    "evidence": ["exact"],
    "lessons": ["formalising-published-mathematics"],
    "summary": (
        "Treats the lesson's blueprint for Zagier's proof as a directed graph and "
        "computes a valid formalisation order (Kahn's algorithm), the items ready to "
        "formalise given those already done, the longest dependency chain, and a "
        "cycle in a deliberately circular variant. Exact graph computations; they "
        "say nothing about whether any lemma is true."
    ),
    "packages": [],
}

#: Blueprint for Zagier's proof: item -> items it uses.
BLUEPRINT = {
    "def:S": [],
    "def:map": [],
    "def:swap": [],
    "lem:facts": ["def:S"],
    "lem:finite": ["def:S", "lem:facts"],
    "lem:cases": ["def:map"],
    "lem:mapsto": ["lem:cases", "lem:finite"],
    "lem:invol": ["def:map", "lem:facts", "lem:finite"],
    "lem:fixed": ["def:map", "lem:facts", "lem:finite"],
    "lem:parity": [],
    "lem:odd": ["lem:mapsto", "lem:invol", "lem:fixed", "lem:parity"],
    "thm:fermat": ["def:swap", "lem:odd", "lem:parity", "lem:finite"],
}

#: Items already formalised at the imagined moment.
DONE = {"def:S", "def:map", "def:swap", "lem:facts", "lem:finite", "lem:cases"}


def topological_order(graph):
    """Kahn's algorithm, smallest name first; None if there is a cycle."""
    remaining = {v: set(us) for v, us in graph.items()}
    order = []
    while remaining:
        ready = sorted(v for v, us in remaining.items() if not us)
        if not ready:
            return None
        v = ready[0]
        order.append(v)
        del remaining[v]
        for us in remaining.values():
            us.discard(v)
    return order


def ready_items(graph, done):
    """Items not yet done all of whose dependencies are done."""
    return sorted(v for v, us in graph.items()
                  if v not in done and all(u in done for u in us))


def longest_chain(graph):
    """A longest dependency chain (a list of items), for an acyclic graph."""
    best = {}
    for v in topological_order(graph):
        chains = [best[u] for u in graph[v]]
        best[v] = max(chains, key=len, default=[]) + [v]
    return max(best.values(), key=len)


def uses_transitively(graph, item):
    """Every item that `item` depends on, directly or indirectly."""
    seen, stack = set(), list(graph[item])
    while stack:
        u = stack.pop()
        if u not in seen:
            seen.add(u)
            stack.extend(graph[u])
    return seen


def find_cycle(graph):
    """Return a dependency cycle [v0, v1, ..., v0], or None."""
    colour = {v: 0 for v in graph}
    path = []

    def visit(v):
        colour[v] = 1
        path.append(v)
        for u in graph[v]:
            if colour[u] == 1:
                return path[path.index(u):] + [u]
            if colour[u] == 0:
                found = visit(u)
                if found:
                    return found
        colour[v] = 2
        path.pop()
        return None

    for v in sorted(graph):
        if colour[v] == 0:
            found = visit(v)
            if found:
                return found
    return None


def wrap(items, indent="   "):
    """Format a list of names in lines of at most 78 characters."""
    return textwrap.fill(", ".join(items), width=78, initial_indent=indent,
                         subsequent_indent=indent)


def main():
    order = topological_order(BLUEPRINT)
    print(f"Blueprint items: {len(BLUEPRINT)}; done so far: {len(DONE)}")
    print("A valid order in which to formalise everything:")
    print(wrap(order))
    print("Ready to formalise now (all dependencies done):")
    print(wrap(ready_items(BLUEPRINT, DONE)))
    chain = longest_chain(BLUEPRINT)
    print(f"Longest dependency chain ({len(chain)} items):")
    print(wrap(chain))
    deps = uses_transitively(BLUEPRINT, "thm:fermat")
    print(f"The theorem rests on {len(deps)} items; every item is used: "
          f"{deps == set(BLUEPRINT) - {'thm:fermat'}}")
    print()
    broken = dict(BLUEPRINT, **{"lem:parity": ["lem:odd"]})
    print("Variant in which the parity lemma 'uses' that |S| is odd:")
    print(f"   topological order exists: {topological_order(broken) is not None}")
    print("   cycle found: " + " -> ".join(find_cycle(broken)))
    print()
    print(textwrap.fill(
        "Epistemic status: exact computations on a small finite graph. They "
        "check the bookkeeping of a blueprint - order, readiness, circularity - "
        "and nothing else: a blueprint can be acyclic and complete while a "
        "lemma in it is false or its formal statement is unfaithful. That is "
        "what the formal proofs, and the people reading the statements, are for.",
        width=78,
    ))


if __name__ == "__main__":
    main()
