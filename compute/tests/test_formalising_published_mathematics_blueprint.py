import formalising_published_mathematics_blueprint as b


def is_valid_order(graph, order):
    position = {v: i for i, v in enumerate(order)}
    return sorted(order) == sorted(graph) and all(
        position[u] < position[v] for v, us in graph.items() for u in us)


def test_topological_order_respects_dependencies():
    order = b.topological_order(b.BLUEPRINT)
    assert is_valid_order(b.BLUEPRINT, order)
    assert order[-1] == "thm:fermat"


def test_ready_items():
    assert b.ready_items(b.BLUEPRINT, b.DONE) == [
        "lem:fixed", "lem:invol", "lem:mapsto", "lem:parity"]
    assert b.ready_items(b.BLUEPRINT, set()) == [
        "def:S", "def:map", "def:swap", "lem:parity"]
    assert b.ready_items(b.BLUEPRINT, set(b.BLUEPRINT)) == []


def test_longest_chain_is_a_chain_of_maximal_length():
    chain = b.longest_chain(b.BLUEPRINT)
    assert all(u in b.BLUEPRINT[v] for u, v in zip(chain, chain[1:]))
    assert len(chain) == 6 and chain[-1] == "thm:fermat"
    tiny = {"a": [], "b": ["a"], "c": ["b"], "d": ["a"]}
    assert b.longest_chain(tiny) == ["a", "b", "c"]


def test_transitive_uses():
    assert b.uses_transitively(b.BLUEPRINT, "lem:finite") == {"def:S", "lem:facts"}
    assert b.uses_transitively(b.BLUEPRINT, "thm:fermat") == set(b.BLUEPRINT) - {"thm:fermat"}


def test_cycles_are_detected():
    assert b.find_cycle(b.BLUEPRINT) is None
    broken = dict(b.BLUEPRINT, **{"lem:parity": ["lem:odd"]})
    cycle = b.find_cycle(broken)
    assert cycle[0] == cycle[-1]
    assert all(u in broken[v] for v, u in zip(cycle, cycle[1:]))
    assert b.topological_order(broken) is None
    assert b.find_cycle({"x": ["x"]}) == ["x", "x"]
