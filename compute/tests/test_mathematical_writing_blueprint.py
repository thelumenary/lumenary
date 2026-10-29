import mathematical_writing_blueprint as mb


def test_forward_reference_found():
    assert mb.forward_references(mb.DRAFT) == [("Thm 3", "Lem 2")]


def test_topological_order_respects_dependencies():
    order = mb.topological_order(mb.DRAFT)
    position = {label: i for i, label in enumerate(order)}
    assert sorted(order) == sorted(label for label, *_ in mb.DRAFT)
    for label, _, _, uses in mb.DRAFT:
        assert all(position[d] < position[label] for d in uses)
    assert mb.forward_references([i for o in order for i in mb.DRAFT if i[0] == o]) == []


def test_conditional_results_are_detected():
    marks = mb.standing(mb.DRAFT)
    assert marks["Cor 6"] == "unconditional"
    assert marks["Prop 7"] == "conditional on Conj 5"
    assert marks["Cor 8"] == "conditional on Conj 5"
    assert marks["Conj 5"].startswith("conjecture")


def test_cycles():
    assert mb.find_cycle(mb.DRAFT) is None
    looped = [("A", "lemma", "proved", ["B"]), ("B", "lemma", "proved", ["C"]),
              ("C", "lemma", "proved", ["A"])]
    assert mb.topological_order(looped) is None
    cycle = mb.find_cycle(looped)
    assert cycle[0] == cycle[-1] and set(cycle) == {"A", "B", "C"}


def test_two_conjectures_propagate():
    items = [("C1", "conjecture", "conjectured", []),
             ("C2", "conjecture", "conjectured", []),
             ("T", "theorem", "proved", ["C1", "C2"])]
    assert mb.standing(items)["T"] == "conditional on C1, C2"
