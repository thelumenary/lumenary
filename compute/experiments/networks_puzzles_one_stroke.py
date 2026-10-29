"""Which figures can be traced in one stroke? Search every route, then compare.

For each small figure (a network of dots and lines) the program counts the
line ends at every dot (the degree), and then searches *every* possible route
that uses each line exactly once, starting from every dot. The search is
exhaustive, so for these figures its answer is certain. We then compare the
search with Euler's rule: a connected figure can be traced in one stroke
exactly when it has 0 or 2 dots of odd degree.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap

EXPERIMENT = {
    "id": "networks_puzzles_one_stroke",
    "title": "One-stroke figures: exhaustive search versus Euler's rule",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["networks-puzzles"],
    "summary": (
        "Counts the degree of every dot in seven small figures, including the "
        "house puzzle and the seven bridges of Konigsberg, and searches every "
        "route that uses each line once. The search settles each figure for "
        "certain and agrees with Euler's odd-dot rule on all seven; it does "
        "not prove the rule for figures it has not tried."
    ),
    "packages": [],
}

#: Each figure is a list of lines; a line joins two dots (letters).
FIGURES = {
    "square": ["AB", "BC", "CD", "DA"],
    "square + diagonal": ["AB", "BC", "CD", "DA", "AC"],
    "envelope (2 diagonals)": ["AB", "BC", "CD", "DA", "AC", "BD"],
    "house": ["AB", "BC", "CD", "DA", "AC", "BD", "DE", "EC"],
    "bow tie": ["AB", "BC", "CA", "CD", "DE", "EC"],
    "two triangles apart": ["AB", "BC", "CA", "DE", "EF", "FD"],
    "Konigsberg bridges": ["IN", "IN", "IS", "IS", "IE", "NE", "SE"],
}


def dots(lines):
    """Return the sorted list of dots that appear on some line."""
    return sorted({d for line in lines for d in line})


def degrees(lines):
    """Return {dot: number of line ends at that dot}."""
    deg = {d: 0 for d in dots(lines)}
    for a, b in lines:
        deg[a] += 1
        deg[b] += 1
    return deg


def odd_dots(lines):
    """Return the sorted list of dots of odd degree."""
    return [d for d, k in degrees(lines).items() if k % 2 == 1]


def is_connected(lines):
    """True if every dot can be reached from every other dot along lines."""
    all_dots = dots(lines)
    if not all_dots:
        return True
    seen, todo = {all_dots[0]}, [all_dots[0]]
    while todo:
        here = todo.pop()
        for a, b in lines:
            for x, y in ((a, b), (b, a)):
                if x == here and y not in seen:
                    seen.add(y)
                    todo.append(y)
    return len(seen) == len(all_dots)


def find_one_stroke(lines):
    """Search every route that uses each line once; return one or None.

    A route is returned as a string of dots, e.g. "ABCA". Every starting dot
    and every order of lines is tried (depth-first search with backtracking).
    """
    used = [False] * len(lines)

    def extend(route):
        if all(used):
            return route
        here = route[-1]
        for i, (a, b) in enumerate(lines):
            if used[i] or here not in (a, b):
                continue
            used[i] = True
            found = extend(route + (b if here == a else a))
            used[i] = False
            if found:
                return found
        return None

    for start in dots(lines):
        found = extend(start)
        if found:
            return found
    return None


def euler_rule_says_yes(lines):
    """Euler's rule: connected, with 0 or 2 dots of odd degree."""
    return is_connected(lines) and len(odd_dots(lines)) in (0, 2)


def main():
    print("Figure                  degrees          odd  rule  search finds")
    agree = 0
    for name, lines in FIGURES.items():
        deg = degrees(lines)
        shown = " ".join(str(deg[d]) for d in dots(lines))
        rule = euler_rule_says_yes(lines)
        route = find_one_stroke(lines)
        agree += rule == (route is not None)
        answer = route if route else "no route"
        print(f"{name:<23} {shown:<16} {len(odd_dots(lines)):>3}  "
              f"{'yes' if rule else 'no':<4}  {answer}")
    print("(Degrees are listed in alphabetical order of the dots.)")
    print()
    print(f"The rule and the search agree on {agree} of {len(FIGURES)} figures.")
    print("Each route starts and ends at the odd dots, when there are two.")
    print("'Two triangles apart' has no odd dots but is not connected,")
    print("so the rule needs the word 'connected'.")
    print()
    print(textwrap.fill(
        "Epistemic status: for each of these seven figures the search tried "
        "every route, so its yes or no is certain (exhaustive-finite). The "
        "agreement with Euler's rule is evidence for the rule, not a proof: "
        "the lesson explains why odd dots must be the ends of a route, and "
        "the Lean module proves that half of the rule for every figure.",
        width=78,
    ))


if __name__ == "__main__":
    main()
