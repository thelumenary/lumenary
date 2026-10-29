"""Theorems can be listed; non-theorems need an argument: the MIU system.

Hofstadter's MIU system (Goedel, Escher, Bach, 1979) is a tiny formal system.
Its only axiom is MI and its rules, for strings x, y over {I, U}, are
    xI -> xIU,   Mx -> Mxx,   xIIIy -> xUy,   xUUy -> xy.
Like the theorems of any recursively axiomatised theory, its theorems can be
listed mechanically: apply every rule to every theorem found so far. Here we
list all theorems reachable through strings of at most 16 symbols.

Is MU a theorem? The search never finds it - but a search can only ever say
"not yet". The answer comes from an argument outside the system: the number
of I's is never divisible by 3 (it starts at 1, and the rules keep it, double
it, or subtract 3). We check this invariant on every theorem found, and check
the known characterisation "Mx is a theorem iff the number of I's in x is not
divisible by 3" on all strings of at most 7 symbols.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from collections import Counter
from itertools import product
import textwrap

EXPERIMENT = {
    "id": "incompleteness_miu_enumeration",
    "title": "Listing the theorems of the MIU system",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["incompleteness"],
    "summary": (
        "Enumerates every theorem of Hofstadter's MIU system reachable through "
        "strings of at most 16 symbols, checks the mod-3 invariant on each, and "
        "confirms the characterisation of theorems for all strings of at most 7 "
        "symbols. Shows that theorems are computably enumerable while MU's "
        "non-derivability needs a proof (the invariant), not a longer search."
    ),
    "packages": [],
}

AXIOM = "MI"


def successors(s):
    """All strings obtained from s by one application of one rule."""
    out = set()
    if s.endswith("I"):
        out.add(s + "U")
    out.add("M" + s[1:] * 2)
    for i in range(1, len(s) - 2):
        if s[i:i + 3] == "III":
            out.add(s[:i] + "U" + s[i + 3:])
    for i in range(1, len(s) - 1):
        if s[i:i + 2] == "UU":
            out.add(s[:i] + s[i + 2:])
    return out


def theorems(max_len):
    """Theorems derivable with every intermediate string of length <= max_len."""
    seen = {AXIOM}
    frontier = [AXIOM]
    while frontier:
        new = []
        for s in frontier:
            for t in sorted(successors(s)):
                if len(t) <= max_len and t not in seen:
                    seen.add(t)
                    new.append(t)
        frontier = new
    return seen


def invariant(s):
    """Number of I's modulo 3; it is never 0 for a theorem."""
    return s.count("I") % 3


def characterisation_failures(found, max_len):
    """Strings Mx of length <= max_len where "#I not divisible by 3" and
    "found as a theorem" disagree."""
    bad = []
    for n in range(max_len):
        for tail in product("IU", repeat=n):
            s = "M" + "".join(tail)
            if (invariant(s) != 0) != (s in found):
                bad.append(s)
    return bad


def main():
    found = theorems(16)
    by_length = Counter(len(s) for s in found)
    print("Theorems of MIU reachable through strings of <= 16 symbols")
    print(f"   total found: {len(found)}")
    print("   by length:  " + " ".join(f"{k}:{by_length[k]}" for k in range(2, 12)))
    print("   shortest:   " + ", ".join(sorted(found, key=lambda s: (len(s), s))[:6]))
    print()
    counts = Counter(invariant(s) for s in found)
    print(f"Invariant (#I mod 3) over all theorems found: {dict(sorted(counts.items()))}")
    print(f"MU found: {'MU' in found}   (#I in MU mod 3 = {invariant('MU')})")
    bad = characterisation_failures(found, 7)
    print(f"Strings of <= 7 symbols where '#I mod 3 != 0' and 'theorem' disagree: "
          f"{len(bad)}")
    print()
    print(textwrap.fill(
        "Epistemic status: exhaustive within the stated bound. The search lists "
        "theorems (it is a semi-decision procedure), but its failure to find MU "
        "proves nothing; the invariant argument proves that MU is not a theorem. "
        "The agreement for strings of at most 7 symbols is a finite check of a "
        "characterisation that is proved in general by a separate argument.",
        width=78,
    ))


if __name__ == "__main__":
    main()
