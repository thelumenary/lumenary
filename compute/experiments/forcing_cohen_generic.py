"""Building a Cohen generic real against a list of "ground model" reals.

In Cohen forcing a condition is a finite binary string, and a stronger
condition extends it. A dense set is a requirement that every condition can
be extended to meet: "decide bit n", or "disagree with the real x somewhere".
A filter meeting countably many dense sets is built step by step (the
Rasiowa-Sikorski lemma): extend the current condition into the next dense
set, forever.

Here the "ground model" is a finite stand-in: a list of reals given by rules
(some famous sequences, and every eventually periodic sequence with short
preperiod and period). We meet the dense sets "avoid x" for each listed real
and "decide bit n" for n < 32, interleaved, and check that the resulting
condition disagrees with every listed real - the generic real is new. Then
we check the other half of the story: the filter of initial segments of any
real g misses the dense set "disagree with g", so no filter meets every dense
set.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from itertools import product
from math import isqrt
import textwrap

EXPERIMENT = {
    "id": "forcing_cohen_generic",
    "title": "A Cohen generic real escapes a list of ground-model reals",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["forcing"],
    "summary": (
        "Builds a descending sequence of Cohen conditions (finite binary strings) "
        "meeting the dense sets 'decide bit n' and 'disagree with x' for a list of "
        "reals x standing in for a countable ground model, and checks exactly that "
        "the result differs from every listed real; then checks that the filter of "
        "initial segments of a real misses a dense set. Finite stand-in only."
    ),
    "packages": [],
}


def _prime(n):
    """Trial-division primality test."""
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def _eventually_periodic(pre, cycle):
    """The real pre + cycle + cycle + ... as a rule."""
    return lambda n: pre[n] if n < len(pre) else cycle[(n - len(pre)) % len(cycle)]


def ground_reals():
    """A list of (name, rule) pairs standing in for the reals of a model M."""
    reals = [
        ("primes", lambda n: int(_prime(n))),
        ("squares", lambda n: int(isqrt(n) ** 2 == n)),
        ("Thue-Morse", lambda n: bin(n).count("1") % 2),
        ("sqrt 2 digits", lambda n: isqrt(2 << (2 * (n + 1))) & 1),
    ]
    for pre_len in range(3):
        for cycle_len in range(1, 4):
            for bits in product((0, 1), repeat=pre_len + cycle_len):
                pre, cycle = bits[:pre_len], bits[pre_len:]
                name = "".join(map(str, pre)) + "(" + "".join(map(str, cycle)) + ")"
                reals.append((name, _eventually_periodic(pre, cycle)))
    return reals


def meet_decide(p, n):
    """Extend p (if needed) so that it decides bit n, padding with zeros."""
    return p + (0,) * max(0, n + 1 - len(p))


def disagreement(p, x):
    """A position where condition p disagrees with the real x, or None."""
    return next((i for i, b in enumerate(p) if b != x(i)), None)


def meet_avoid(p, x):
    """Extend p (if needed) so that it disagrees with x somewhere."""
    if disagreement(p, x) is not None:
        return p
    return p + (1 - x(len(p)),)


def build_generic(reals, bits):
    """Meet 'avoid x_k' and 'decide n' alternately; return the final condition
    and the list of conditions p_0 <= p_1 <= ... that were built."""
    p, chain = (), [()]
    for step in range(max(len(reals), bits)):
        if step < len(reals):
            p = meet_avoid(p, reals[step][1])
            chain.append(p)
        if step < bits:
            p = meet_decide(p, step)
            chain.append(p)
    return p, chain


def is_chain(conditions):
    """Is each condition an initial segment of the next (a descending chain)?"""
    return all(q[:len(p)] == p for p, q in zip(conditions, conditions[1:]))


def main():
    reals = ground_reals()
    g, chain = build_generic(reals, 32)
    print(f"Ground reals listed: {len(reals)} rules (some repeat a real)")
    print(f"Dense sets met: {len(reals)} of the form 'avoid x', 32 'decide bit n'")
    print(f"Conditions built: {len(chain)}, each extending the last: {is_chain(chain)}")
    print(f"Generic condition, {len(g)} bits:")
    text = "".join(map(str, g))
    for start in range(0, len(text), 64):
        print("   " + text[start:start + 64])
    positions = [disagreement(g, x) for _, x in reals]
    print(f"Disagrees with every listed real: {all(i is not None for i in positions)}")
    for name, x in reals[:6]:
        print(f"   {name:<14} first disagreement at bit {disagreement(g, x)}")
    print(f"   ... and {len(reals) - 6} eventually periodic reals")
    print()
    real_g = _eventually_periodic(g, (0,))
    misses = all(disagreement(g[:k], real_g) is None for k in range(len(g) + 1))
    print("The filter of initial segments of g (padded with zeros) contains no")
    print(f"condition disagreeing with g: {misses} - it misses that dense set.")
    print()
    print(textwrap.fill(
        "Epistemic status: exact computation for a finite list of reals and "
        "finitely many dense sets. It illustrates the Rasiowa-Sikorski "
        "construction and why a generic real is new; the real theorem - that "
        "for a countable transitive model M a generic G exists, G is not in M, "
        "and M[G] satisfies ZFC - is proved in the lesson, not here.",
        width=78,
    ))


if __name__ == "__main__":
    main()
