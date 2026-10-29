"""Explicit-state model checking of three mutual-exclusion protocols.

Two processes share boolean flags (and, for Peterson's algorithm, a variable
``turn``). Every interleaving of their atomic steps is explored by
breadth-first search, so each reported property is checked on the *whole*
finite state space of the model: this is exhaustive, exact evidence about the
model. Breadth-first search also returns a *shortest* counterexample when a
property fails. The CTL property AG EF crit0 ("from every reachable state,
process 0 can still reach its critical section") is computed as a least fixed
point, Z_{k+1} = crit0 U pre(Z_k), exactly as in the lesson's Lean theorem
``ef_eq_lfp``. What is verified is the model, not real code on real hardware.
"""

from collections import deque

EXPERIMENT = {
    "id": "formal_methods_model_checking",
    "title": "Model checking mutual exclusion: two flawed protocols and Peterson's",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["formal-methods"],
    "summary": (
        "Explores every reachable state of three two-process mutual-exclusion "
        "protocols by breadth-first search. It finds a shortest trace in which a "
        "naive protocol lets both processes into the critical section, a deadlock "
        "in a second protocol, and confirms mutual exclusion, deadlock freedom and "
        "AG EF crit for Peterson's algorithm (EF computed as a least fixed point). "
        "Exhaustive for these finite models only; fairness is not modelled."
    ),
    "packages": [],
}

# A state is (pc0, pc1, flag0, flag1, turn).
INITIAL = (0, 0, False, False, 0)


def _with(state, i, pc=None, flag=None, turn=None):
    """Return a copy of ``state`` with process i's pc/flag (and turn) changed."""
    pcs, flags = [state[0], state[1]], [state[2], state[3]]
    if pc is not None:
        pcs[i] = pc
    if flag is not None:
        flags[i] = flag
    return (pcs[0], pcs[1], flags[0], flags[1],
            state[4] if turn is None else turn)


def step_check_then_set(state, i):
    """Naive protocol: look at the other flag, then raise our own."""
    j, pc = 1 - i, state[i]
    if pc == 0:
        return _with(state, i, pc=1)
    if pc == 1:                       # enter only if the other flag is down
        return None if state[2 + j] else _with(state, i, pc=2)
    if pc == 2:
        return _with(state, i, pc=3, flag=True)
    return _with(state, i, pc=0, flag=False)   # pc 3 = critical: leave


def step_set_then_check(state, i):
    """Raise our flag first, then wait until the other flag is down."""
    j, pc = 1 - i, state[i]
    if pc == 0:
        return _with(state, i, pc=1)
    if pc == 1:
        return _with(state, i, pc=2, flag=True)
    if pc == 2:
        return None if state[2 + j] else _with(state, i, pc=3)
    return _with(state, i, pc=0, flag=False)   # pc 3 = critical: leave


def step_peterson(state, i):
    """Peterson's algorithm: flag[i] := true; turn := j; await; critical."""
    j, pc = 1 - i, state[i]
    if pc == 0:
        return _with(state, i, pc=1)
    if pc == 1:
        return _with(state, i, pc=2, flag=True)
    if pc == 2:
        return _with(state, i, pc=3, turn=j)
    if pc == 3:
        go = (not state[2 + j]) or state[4] == i
        return _with(state, i, pc=4) if go else None
    return _with(state, i, pc=0, flag=False)   # pc 4 = critical: leave


#: name -> (step function, critical pc)
PROTOCOLS = {
    "check-then-set": (step_check_then_set, 3),
    "set-then-check": (step_set_then_check, 3),
    "Peterson": (step_peterson, 4),
}


def successors(step, state):
    """All states reachable in one atomic step of either process."""
    return [t for t in (step(state, 0), step(state, 1)) if t is not None]


def explore(step):
    """Breadth-first search; return (parent map, successor map)."""
    parent, succ = {INITIAL: None}, {}
    queue = deque([INITIAL])
    while queue:
        s = queue.popleft()
        succ[s] = successors(step, s)
        for t in succ[s]:
            if t not in parent:
                parent[t] = s
                queue.append(t)
    return parent, succ


def trace_to(parent, state):
    """The BFS path from the initial state to ``state`` (a shortest path)."""
    path = []
    while state is not None:
        path.append(state)
        state = parent[state]
    return path[::-1]


def ef_fixpoint(succ, goal):
    """Least fixed point of Z -> goal U pre(Z); return (set, sizes of iterates)."""
    z, sizes = set(), []
    while True:
        new = {s for s in succ if s in goal or any(t in z for t in succ[s])}
        sizes.append(len(new))
        if new == z:
            return z, sizes
        z = new


def check(name):
    """Model-check one protocol; return a dict of results."""
    step, crit = PROTOCOLS[name]
    parent, succ = explore(step)
    bad = [s for s in parent if s[0] == crit and s[1] == crit]
    dead = [s for s in parent if not succ[s]]
    goal = {s for s in succ if s[0] == crit}
    ef, sizes = ef_fixpoint(succ, goal)
    return {
        "states": len(parent),
        "mutex": not bad,
        "counterexample": trace_to(parent, min(bad, key=lambda s: len(
            trace_to(parent, s)))) if bad else None,
        "deadlocks": dead,
        "ag_ef_crit0": set(succ) <= ef,
        "ef_sizes": sizes,
    }


def describe(state):
    """Short text for a state."""
    flags = "".join("T" if f else "F" for f in state[2:4])
    return f"pc=({state[0]},{state[1]}) flags={flags} turn={state[4]}"


def main():
    print("Explicit-state model checking, two processes, all interleavings")
    print(f"{'protocol':<16}{'states':>7}  {'mutual excl.':<14}"
          f"{'deadlock-free':<15}AG EF crit0")
    results = {name: check(name) for name in PROTOCOLS}
    for name, r in results.items():
        mutex = "holds" if r["mutex"] else "VIOLATED"
        dead = "yes" if not r["deadlocks"] else "NO"
        ag = "yes" if r["ag_ef_crit0"] else "no"
        print(f"{name:<16}{r['states']:>7}  {mutex:<14}{dead:<15}{ag}")
    print()
    print("Shortest counterexample to mutual exclusion (check-then-set):")
    for k, s in enumerate(results["check-then-set"]["counterexample"]):
        print(f"  {k}: {describe(s)}")
    print("Both processes are now at pc 3, the critical section.")
    print()
    print("Deadlocked states of set-then-check (no process can move):")
    for s in results["set-then-check"]["deadlocks"]:
        print(f"  {describe(s)}")
    sizes = results["Peterson"]["ef_sizes"]
    print("Peterson: sizes of the iterates of Z -> crit0 U pre(Z) from the empty")
    print("set: " + ", ".join(map(str, sizes)) + " (stable = the least fixed point)")
    print()
    print("Epistemic status: exhaustive and exact for these finite models - every")
    print("reachable state was examined, and the counterexample and deadlock are")
    print("concrete runs. It says nothing about real code, compilers or weak")
    print("memory hardware, and starvation freedom needs fairness assumptions")
    print("that are not modelled; Peterson's correctness in general is a theorem.")


if __name__ == "__main__":
    main()
