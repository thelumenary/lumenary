"""Cauchy-Schwarz and the triangle inequality, checked exactly.

For every pair of integer vectors u, v in three dimensions with coordinates
from -2 to 2 we check, in exact integer arithmetic, Lagrange's identity
|u|^2 |v|^2 - (u.v)^2 = |u x v|^2, hence the Cauchy-Schwarz inequality
(u.v)^2 <= |u|^2 |v|^2, and find exactly which pairs give equality. We then
test the triangle inequality and its equality cases, and finally let SymPy
verify Lagrange's identity for symbolic coordinates.
"""

import itertools
import math

import sympy

EXPERIMENT = {
    "id": "vectors_cauchy_schwarz",
    "title": "Cauchy-Schwarz and the triangle inequality, checked exactly",
    "evidence": ["exact", "exhaustive-finite", "symbolic"],
    "lessons": ["vectors"],
    "summary": (
        "Checks Lagrange's identity, the Cauchy-Schwarz inequality and the "
        "triangle inequality on all 15,625 pairs of integer vectors in 3D with "
        "coordinates from -2 to 2, using exact integers, and classifies the "
        "equality cases; then SymPy verifies Lagrange's identity symbolically. "
        "Exhaustive for this finite grid only; the lesson proves the general case."
    ),
    "packages": ["sympy"],
}


def dot(u, v):
    """The dot product u . v."""
    return sum(a * b for a, b in zip(u, v))


def cross(u, v):
    """The cross product u x v of two 3D vectors."""
    return (u[1] * v[2] - u[2] * v[1],
            u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0])


def is_parallel(u, v):
    """True when u and v are parallel (including when one is zero)."""
    return cross(u, v) == (0, 0, 0)


def same_direction(u, v):
    """True when one vector is a non-negative multiple of the other."""
    return is_parallel(u, v) and dot(u, v) >= 0


def triangle_holds(u, v):
    """Exact test of |u + v| <= |u| + |v|, with no square roots.

    |u+v| <= |u| + |v|  iff  |u+v|^2 <= |u|^2 + |v|^2 + 2|u||v|
    iff  u.v <= |u||v|, which (for u.v >= 0) is (u.v)^2 <= |u|^2 |v|^2.
    Returns (holds, equality).
    """
    uv, uu, vv = dot(u, v), dot(u, u), dot(v, v)
    holds = uv <= 0 or uv * uv <= uu * vv
    equality = uv >= 0 and uv * uv == uu * vv
    return holds, equality


def main():
    grid = list(itertools.product(range(-2, 3), repeat=3))
    pairs = cs_fail = lagrange_fail = 0
    cs_equal = parallel = tri_fail = tri_equal = same_dir = 0
    for u in grid:
        for v in grid:
            pairs += 1
            uv, uu, vv = dot(u, v), dot(u, u), dot(v, v)
            lagrange_fail += uu * vv - uv * uv != dot(cross(u, v), cross(u, v))
            cs_fail += uv * uv > uu * vv
            cs_equal += uv * uv == uu * vv
            parallel += is_parallel(u, v)
            holds, equality = triangle_holds(u, v)
            tri_fail += not holds
            tri_equal += equality
            same_dir += same_direction(u, v)
    print(f"All pairs of vectors in {{-2,...,2}}^3: {pairs} pairs (exact integers)")
    print(f"  Lagrange identity |u|^2|v|^2 - (u.v)^2 = |u x v|^2 fails: "
          f"{lagrange_fail}")
    print(f"  Cauchy-Schwarz (u.v)^2 <= |u|^2 |v|^2 fails: {cs_fail}")
    print(f"  equality (u.v)^2 = |u|^2|v|^2: {cs_equal} pairs; "
          f"parallel pairs: {parallel}")
    print(f"  triangle inequality fails: {tri_fail}")
    print(f"  equality |u+v| = |u|+|v|: {tri_equal} pairs; "
          f"same-direction pairs: {same_dir}")
    u, v = (1, 2, 2), (2, -1, 2)
    print(f"Example: u = {u}, v = {v}: u.v = {dot(u, v)}, |u| = 3, |v| = 3,")
    angle = math.degrees(math.acos(dot(u, v) / 9))
    print(f"  angle = arccos(4/9) = {angle:.2f} degrees")
    s = sympy.symbols("u1:4 v1:4")
    us, vs = s[:3], s[3:]
    gap = sympy.expand(dot(us, us) * dot(vs, vs) - dot(us, vs) ** 2
                       - dot(cross(us, vs), cross(us, vs)))
    print(f"SymPy: |u|^2|v|^2 - (u.v)^2 - |u x v|^2 expands to {gap}")
    print()
    print("Epistemic status: the grid check is exact and exhaustive, but only")
    print("for these 15,625 integer pairs. SymPy's expansion to 0 is a symbolic")
    print("verification of Lagrange's identity for all real coordinates (as")
    print("far as SymPy is trusted); the lesson's proof needs no computer.")


if __name__ == "__main__":
    main()
