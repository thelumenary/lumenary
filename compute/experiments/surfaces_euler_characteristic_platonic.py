"""The five Platonic solids from coordinates: counting V, E, F and angle defects.

Part 1 lists the solutions of the inequality (p - 2)(q - 2) < 4 with p, q >= 3,
which Euler's formula forces on a polyhedron with p-gonal faces and q faces at
each vertex, and computes V, E, F from E = 2pq / (2p + 2q - pq). Part 2 starts
from explicit vertex coordinates of the five solids, finds the edges as the
pairs of vertices at minimal distance, finds the faces as the shortest cycles
of the edge graph, and checks V - E + F = 2. It also adds up Descartes's angle
defects (2 pi minus the face angles at each vertex) and finds 4 pi = 2 pi chi;
for a square picture frame, a torus, the defects cancel to 0. Exact counting
on explicit polyhedra, with floating point only in distances and angles.
"""

import itertools
import math

EXPERIMENT = {
    "id": "surfaces_euler_characteristic_platonic",
    "title": "The Platonic solids: Euler's formula and Descartes's 4 pi",
    "evidence": ["exact", "exhaustive-finite", "numerical"],
    "lessons": ["surfaces-euler-characteristic"],
    "summary": (
        "Finds all (p, q) with (p - 2)(q - 2) < 4, then builds the five Platonic "
        "solids from coordinates, recovers edges (closest pairs) and faces "
        "(shortest cycles), checks V - E + F = 2 and adds up the angle defects, "
        "getting 4 pi each time: Euler's formula and Descartes's theorem, the "
        "discrete Gauss-Bonnet theorem; a picture-frame torus gives 0 = 2 pi chi."
    ),
    "packages": [],
}

PHI = (1 + math.sqrt(5)) / 2


def schlafli_solutions(limit=20):
    """All (p, q, V, E, F) with 3 <= p, q <= limit and (p-2)(q-2) < 4."""
    out = []
    for p, q in itertools.product(range(3, limit + 1), repeat=2):
        d = 2 * p + 2 * q - p * q
        if d > 0:
            e = 2 * p * q // d
            out.append((p, q, 2 * e // q, e, 2 * e // p))
    return out


def cyclic(points):
    """Close a list of points under cyclic permutation of coordinates."""
    out = set()
    for x, y, z in points:
        out |= {(x, y, z), (y, z, x), (z, x, y)}
    return sorted(out)


def signs(*coords):
    """All sign combinations of the non-zero coordinates."""
    choices = [(c, -c) if c else (0.0,) for c in coords]
    return list(itertools.product(*choices))


SOLIDS = {
    "tetrahedron": [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)],
    "cube": signs(1, 1, 1),
    "octahedron": cyclic(signs(1, 0, 0)),
    "dodecahedron": signs(1, 1, 1) + cyclic(signs(0, 1 / PHI, PHI)),
    "icosahedron": cyclic(signs(0, 1, PHI)),
}


def edges(points):
    """Pairs of vertices at the minimal distance."""
    pairs = list(itertools.combinations(range(len(points)), 2))
    d = {pr: math.dist(points[pr[0]], points[pr[1]]) for pr in pairs}
    m = min(d.values())
    return [pr for pr in pairs if abs(d[pr] - m) < 1e-9]


def cycles(n, edge_list, k):
    """All k-cycles (as vertex tuples), each listed once."""
    adj = {v: set() for v in range(n)}
    for a, b in edge_list:
        adj[a].add(b)
        adj[b].add(a)
    found = []

    def extend(path):
        if len(path) == k:
            if path[0] in adj[path[-1]] and path[1] < path[-1]:
                found.append(tuple(path))
            return
        for w in sorted(adj[path[-1]]):
            if w > path[0] and w not in path:
                extend(path + [w])

    for start in range(n):
        extend([start])
    return found


def faces(n, edge_list):
    """The shortest cycles of the edge graph (the faces of a Platonic solid)."""
    for k in range(3, 7):
        found = cycles(n, edge_list, k)
        if found:
            return found
    return []


def angle(a, o, b):
    """The angle at o between the segments oa and ob."""
    u = [x - y for x, y in zip(a, o)]
    v = [x - y for x, y in zip(b, o)]
    c = sum(x * y for x, y in zip(u, v)) / (math.hypot(*u) * math.hypot(*v))
    return math.acos(max(-1.0, min(1.0, c)))


def total_defect(points, face_list):
    """Sum over vertices of 2 pi minus the face angles there."""
    angle_sum = [0.0] * len(points)
    for face in face_list:
        k = len(face)
        for i in range(k):
            a, o, b = face[i - 1], face[i], face[(i + 1) % k]
            angle_sum[o] += angle(points[a], points[o], points[b])
    return sum(2 * math.pi - s for s in angle_sum)


def picture_frame():
    """A square picture frame (a torus): its 16 vertices and 16 quad faces."""
    ring = [(3, 3), (-3, 3), (-3, -3), (3, -3), (1, 1), (-1, 1), (-1, -1),
            (1, -1)]
    points = [(x, y, z) for z in (1, -1) for x, y in ring]
    fs = []
    for k in range(4):
        o, o1, i, i1 = k, (k + 1) % 4, 4 + k, 4 + (k + 1) % 4
        fs += [(o, o1, i1, i), (o + 8, o1 + 8, i1 + 8, i + 8),
               (o, o1, o1 + 8, o + 8), (i, i1, i1 + 8, i + 8)]
    return points, fs


def edges_of_faces(face_list):
    """The distinct edges of a list of polygonal faces."""
    return {tuple(sorted((f[i - 1], f[i]))) for f in face_list
            for i in range(len(f))}


def main():
    print("Solutions of (p - 2)(q - 2) < 4 with 3 <= p, q <= 20:")
    for p, q, v, e, f in schlafli_solutions():
        print(f"  {{{p},{q}}}: V = {v:>2}, E = {e:>2}, F = {f:>2}")
    print()
    print("From coordinates (edges = closest pairs, faces = shortest cycles):")
    print(f"  {'solid':<13}{'V':>3}{'E':>4}{'F':>4}{'p':>3}{'q':>3}"
          f"{'V-E+F':>7}{'defect/pi':>11}")
    for solid, pts in SOLIDS.items():
        es = edges(pts)
        v, e = len(pts), len(es)
        fs = faces(v, es)
        f, p, q = len(fs), len(fs[0]), 2 * e // v
        d = total_defect(pts, fs) / math.pi
        print(f"  {solid:<13}{v:>3}{e:>4}{f:>4}{p:>3}{q:>3}{v - e + f:>7}"
              f"{d:>11.6f}")
    pts, fs = picture_frame()
    v, e, f = len(pts), len(edges_of_faces(fs)), len(fs)
    d = total_defect(pts, fs) / math.pi
    print(f"  {'frame torus':<13}{v:>3}{e:>4}{f:>4}{4:>3}{'-':>3}{v - e + f:>7}"
          f"{round(d, 6) + 0.0:>11.6f}")
    print("  The torus has chi = 0, and its angle defects cancel: +pi/2 at each")
    print("  outer corner, -pi/2 at each inner corner. Total defect = 2 pi chi.")
    print()
    print("Epistemic status: part 1 is an exhaustive search (the bound p, q <= 5")
    print("is proved in the lesson); part 2 counts six explicit polyhedra exactly")
    print("(the frame's faces are listed by hand), with floating-point angles, so")
    print("the defect sums are numerical. Six examples are evidence for Euler's")
    print("and Descartes's theorems, not proofs.")


if __name__ == "__main__":
    main()
