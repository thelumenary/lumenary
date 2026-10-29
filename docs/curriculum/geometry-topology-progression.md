# Geometry and topology progression

<!-- Topic ids below come from content/math/graph/graph.json (tag `geometry-topology-progression`). Update this document whenever the graph changes. -->

Set theory and category theory are the two foundational languages of Lumenary Math (see `set-theory-progression.md` and `category-theory-progression.md`). They are not the only ways of seeing. **Geometry** — distance, angle, shape, curvature, symmetry — and **topology** — what survives continuous deformation — run through the whole curriculum as a third great thread, from sorting shapes in kindergarten to 3-manifolds and symplectic topology in the research pathways. This document traces that thread. Topics on it carry the graph tag `geometry-topology-progression`, and the specialisation pathway `geometry-topology` (in `pathways.json`) walks it from Euclid to low-dimensional topology.

## Principles

- **The picture is part of the mathematics.** Every geometry and topology lesson has a picture — a widget, an SVG figure or a diagram — and the higher lessons explain how to *see* the proofs, not only how to write them.
- **Geometry and topology are viewpoints on everything, not just subjects.** From early undergraduate onwards every lesson has a `viewpoints` section (see `viewpoints.md`); the topologist's and geometer's views appear there whenever they are meaningful — in algebra (groups as symmetries, Galois theory and covering spaces), analysis (spaces of functions, curvature of graphs), logic (Stone duality, topological semantics) and category theory (sheaves, the functor of points, homotopy theory as the origin of categories).
- **Intuition first, rigour always.** Children meet shapes, symmetry and "stretchy" equivalence through play; secondary learners prove theorems of Euclidean geometry; undergraduates make topology precise with metric and topological spaces before using the big invariants. Informal arguments (such as the classification of surfaces by cutting and gluing) are labelled as such, with references to complete proofs.
- **Honesty at the frontier.** The research topics separate classical results (geometrisation, Mostow rigidity, Gauss–Bonnet–Chern) from open problems (the smooth 4-dimensional Poincaré conjecture, the Hodge conjecture, the homotopy groups of spheres).

## Stage by stage

### Kindergarten to Grade 5

- **Shapes** (`math.geom.shapes`, K–2): sorting and naming shapes; corners, edges and faces of solids (the seed of Euler's formula).
- **Measuring length and time** (`math.geom.measurement`, K–2).
- **Area, perimeter and angles** (`math.geom.area-angles`, 3–5).
- **Symmetry: slides, turns and flips** (`math.geom.symmetry-transformations`, 3–5): transformations that preserve shape, and doing/undoing them — a precursor of groups acting on spaces.
- **Dots and lines: networks and puzzles** (`math.discrete.networks-puzzles`, 3–5): Euler's Königsberg problem, the first theorem of topology and graph theory.

### Grades 6–8

- **The coordinate plane** (`math.geom.coordinate-plane`), **The Pythagorean theorem** (`math.geom.pythagorean-theorem`), **Rigid motions, congruence and similarity** (`math.geom.rigid-motions-similarity`).

### Grades 9–12

- **Euclidean geometry and proof** (`math.geom.euclidean-geometry`), **Trigonometry** (`math.geom.trigonometry`).
- **Vectors and coordinate geometry** (`math.geom.vectors`): the bridge from synthetic to analytic geometry and to linear algebra.
- **Conic sections** (`math.geom.conic-sections`): the classical curves, preparing projective geometry.

### Early undergraduate

- **Transformation geometry and the Erlangen programme** (`math.geom.transformation-geometry`): a geometry is a space with a group of transformations.
- **Surfaces, polyhedra and the Euler characteristic** (`math.geom.surfaces-euler-characteristic`): the first course in the topologist's way of seeing — Euler's formula, Platonic solids, gluing polygons, orientability and the classification of surfaces.
- **Non-Euclidean geometry: spherical and hyperbolic** (`math.geom.non-euclidean-geometry`): curvature as the measure of the failure of the parallel postulate; the independence of that postulate.

### Advanced undergraduate

- **Metric spaces and point-set topology** (`math.geom.point-set-topology`): the precise language of continuity, compactness and connectedness.
- **Differential geometry of curves and surfaces** (`math.geom.curves-surfaces`): curvature, the Theorema Egregium, local Gauss–Bonnet.
- **Homotopy and the fundamental group** (`math.geom.fundamental-group`): the first algebraic invariant of spaces.
- **Projective geometry** (`math.geom.projective-geometry`), **Differential forms and Stokes' theorem** (`math.geom.differential-forms`), **Knot theory** (`math.geom.knot-theory`), **Matrix groups and continuous symmetry** (`math.geom.matrix-groups`).

### First-year graduate

- **Smooth manifolds** (`math.geom.smooth-manifolds`), **Algebraic topology** (`math.geom.algebraic-topology`), **Riemannian geometry** (`math.geom.riemannian-geometry`), **Differential topology** (`math.geom.differential-topology`), **Homotopy theory** (`math.geom.homotopy-theory`), **Vector bundles and characteristic classes** (`math.geom.vector-bundles-characteristic-classes`), **Lie groups and Lie algebras** (`math.geom.lie-groups`), **Riemann surfaces** (`math.geom.riemann-surfaces`), **Algebraic geometry** (`math.geom.algebraic-geometry`), **Sheaves** (`math.geom.sheaves`).
- Geometry in physics: **The geometry of spacetime: special and general relativity** (`math.applied.relativity`).

### Optional research pathways

- **Low-dimensional topology: 3- and 4-manifolds** (`math.geom.low-dimensional-topology`).
- **Geometric group theory** (`math.geom.geometric-group-theory`).
- **Symplectic geometry and topology** (`math.geom.symplectic-geometry`).
- **Complex and Kähler geometry; Hodge theory** (`math.geom.complex-kahler-geometry`).
- **Stable homotopy theory and generalised cohomology** (`math.geom.stable-homotopy-theory`).
- **Geometric analysis** (`math.analysis.geometric-analysis`), **Gauge theory and the geometry of physics** (`math.applied.gauge-theory`).

## Where the thread meets the other foundations

| Meeting point | What connects |
| --- | --- |
| Point-set topology ↔ set theory | A topology is a family of subsets closed under unions and finite intersections; compactness arguments use Zorn's lemma (Tychonoff). |
| Algebraic topology ↔ category theory | Homology and π₁ are functors; category theory was created (Eilenberg–Mac Lane, 1945) to make "natural" precise in topology. |
| Sheaves ↔ logic and topoi | The sheaves on a space form a topos; its internal logic is intuitionistic. |
| Homotopy theory ↔ type theory | Homotopy type theory reads types as spaces and identifications as paths. |
| Riemannian geometry ↔ analysis | Curvature is governed by PDE (Ricci flow, minimal surfaces); Gauss–Bonnet links curvature to the Euler characteristic. |
| Knots ↔ physics | The Jones polynomial arises from Chern–Simons theory. |
| Riemann surfaces ↔ number theory | A complex elliptic curve is a torus; its rational points are arithmetic geometry. |
