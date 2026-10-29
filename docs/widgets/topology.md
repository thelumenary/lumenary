# Topology and geometry widgets

Six interactive explorations for the topologist's and geometer's viewpoints, from "Shapes" and "Symmetry" up to surfaces, non-Euclidean geometry, the fundamental group, knot theory and differential geometry. Each one is a client component registered in `src/components/widgets/registry-topology.ts`. You use it in a lesson's MDX by its tag name.

Things that hold for all six:

- Every prop is optional. Bad values are ignored or clamped, so a typo never crashes the page; you just get the default.
- `title` and `subtitle` (strings) replace the widget's translated heading. Write them in the lesson's language. If you leave them out, the reader sees the heading in their own interface language.
- MDX attribute syntax: strings are written as `prop="…"`, everything else as `prop={…}`, for example `solids={["cube", "torus"]}`, `askCount={false}` or `punctures={[[-1.6, 0], [1.6, 0]]}`.
- Where a widget shows numerical evidence, it says so on screen. Examples are labelled as evidence, not proof. Analogies are labelled as analogies.

---

## EulerCounter

**What it does.** A gallery of polyhedra drawn as see-through wireframes. The reader can drag them or turn them with buttons, and edges at the back are dashed. They count vertices V, edges E and faces F themselves: they type their answers, press **Check**, and can **Reveal** if stuck. Clicking a box highlights the vertices, edges or faces in the drawing. Then they see V − E + F. Every solid without holes gives 2. The picture-frame torus gives 0 and the two-holed frame gives −2. A results table fills in as solids are counted.

The **Surfaces and genus** tab shows sphere, torus, double torus and triple torus with χ = 2 − 2g. It pairs each with a polyhedron from the gallery that is the same surface cut into faces. It also has a "cut it up differently" panel: three refinement moves (split an edge, cut a face with a diagonal, add a vertex inside a face) change V, E and F but never χ. This illustrates that χ is a topological invariant, with an explicit note that examples are not a proof and that the general proof needs common refinements or homology. It also notes that the formula is only for orientable surfaces.

**Suits:** Shapes (K–2: counting corners, edges and faces with `askCount`), 3D solids (3–8), Euler's formula, Surfaces and the Euler characteristic, the classification of surfaces.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `solids` | string[] | all nine | Which solids appear, in this order. Ids: `"tetrahedron"`, `"cube"`, `"octahedron"`, `"dodecahedron"`, `"icosahedron"`, `"prism"` (triangular prism), `"pyramid"` (square pyramid), `"torus"` (picture frame with one hole: V = 16, E = 32, F = 16), `"doubleTorus"` (frame with two holes: V = 32, E = 64, F = 30). |
| `tab` | `"solids"` \| `"surfaces"` | `"solids"` | Which tab is open first. |
| `askCount` | boolean | `true` | `true`: the reader types V, E, F and checks them. `false`: the counts are shown straight away. |
| `title`, `subtitle` | string | translated | Heading overrides. |

```mdx
<EulerCounter solids={["cube", "tetrahedron", "pyramid"]} title="Count the corners, edges and faces" />
```

```mdx
<EulerCounter solids={["tetrahedron", "cube", "octahedron", "dodecahedron", "icosahedron"]} subtitle="The five Platonic solids: what do you notice about V − E + F?" />
```

```mdx
<EulerCounter solids={["cube", "torus", "doubleTorus"]} askCount={false} subtitle="Holes change the answer: χ = 2 − 2g." />
```

```mdx
<EulerCounter tab="surfaces" />
```

---

## CurvedTriangles

**What it does.** Geodesic triangles in three geometries. The reader drags the vertices (or focuses one and uses the arrow keys) and watches the angle sum. In **Flat plane** it is always 180°. On the **Sphere** the drawing is an orthographic view that can be turned; the sides are great-circle arcs and the angle sum exceeds 180°. In the **Hyperbolic plane** (Poincaré disk; sides are arcs orthogonal to the boundary, drawn extended to the boundary in dashes) it falls short of 180°. Angles are computed exactly from the models: tangent vectors on the sphere, and Euclidean angles between arc tangents in the conformal disk.

The area is computed *independently* by numerical boundary integration, so the readout honestly shows that excess = area / R² on the sphere and defect = area at curvature −1. A green check appears when they agree. Presets include the three-right-angle triangle covering 1/8 of the sphere. A table relates all three to "angle sum − π = K · area" and calls it a first glimpse of the Gauss–Bonnet theorem.

**Suits:** Angle sum of a triangle (6–8), Spherical geometry and navigation, Non-Euclidean geometry, the parallel postulate, Gaussian curvature, Gauss–Bonnet, Riemannian geometry.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `mode` | `"plane"` \| `"sphere"` \| `"hyperbolic"` | first of `modes` | Geometry shown first. |
| `modes` | string[] | all three | Which geometry tabs are offered. If only one is given, there are no tabs. |
| `vertices` | 3 points, or `{ plane?, sphere?, hyperbolic? }` | built-in triangles | Starting triangle. A plain array applies to the starting `mode`. **plane:** `[x, y]` with x in −5…5 and y in −3.6…3.6. **sphere:** `[latitude, longitude]` in degrees (north pole = `[90, 0]`). **hyperbolic:** `[x, y]` inside the unit disk (clamped to radius 0.93). The object form sets several geometries at once. |
| `title`, `subtitle` | string | translated | Heading overrides. |

```mdx
<CurvedTriangles modes={["plane"]} title="Do the angles of a triangle always add up to 180°?" />
```

```mdx
<CurvedTriangles mode="sphere" modes={["sphere"]} vertices={[[90, 0], [0, 0], [0, 90]]} subtitle="Start at the North Pole, walk to the equator, turn 90°, walk a quarter of the way round, turn 90° and walk home." />
```

```mdx
<CurvedTriangles mode="hyperbolic" modes={["plane", "hyperbolic"]} vertices={{ hyperbolic: [[-0.7, -0.4], [0.75, -0.35], [0, 0.8]] }} />
```

```mdx
<CurvedTriangles mode="sphere" subtitle="A first glimpse of Gauss–Bonnet: angle sum − π = K · area." />
```

---

## SurfaceGluing

**What it does.** Closed surfaces made from a square with its sides glued in pairs. Arrows on the sides show the gluing (single arrow = a, double arrow = b). The surfaces are the torus a b a⁻¹ b⁻¹, the Klein bottle a b a⁻¹ b, the sphere a a⁻¹ b b⁻¹ and the real projective plane a b a b. The words are read counter-clockwise from the bottom-left corner.

A little flatlander holding a flag in its *left* hand walks around. It goes forward and back, turns to its own left or right, or walks continuously, using buttons, the arrow keys (the square is focusable) or a drag. When it crosses a side it re-enters through the partner side; near a seam a ghost copy shows it passing through. If that gluing reverses orientation, it comes back **mirror-reversed**: the flag changes sides and its trail turns violet and dashed. So learners *see* non-orientability, and the text points out that a mirrored creature's "left turn" looks clockwise to us.

The panel states orientability and χ (torus 0, Klein bottle 0, sphere 2, projective plane 1), and derives χ = V − E + F from how the corners glue together. The **Tiling view** (torus and Klein bottle only) shows a 3 × 3 patch of the plane tiled by copies of the square. For the Klein bottle, alternate columns are flipped. The plane is described as the universal cover. For the sphere and the projective plane, the widget explains why there is no flat tiling.

**Suits:** Symmetry and reflections (as an informal "mirror world" story), video-game wrap-around worlds, Surfaces and the Euler characteristic, orientability, the classification of surfaces, covering spaces and the fundamental group (tiling view).

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `surface` | `"torus"` \| `"klein"` \| `"sphere"` \| `"rp2"` | first of `surfaces` | Surface shown first. |
| `surfaces` | string[] | all four | Which surface buttons are offered. If only one is given, there are no buttons. |
| `showTiling` | boolean | `false` | Start in the tiling view (only takes effect for `"torus"` and `"klein"`). |
| `title`, `subtitle` | string | translated | Heading overrides. |

```mdx
<SurfaceGluing surfaces={["torus"]} title="A world that wraps around" subtitle="Walk off one edge and you come back on the other — like many video games." />
```

```mdx
<SurfaceGluing surface="klein" surfaces={["torus", "klein"]} />
```

```mdx
<SurfaceGluing surface="torus" surfaces={["torus", "klein"]} showTiling subtitle="Unrolled: copies of the square tile the plane (the universal cover)." />
```

```mdx
<SurfaceGluing surface="rp2" />
```

---

## KnotColoring

**What it does.** Knot and link diagrams with proper over/under gaps: the unknot (drawn with one twist), the trefoil 3₁, the figure-eight knot 4₁, the Hopf link and the cinquefoil 5₁. The diagrams are computed from 3D curves, and the crossings are found numerically.

Clicking an arc (or focusing it and pressing Enter, or 1/2/3) cycles it through three colours. Each colour also has a shape (circle, triangle, square), so colour is never the only cue. Every crossing is checked against the rule "all three arcs the same colour or all different" and marked ✓ or ✗. A valid colouring with at least two colours is announced as a tricolouring. **Try every colouring** checks all 3ⁿ colourings and reports how many are valid (trefoil: 9, of which 3 use one colour; the others: only the 3 one-colour ones). If one exists, it shows a three-colour solution.

The panel shows the crossings in this diagram next to the crossing number (for the twisted unknot: 1 versus 0), and the linking number ±1 for the Hopf link. The text explains that tricolourability is a knot invariant because it survives Reidemeister moves. So the trefoil is not the unknot. The figure-eight knot is not tricolourable yet is knotted, which shows that invariants can fail to distinguish knots.

**Suits:** Patterns and colouring rules (as a puzzle), Knot theory, invariants in general, Reidemeister moves, Low-dimensional topology.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `knot` | `"unknot"` \| `"trefoil"` \| `"figureEight"` \| `"hopf"` \| `"cinquefoil"` | `"trefoil"` (or the first of `knots`) | Diagram shown first. |
| `knots` | string[] | all five | Which diagrams are offered. If only one is given, there are no buttons. |
| `title`, `subtitle` | string | translated | Heading overrides. |

```mdx
<KnotColoring knot="trefoil" knots={["unknot", "trefoil"]} subtitle="Can you colour the trefoil? Can you colour the unknot?" />
```

```mdx
<KnotColoring knot="figureEight" knots={["trefoil", "figureEight"]} subtitle="An invariant that says 'no' twice proves nothing." />
```

```mdx
<KnotColoring knot="hopf" knots={["hopf"]} title="Can these two rings be pulled apart?" />
```

```mdx
<KnotColoring />
```

---

## WindingNumber

**What it does.** The plane with one or two holes (punctures), which the reader can drag or move with the arrow keys, and a closed loop. Preset loops are a circle, a figure eight, a loop going twice around, and a crescent that curls around a hole without enclosing it. **Draw your own** lets the reader sketch any loop with a pointer; it closes automatically. Keyboard users choose a preset.

**Play** (or the slider) sends a point around the loop. A dashed radius vector from each hole follows it, and a growing spiral shows the angle swept so far. The winding number around each hole is computed by adding up the change of argument. Next to it the widget shows (1/2πi)∮ dz/(z − a), computed separately by the midpoint rule; it should match. If the loop runs through a hole, the widget says the winding number is undefined there.

The text explains that loops in the once-punctured plane are classified up to homotopy by their winding number (π₁ = ℤ, as for the circle). With two holes it says honestly that winding numbers no longer tell the whole story: the fundamental group is free on two generators, and the commutator loop winds 0 around each hole yet is not contractible.

**Suits:** Angles and turning (as "how many times did you turn around?"), polar coordinates, the argument of a complex number, the fundamental group, homotopy, complex analysis (Cauchy's integral formula, the argument principle, residues).

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `punctures` | `[[x, y], …]` (1 or 2 points) | `[[-1.6, 0]]` | Hole positions, in the box −5…5 × −5…5 (y up). Extra points are ignored. The presets are designed around `[-1.6, 0]` and `[1.6, 0]`; the reader can add or remove the second hole. |
| `loop` | `"circle"` \| `"figureEight"` \| `"twice"` \| `"miss"` | first of `loops` | Starting loop. With the default holes, the winding numbers around (−1.6, 0) and (1.6, 0) are circle 1 and 1, figure eight −1 and 1, twice 2 and 0, miss 0 and 0. |
| `loops` | string[] | all four | Which preset buttons are offered ("Draw your own" is always available). |
| `title`, `subtitle` | string | translated | Heading overrides. |

```mdx
<WindingNumber loop="circle" loops={["circle", "twice", "miss"]} subtitle="How many times does the arrow turn all the way round?" />
```

```mdx
<WindingNumber punctures={[[-1.6, 0], [1.6, 0]]} loop="figureEight" />
```

```mdx
<WindingNumber loop="twice" loops={["circle", "twice"]} title="Winding number and ∮ dz/(z − a)" subtitle="The integral counts how many times the loop winds around a." />
```

---

## CurveCurvature

**What it does.** The geometer's curvature of plane curves. The curves are a circle (radius slider), an ellipse (height slider), a parabola y = kx² − 1.2 (steepness slider), a cardioid, a figure eight (Bernoulli's lemniscate), a limaçon r = 1 + c·cos θ (slider for c), and a cubic Bézier curve with four draggable control points.

A point moves along the curve at constant speed (press **Play** or use the slider). It shows the unit tangent T, the unit normal N (T turned 90° left) and the **osculating circle**: radius 1/|κ|, centre on the side the curve bends towards. Where κ ≈ 0 the circle becomes a dashed tangent line. Below, the signed curvature κ(s) is plotted against arc length, with positive area shaded teal and negative area terracotta.

The total curvature ∫ κ ds is computed numerically from exact derivatives and shown as a multiple of 2π. For closed regular curves it states the turning number and Hopf's Umlaufsatz: circle and ellipse 1, the limaçon with an inner loop 2, the figure eight 0. Sliding c across 1 makes the turning number jump through a cusp. For the cardioid it explains the cusp: the smooth part turns by 3π, and the cusp contributes −π. For open curves, ∫ κ ds is just the total turn of the tangent.

**Suits:** Circles and radius (as "how sharply does the road bend?"), Conic sections, Calculus of plane curves and arc length, Differential geometry of curves and surfaces, the Umlaufsatz and the Whitney–Graustein theorem.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `curve` | `"circle"` \| `"ellipse"` \| `"parabola"` \| `"cardioid"` \| `"lemniscate"` \| `"limacon"` \| `"bezier"` | first of `curves` | Curve shown first. |
| `curves` | string[] | all seven | Which curve buttons are offered. If only one is given, there are no buttons. |
| `showOsculating` | boolean | `true` | Whether the osculating circle starts switched on (the reader can toggle it). |
| `params` | `{ R?, b?, k?, c?, ctrl? }` | `{ R: 1.5, b: 1.1, k: 0.5, c: 2, ctrl: [[-2.4,-1.2],[-1.2,1.9],[1,-1.9],[2.4,1.1]] }` | Starting shape. `R` = circle radius (0.4–2.2). `b` = ellipse half-height, with half-width 2 (0.3–2). `k` = parabola steepness (0.1–0.75). `c` = limaçon parameter (0.2–2.5; c > 1 gives an inner loop, c = 1 is a cardioid with a cusp). `ctrl` = four Bézier control points `[x, y]` in −3.2…3.2 × −2.4…2.4. |
| `title`, `subtitle` | string | translated | Heading overrides. |

```mdx
<CurveCurvature curve="circle" curves={["circle", "ellipse"]} subtitle="A small circle bends sharply: κ = 1/R." />
```

```mdx
<CurveCurvature curve="limacon" curves={["circle", "limacon", "lemniscate"]} subtitle="Hopf's Umlaufsatz: ∫ κ ds = 2π × turning number." />
```

```mdx
<CurveCurvature curve="bezier" curves={["bezier"]} params={{ ctrl: [[-2.5, -1], [-0.5, 2], [0.5, -2], [2.5, 1]] }} title="Where does the curve change from bending left to bending right?" />
```

```mdx
<CurveCurvature curve="parabola" curves={["parabola", "ellipse"]} showOsculating={false} />
```
