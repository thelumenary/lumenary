# Discrete widgets: graphs, logic, probability, commutative diagrams

Four tags for lessons on discrete mathematics, logic, probability and category theory:

| Tag | Kind | What it is for |
| --- | --- | --- |
| `<GraphExplorer>` | interactive (client) | finite graphs: degrees, walks and Euler trails, colouring, spanning trees, adjacency matrices |
| `<TruthTable>` | interactive (client) | truth tables for propositional formulas, classification, equivalence |
| `<ChanceLab>` | interactive (client) | seeded probability simulations shown next to the exact value |
| `<CommutativeDiagram>` | static (server) | typeset commutative diagrams, no client JavaScript |

General MDX rules: strings are written `prop="…"`; numbers, booleans, arrays and objects are written `prop={…}`. Every prop is optional. Malformed entries are skipped, and the widget says so instead of crashing. `title` and `subtitle` (on the three interactive widgets) replace the default translated heading; write them in English, like the rest of the lesson.

Code: `src/components/widgets/{GraphExplorer,TruthTable,ChanceLab,CommutativeDiagram}.tsx`, logic in `src/components/widgets/lib/{graph,logic,chance,diagram}-core.ts`, tests in `tests/widgets-discrete.test.ts`.

---

## GraphExplorer

Draws a finite graph (an undirected multigraph without loops) and offers up to five tabs. **Degrees**: every vertex shows its degree, the sum is checked against the handshake lemma Σ deg(v) = 2|E|, and selecting a vertex highlights its edges. **Walks**: click edges one after another (or a start vertex first) to build a walk; the widget says whether it is a trail, closed, a circuit, an Euler trail or an Euler circuit, and explains from the odd-degree vertices whether an Euler trail or circuit can exist at all. **Colouring**: click vertices to cycle through six colours (each also numbered, so colour is never the only cue); clashes and the number of colours are reported, "Try greedy" runs a largest-degree-first greedy colouring, and "Fewest possible?" reveals the chromatic number found by exhaustive search (graphs with up to 16 vertices). For presets whose planarity is known it states the Four Colour Theorem honestly, as a theorem proved with computer assistance (Appel–Haken 1976; Gonthier's Coq proof, 2005). **Spanning trees**: click edges to build a spanning tree; it checks for cycles (and names one), connectedness and |E| = |V| − 1, and reports the exact number of spanning trees (Kirchhoff's matrix-tree theorem). **Matrix**: the adjacency matrix A and its powers A^k for k = 1…6; choosing a cell explains that the entry counts walks of length k (and lists them when there are few), with notes on row sums, the diagonal of A² and triangles via trace(A³)/6.

Suits: Euler and the Königsberg bridges, the handshake lemma, graph colouring and map colouring, trees, networks, adjacency matrices and matrix powers, an introduction to linear algebra through counting.

Everything works by keyboard (Tab to vertices and edges, Enter or Space to select; Delete removes a vertex's colour) and on phones.

### Props

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `preset` | string | `"konigsberg"` | One of `"konigsberg"` (7-bridge multigraph), `"k4"`, `"k5"`, `"k33"`, `"petersen"`, `"cube"` (Q₃, vertices labelled 000…111), `"cycle6"`, `"tree"` (7-vertex binary tree), `"wheel"` (hub plus 5 rim vertices, needs 4 colours). Ignored when `nodes` or `edges` is given. |
| `nodes` | (string \| number)[] | — | Custom vertex labels, e.g. `["A","B","C"]`. Keep labels short (1–3 characters draw best). At most 30 vertices. |
| `edges` | [a, b][] | — | Custom edges. Each endpoint is a **label (string)** or a **0-based index (number)**. Repeat a pair for parallel edges; loops (`["A","A"]`) are skipped. At most 90 edges. If `nodes` is omitted, the vertices are taken from the edges. |
| `positions` | [x, y][] or {x, y}[] | circle | One position per vertex, in any units: **x to the right, y downwards** (so a tree's root has the smallest y). The drawing is scaled to fit. If the list is missing, too short or malformed, vertices go on a circle. |
| `mode` | string | first of `modes` | Tab to open first: `"degrees"`, `"walk"`, `"colour"`, `"spanning"`, `"matrix"`. |
| `modes` | string[] | all five | Which tabs to offer, in order. With a single mode no tab bar is shown. |
| `presets` | string[] | all presets when neither `preset` nor a custom graph is given; otherwise none | Presets to offer in a "Graph" picker. Ignored for custom graphs. |
| `title`, `subtitle` | string | translated | Override the heading. |

### Examples

The Königsberg bridges, walks only:

```mdx
<GraphExplorer preset="konigsberg" modes={["walk", "degrees"]} title="Can you cross every bridge exactly once?" />
```

A custom graph with labels and positions (a small town), starting on degrees:

```mdx
<GraphExplorer
  nodes={["Home", "Shop", "Park", "School"]}
  edges={[["Home", "Shop"], ["Shop", "Park"], ["Park", "Home"], ["Park", "School"], ["Shop", "School"]]}
  positions={[[0, 0], [2, 0], [1, 1.5], [3, 1.5]]}
  modes={["degrees", "walk"]}
/>
```

Map colouring: four countries that all touch each other, then K₅, which is not planar:

```mdx
<GraphExplorer preset="k4" modes={["colour"]} subtitle="Each vertex is a country; an edge means the two share a border." />
<GraphExplorer presets={["k4", "wheel", "petersen", "k5"]} mode="colour" />
```

Counting walks with matrix powers on the cube, using indices instead of labels:

```mdx
<GraphExplorer preset="cube" modes={["matrix"]} />
<GraphExplorer nodes={["1", "2", "3", "4"]} edges={[[0, 1], [1, 2], [2, 3], [3, 0], [0, 2]]} modes={["matrix", "spanning"]} />
```

---

## TruthTable

A text box for a propositional formula, symbol buttons that insert at the cursor, and the full truth table with one column per sub-formula (togglable), the main column highlighted. It shows how the formula was read (fully bracketed), classifies it as a **tautology**, **contradiction** or **contingent**, and with a second formula tests **logical equivalence**, marking the rows where they differ with ≠ (not only by colour). Short example buttons load the contrapositive, converse, De Morgan, excluded middle and distributive law. Errors are explained inline with the character position.

Suits: introductions to logic and proof, conditionals and their converse/contrapositive, De Morgan's laws, Boolean algebra, digital logic.

### Formula syntax

- Variables: single **lowercase** letters `a`–`z` (at most 6 in one table, i.e. 64 rows). Write `p ∧ q`, not `pq`.
- Constants: `T`/`F`, `true`/`false`, `⊤`/`⊥`, `1`/`0`.
- Operators, tightest first (all spellings are equivalent):

| Meaning | Symbol | Word | ASCII |
| --- | --- | --- | --- |
| not | `¬` | `not` | `~` or `!` |
| and | `∧` | `and` | `&`, `&&`, `/\` |
| or | `∨` | `or` | `\|`, `\|\|`, `\/` |
| exclusive or (same level as or) | `⊕` | `xor` | — |
| implies | `→` or `⇒` | `implies` | `->` or `=>` |
| if and only if | `↔`, `⇔` or `≡` | `iff` | `<->` or `<=>` |

- `→` is right-associative: `p → q → r` means `p → (q → r)`. `∧`, `∨` and `↔` group to the left. Use brackets `( )` freely.
- Rows are listed in textbook order, starting with every variable true (T T, T F, F T, F F). In other languages the letters T/F are translated (e.g. V/F in Spanish).

### Props

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `formula` | string | `"p → q"` | The formula shown first (learners can edit it). |
| `compare` | string | — | A second formula; when given, the comparison box opens and equivalence is tested. |
| `showSubformulas` | boolean | `true` | Whether sub-formula columns are shown at first (there is a toggle). |
| `title`, `subtitle` | string | translated | Override the heading. |

### Examples

```mdx
<TruthTable formula="p -> q" compare="~q -> ~p" title="A statement and its contrapositive" />
```

```mdx
<TruthTable formula="not (p and q)" compare="not p or not q" />
```

```mdx
<TruthTable formula="(p → q) ∧ (q → r) → (p → r)" showSubformulas={false} subtitle="Is this argument form always valid?" />
```

```mdx
<TruthTable formula="p xor q" compare="(p or q) and not (p and q)" />
```

---

## ChanceLab

Probability experiments run with a small **seeded** random number generator (mulberry32), so the page renders identically on server and client; "New run" changes the seed and animates the run (no animation under `prefers-reduced-motion`), "Replay" re-animates the same run. Every experiment shows the simulated value **next to the exact value** (simulation in teal, exact in violet, also distinguished by line style and markers) and ends with an "Evidence, not proof" note naming the number of trials and the run.

| `experiment` | What it shows | Uses |
| --- | --- | --- |
| `"coin"` | running proportion of heads → 1/2 (law of large numbers), with the band 1/2 ± 1/√n and faint earlier runs | `trials` = flips |
| `"dice"` | one fair die: histogram vs the exact 1/6 | `trials` = rolls |
| `"two-dice"` | sum of two dice vs the exact triangular distribution (ways out of 36) | `trials` = rolls |
| `"galton"` | Galton board: binomial counts, exact binomial expectation C(n, j)/2ⁿ, normal approximation, path of the latest ball | `trials` = balls, `n` = rows (1–20, default 10) |
| `"random-walk"` | 8 of many ±1 walks, the root-mean-square distance vs the exact √n | `trials` = walks (≤ 2,000, default 200), `n` = steps (10–1,000, default 100) |
| `"birthday"` | probability of a shared birthday in a group of k: simulated estimate with a 95% interval on the exact curve 1 − 365·364···(365−k+1)/365ᵏ | `trials` = groups, `k` = group size (2–100, default 23) |
| `"monty-hall"` | running win rates for sticking and switching vs exact 1/3 and 2/3, plus a "play it yourself" game with a running tally | `trials` = games |
| `"buffon"` | Buffon's needle (needle length = line spacing): crossing proportion vs 2/π and the estimate π ≈ 2N/C with a 95% margin and the actual error; directions are sampled without using π | `trials` = needles |

### Props

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `experiment` | string | `"coin"` | Experiment to show first (see table). Given alone, only that experiment is shown (no tabs). |
| `experiments` | string[] | all eight (or just `experiment`) | Which experiments to offer as tabs, in order. |
| `trials` | number | per experiment (500–1,000) | Starting number of trials, 10–10,000; the slider offers 10, 20, 50, …, 10,000 plus this value. Applies to every offered experiment. |
| `n` | number | 10 rows / 100 steps | Galton rows (1–20) and random-walk steps (10–1,000). |
| `k` | number | 23 | Birthday group size (2–100). |
| `title`, `subtitle` | string | translated | Override the heading (the default subtitle describes the current experiment). |

### Examples

```mdx
<ChanceLab experiment="coin" trials={1000} title="Does the coin remember?" />
```

```mdx
<ChanceLab experiments={["dice", "two-dice"]} trials={2000} />
```

```mdx
<ChanceLab experiment="galton" n={12} trials={1000} />
<ChanceLab experiment="birthday" k={30} />
```

```mdx
<ChanceLab experiments={["monty-hall", "buffon", "random-walk"]} />
```

---

## CommutativeDiagram

A **server component**: the diagram is laid out and typeset with KaTeX when the page is built, so it ships no JavaScript and is not wrapped in the interactive-widget card; it sits centred in the text like displayed maths. Objects sit on a grid; arrows stop short of the object boxes, may bend, and parallel pairs between the same two objects (in either direction) are automatically drawn side by side with their labels on the outside. Strokes use `currentColor`, so diagrams are crisp in light and dark mode. Screen readers get an `aria-label` listing the objects and every arrow ("f from A to B; g (dashed) from B to C; …"), generated in English from the TeX; pass `ariaLabel` to write your own.

The lesson macros `\N \Z \Q \R \C \cat{…} \id \Hom` work in labels.

### TeX inside `{…}` needs doubled backslashes

`objects` and `arrows` are JavaScript, so **every backslash must be doubled**: write `tex: "A \\times B"`, `tex: "\\pi_1"`. (A single `"\to"` would become a TAB followed by `o`. The widget repairs the common cases `\t \f \b \v \r \n` — e.g. `\to`, `\frac`, `\beta`, `\nu`, `\rho`, `\vee` — but `"\mathbb{Z}"` silently loses its backslash, so always double them.) The `caption` is a plain attribute string, so there a single backslash is right, and `$…$` in the caption is typeset: `caption="The square $g \circ f = k \circ h$ commutes."`

### Props

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `objects` | `{ id, tex, row, col }[]` | `[]` | `id`: unique name used by arrows. `tex`: label (defaults to `id`). `row` grows downwards, `col` to the right; numbers, fractions allowed (e.g. `col: 0.5` for the apex of a triangle). |
| `arrows` | `{ from, to, tex?, style?, bend?, labelSide? }[]` | `[]` | `from`/`to`: object ids (must differ). `tex`: label. `style`: `"solid"` (default), `"dashed"` (e.g. a unique induced map), `"hook"` (↪ injection/monomorphism), `"epi"` (↠ two-headed, surjection/epimorphism), `"double"` (⇒, e.g. a natural transformation or 2-cell), `"iso"` (solid with ≅ beside it). `bend`: degrees, −75…75; positive bends to the **left of the direction of travel** (tikz-cd `bend left`). `labelSide`: `"left"` (default, tikz-cd's default) or `"right"` (tikz-cd's `'` swap), relative to the direction of travel: a rightward arrow's left is above, a downward arrow's left is to the screen's right. In a parallel pair labels always go outside. |
| `caption` | string | — | Text under the diagram; `$…$` is typeset. |
| `size` | `"sm"` \| `"md"` \| `"lg"` | `"md"` | Grid spacing and font size. Use `"sm"` for long rows such as exact sequences. |
| `ariaLabel` | string | generated | Replaces the generated screen-reader description. |

### Examples

A commutative square:

```mdx
<CommutativeDiagram
  objects={[
    { id: "A", tex: "A", row: 0, col: 0 },
    { id: "B", tex: "B", row: 0, col: 1 },
    { id: "C", tex: "C", row: 1, col: 0 },
    { id: "D", tex: "D", row: 1, col: 1 },
  ]}
  arrows={[
    { from: "A", to: "B", tex: "f" },
    { from: "A", to: "C", tex: "g", labelSide: "right" },
    { from: "B", to: "D", tex: "h" },
    { from: "C", to: "D", tex: "k", labelSide: "right" },
  ]}
  caption="The square commutes: $h \circ f = k \circ g$."
/>
```

A product, with the unique induced arrow dashed:

```mdx
<CommutativeDiagram
  objects={[
    { id: "X", tex: "X", row: 0, col: 1 },
    { id: "P", tex: "A \\times B", row: 1, col: 1 },
    { id: "A", tex: "A", row: 1, col: 0 },
    { id: "B", tex: "B", row: 1, col: 2 },
  ]}
  arrows={[
    { from: "X", to: "A", tex: "f", labelSide: "right" },
    { from: "X", to: "B", tex: "g" },
    { from: "X", to: "P", tex: "\\langle f, g \\rangle", style: "dashed" },
    { from: "P", to: "A", tex: "\\pi_1" },
    { from: "P", to: "B", tex: "\\pi_2", labelSide: "right" },
  ]}
  caption="Any pair $f, g$ factors through $A \times B$ by exactly one dashed arrow."
/>
```

A short exact sequence 0 → A → B → C → 0 (two objects may share the label `0` but need different ids):

```mdx
<CommutativeDiagram
  size="sm"
  objects={[
    { id: "zl", tex: "0", row: 0, col: 0 },
    { id: "A", tex: "A", row: 0, col: 1 },
    { id: "B", tex: "B", row: 0, col: 2 },
    { id: "C", tex: "C", row: 0, col: 3 },
    { id: "zr", tex: "0", row: 0, col: 4 },
  ]}
  arrows={[
    { from: "zl", to: "A" },
    { from: "A", to: "B", tex: "f", style: "hook" },
    { from: "B", to: "C", tex: "g", style: "epi" },
    { from: "C", to: "zr" },
  ]}
  caption="Exact: the image of $f$ is the kernel of $g$."
/>
```

A naturality square for η : F ⇒ G:

```mdx
<CommutativeDiagram
  objects={[
    { id: "FX", tex: "F(X)", row: 0, col: 0 },
    { id: "GX", tex: "G(X)", row: 0, col: 1 },
    { id: "FY", tex: "F(Y)", row: 1, col: 0 },
    { id: "GY", tex: "G(Y)", row: 1, col: 1 },
  ]}
  arrows={[
    { from: "FX", to: "GX", tex: "\\eta_X" },
    { from: "FX", to: "FY", tex: "F(f)", labelSide: "right" },
    { from: "GX", to: "GY", tex: "G(f)" },
    { from: "FY", to: "GY", tex: "\\eta_Y", labelSide: "right" },
  ]}
  caption="Naturality: $G(f) \circ \eta_X = \eta_Y \circ F(f)$."
/>
```

A pullback, with bent arrows from the competing cone and the unique dashed arrow:

```mdx
<CommutativeDiagram
  objects={[
    { id: "Q", tex: "Q", row: 0, col: 0 },
    { id: "P", tex: "A \\times_C B", row: 1, col: 1 },
    { id: "A", tex: "A", row: 1, col: 2 },
    { id: "B", tex: "B", row: 2, col: 1 },
    { id: "C", tex: "C", row: 2, col: 2 },
  ]}
  arrows={[
    { from: "Q", to: "A", tex: "q_1", bend: 20 },
    { from: "Q", to: "B", tex: "q_2", bend: -20, labelSide: "right" },
    { from: "Q", to: "P", tex: "u", style: "dashed" },
    { from: "P", to: "A", tex: "p_1" },
    { from: "P", to: "B", tex: "p_2", labelSide: "right" },
    { from: "A", to: "C", tex: "f" },
    { from: "B", to: "C", tex: "g", labelSide: "right" },
  ]}
  caption="The pullback of $f$ and $g$."
/>
```

An adjunction F ⊣ G (an opposite-direction pair is drawn side by side automatically):

```mdx
<CommutativeDiagram
  objects={[
    { id: "C", tex: "\\mathcal{C}", row: 0, col: 0 },
    { id: "D", tex: "\\mathcal{D}", row: 0, col: 1 },
  ]}
  arrows={[
    { from: "C", to: "D", tex: "F" },
    { from: "D", to: "C", tex: "G" },
  ]}
  caption="An adjunction $F \dashv G$."
/>
```

Also handy: an equaliser pair is simply two arrows with the same `from` and `to` (`f` drawn on top, `g` below); `{ from: "A", to: "B", style: "iso" }` marks an isomorphism; two arrows between the same objects with `bend: 30` and `bend: -30` draw a pair of parallel curved arrows, e.g. for a 2-cell together with a `"double"` arrow.

### Notes

- The layout estimates TeX widths (it cannot measure on the server). Very long labels may sit slightly close to an arrow end; give such objects more room with fractional `col` values or `size="lg"`.
- Labels are KaTeX inside SVG `<foreignObject>`. Browsers scale them with the SVG on narrow screens; diagrams wider than the column scroll horizontally rather than shrinking below 240 px.
