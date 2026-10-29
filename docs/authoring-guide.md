# Lesson authoring guide

This is the working contract for writing a Lumenary lesson (a "module"): what files to create, what every lesson must contain, the conventions for its Lean and Python, and the checks that must pass. It applies to human contributors and to AI-assisted drafting alike. Read `docs/architecture.md` first for the big picture.

> **The rule above all others: never claim what has not happened.** A lesson is labelled `ai-drafted` until a named human reviews it. "Formally verified" and "computationally tested" labels are derived from build reports, never written by hand. Established theorems, conjectures, heuristics, analogies and numerical evidence are always labelled as what they are.

## 1. Files for one lesson

For a topic `math.<area>.<name>` in `content/math/graph/graph.json`, the lesson slug is `<name>` (the last segment of the id).

| File | Purpose |
| --- | --- |
| `content/math/lessons/<slug>/en.mdx` | The canonical lesson (frontmatter + MDX body). |
| `content/math/lessons/<slug>/exercises.json` | Exercises with hints, feedback and worked solutions. |
| `formal/Lumenary/<Module>.lean` | The lesson's Lean declarations. `<Module>` is the slug in PascalCase (`point-set-topology` → `PointSetTopology`). |
| `formal/LumenaryExercises/<Module>.lean` | Optional Lean exercises (statements with `sorry`; solutions in the main file). |
| `compute/experiments/<id>.py` | One or more Python experiments. Ids start with the slug in snake_case (`point_set_topology_open_sets`). |
| `compute/tests/test_<id>.py` | pytest tests for each experiment. |

Do **not** edit shared files (the graph, pathways, message catalogues, components, other lessons, root Lean files, verification reports). The coordinator links the lesson into the graph (`status`, `lesson`) after it passes its checks. Lake builds every module under `formal/Lumenary/` automatically (library globs), so no index file needs editing.

## 2. Frontmatter

```yaml
---
slug: point-set-topology
topic: math.geom.point-set-topology
title: Metric spaces and point-set topology
subtitle: One sentence that makes a learner want to read on (inline Markdown and $maths$ allowed).
level: ug2                       # must equal the topic's level in the graph
ages: Undergraduate (or any age) # human-readable; for school levels e.g. "Ages 11–14"
minutes: 90                      # honest reading-and-working time
order: 6012                      # given to you by the coordinator; never reuse
objectives:                      # 3–6, concrete and checkable; usually adapted from the graph topic
  - Define open and closed sets in a metric space and prove basic properties
narrators: []                    # chloe | margaret | gideon — see §4
lean:                            # every Lean declaration the lesson shows, fully qualified
  - Lumenary.PointSetTopology.continuous_comp
compute: [point_set_topology_open_sets]
trails: []                       # existing Wonder Trail slugs only
labels: [ai-drafted]
---
```

## 3. The body: sections

The body is a sequence of `<Section id="…" kind="…" title="…">` blocks (blank lines around their content). Ids are unique within the lesson and stable (they are link anchors). `kind` is one of:

| kind | mode | use for |
| --- | --- | --- |
| `motivation` | H | Why anyone would care: a question, a puzzle, a real situation. |
| `intuition` | H | The idea before the formalism; pictures; small cases. |
| `definitions` | H | Precise definitions (`<Definition>`), notation. |
| `examples` | H | Worked examples, including non-examples and boundary cases. |
| `human` | H | Explanations, discussion, conjectures, the "why". |
| `proof` | H | Theorems with complete, rigorous proofs. |
| `formal` | F | Lean: what is formalised, how it matches the human proof, what Mathlib provides. |
| `computation` | C | Python experiments and what kind of evidence they give. |
| `visualization` | — | An interactive exploration (widget) with guidance on what to try. |
| `exercises` | — | Must contain exactly `<Exercises />`. |
| `misconceptions` | H | `<Misconception>` blocks, each with the correction. |
| `viewpoints` | H | The same mathematics seen by different mathematicians (`<Viewpoint>` blocks) — see §5. |
| `trails` | — | `<Trail slug="…" />` cards for optional Wonder Trails (existing trails only). |
| `sets` | H | The set-theoretic connection (school levels especially). |
| `categories` | H | The category-theoretic connection, where meaningful. |
| `history` | — | History and global context, accurately attributed. |
| `reading` | — | Further reading: real, well-known texts. |

**Required in every lesson:** `exercises`, `formal`, `computation` and `reading`, plus enough of the others to teach the topic properly (at least six sections in all). From early undergraduate onwards a `viewpoints` section is also required (§5). Follow the standard order — motivation → intuition → definitions → examples → proofs → formal → computation → visualization → exercises → misconceptions → viewpoints/sets/categories → trails → history → reading — adapting it when the topic demands.

### Adapting to the learner's age

- **K–2 and 3–5:** short sentences, concrete objects, pictures and play; no formal notation unless it is the point of the lesson. The `formal` section is a game about true/false statements or precise instructions, with the Lean shown inside `<ForGrownUps>`. The `computation` section shows what a computer can count or check, narrated by Margaret. Use widgets generously. 20–35 minutes.
- **6–8 and 9–12:** build from examples to definitions to proof; prove the main results; Lean appears directly in the `formal` section with explanation; Python exercises appear. 40–75 minutes.
- **Undergraduate:** a university-level treatment of the topic's core: definitions, the central theorems with full proofs (or clearly marked proof sketches with references when a full proof would take a course), examples, counterexamples. 60–120 minutes.
- **Graduate and research:** professional, concise, rigorous. A graduate lesson is an entry point to a course: the main definitions and examples, one or two central theorems proved in full, the landscape of the subject, and a reading path. A research lesson is an orientation: what the field studies, its key objects and theorems, a worked example, what is known and what is open (clearly separated), how to start reading. Never fake depth: if a proof is beyond the lesson, say so and cite where it is done. 60–150 minutes.

## 4. Blocks and components

All are used as JSX tags inside MDX (leave blank lines around block content so Markdown inside renders):

| Tag | Use |
| --- | --- |
| `<Definition term="…">` | A precise definition. |
| `<Theorem name="…">` | A statement (also lemmas, propositions, corollaries — say which in `name`). |
| `<Proof>` | A complete proof, directly after the statement. |
| `<Example title="…">` | A worked example. |
| `<Misconception>` | A common error and its correction. |
| `<Note>` | An aside. |
| `<Analogy>` | An intuitive analogy — explicitly not a formal construction. |
| `<Viewpoint lens="…" title="…">` | One mathematician's view (§5). |
| `<Figure caption="…">` | A static diagram, usually an inline `<svg>` (see below). |
| `<ForGrownUps title="…">` | Collapsible detail for adults (school levels). |
| `<Narrator who="chloe\|margaret\|gideon">` | The feline narrators: Chloe (mathematician, "Why is this true?"), Margaret (computationalist, "What happens if we calculate it?"), Gideon (formalist tomcat, "Can we prove this precisely?"). Use them selectively in K–12 lessons, sparingly in UG1, and not at all from UG2 upwards — advanced lessons stay professional. |
| `<Reflection title="…">` | An optional Christian reflection, collapsed by default and clearly separated from the mathematics. At most one per lesson, only where it arises naturally and respectfully, never in an argument, and never in most lessons. Mathematics must never depend on it. |
| `<Lean decl="Lumenary.Module.name" />` | Shows a compiled Lean declaration (source extracted from its region). Every one must be listed in the frontmatter `lean`. |
| `<Python id="…" />` | Shows and runs a tested experiment in the browser. Must be listed in `compute`. |
| `<TopicLink id="math.…">text</TopicLink>` | Links another topic (its lesson if it exists, otherwise its topic page). Use it freely for prerequisites and connections. |
| `<Trail slug="…" />` | A Wonder Trail card (existing trails only: see `content/math/trails/`). |
| `<Exercises />` | The lesson's exercises; only in the `exercises` section. |

**Interactive widgets.** The available widgets and their exact props are documented in `docs/widgets/*.md` (number, shape-data, analysis, discrete, topology), plus the original ones used by the first five lessons (`SortingGame`, `VennExplorer`, `IntegerLine`, `ArrowDiagram`, `CompositionMachine`, …). Most lessons should have at least one widget in a `visualization` section, with a sentence or two on what to try and what to notice. Props are MDX expressions: `fns={["sin(x)", "x - x^3/6"]}`. `CommutativeDiagram` draws commutative diagrams with typeset labels.

**Inline SVG figures.** For static pictures, write SVG inside `<Figure>`: give it a `viewBox`, `role="img"` and an `aria-label`, and colour it with the theme variables so it works in dark mode: `stroke="var(--ink-2)"`, `fill="var(--sky-soft)"`, accents `var(--gold)`, `var(--human)`, `var(--formal)`, `var(--compute)`. Use JSX attribute names (`strokeWidth`, `textAnchor`, `fontSize`, `strokeDasharray`). Keep text short; put mathematics in the caption or surrounding prose.

**Mathematics.** KaTeX renders `$…$` inline and `$$…$$` display maths (put `$$` on their own lines). Macros: `\N \Z \Q \R \C`, `\id`, `\Hom`, `\cat{C}` (bold category name). In MDX prose (outside maths) `{`, `}` and `<` are special: write `\{`, `\}` and `&lt;`, or put the expression in maths. Don't use raw HTML comments (`<!-- -->`); MDX comments are `{/* … */}`. Use Unicode punctuation (—, ‘ ’ “ ”) and proper symbols. British or American spelling is fine; be consistent within a lesson.

## 5. Viewpoints: many ways of seeing

The Lumenary teaches set theory as the language of early mathematics and category theory as a major structural language of higher mathematics. **Neither is the only way to see.** A topologist, a geometer, an analyst, an algebraist, a number theorist, a probabilist, a logician, a combinatorialist and a physicist each notice different things about the same idea, and higher mathematics is the conversation between them.

From early undergraduate onwards every lesson has a `viewpoints` section of `<Viewpoint>` blocks:

| Level | Required |
| --- | --- |
| UG 1 | at least 2 lenses, at least 1 beyond set theory/category theory/logic |
| UG 2, Grad, Research | at least 3 lenses, at least 2 beyond set theory/category theory/logic |

Lenses: `topology`, `geometry`, `analysis`, `algebra`, `number-theory`, `combinatorics`, `probability`, `logic`, `computation`, `physics`, `sets`, `categories`.

How to write a good viewpoint (typically 1–3 paragraphs each, with mathematics, not slogans):

- **Topology** — what is invariant under continuous deformation; spaces of solutions, configurations or maps; connectedness, compactness, holes; homotopy and homology; fixed-point and index theorems. *E.g. for linear algebra: GL(n, ℝ) has two connected components distinguished by the sign of the determinant, and orientation is a topological notion.*
- **Geometry** — distance, angle, curvature, symmetry, shape; the picture; group actions and invariants (Klein's Erlangen programme); manifolds and metrics. *E.g. for groups: every group is the symmetry group of something; for quadratic forms: conics and quadrics.*
- **Analysis** — limits, estimates, approximation, inequalities, convergence, size (measure, norms), the infinite-dimensional version. *E.g. for algebraic topology: de Rham cohomology detects holes with differential forms; for number theory: the zeta function.*
- **Algebra** — the structure underneath: operations, groups/rings/modules acting, invariants as algebraic objects, linearisation. *E.g. for topology: π₁ and homology turn spaces into groups.*
- **Number theory** — integrality, primes, congruences, arithmetic of the objects in question. **Combinatorics** — counting, finite structures, extremal and probabilistic arguments. **Probability** — randomness as a tool or as the subject (random walks, typical behaviour). **Logic** — what can be defined, proved or decided; models; formal systems. **Computation** — algorithms, complexity, what can be computed and how. **Physics** — where the idea lives in physical law, and how physical intuition suggested it (always distinguishing heuristic from proof).
- **Sets** and **categories** — keep them, but as one voice among many: e.g. "a topology is a set with a family of subsets" (sets) and "Top is a category; homotopy is a quotient of it" (categories).

Rules: choose the lenses that genuinely illuminate the topic; be specific and correct (a precise statement, a worked example, or a named theorem — with conditions); mark analogies as analogies; link the relevant topics with `<TopicLink>`. **For topics in geometry, topology and analysis, include the topologist's and/or geometer's view explicitly whenever it is meaningful — and for algebra, logic and category theory topics, look hard for the geometric or topological picture (e.g. Galois theory ↔ covering spaces, Yoneda ↔ the functor of points, sheaves ↔ local-to-global, monads ↔ … ).** School-level lessons may include a `viewpoints` section too (simpler, 1–2 lenses), but are not required to.

## 6. Formal mathematics (Lean 4)

The Lean project lives in `formal/` (Lean `v4.35.0`, Mathlib `v4.35.0`). The website shows exactly the code that compiled, extracted by region markers.

```lean
/-
The Lumenary — formal mathematics
Point-set topology: open sets in metric spaces, continuity, compactness.

What is proved here and what Mathlib already provides — one short paragraph for learners.
-/
import Mathlib.Topology.MetricSpace.Basic

namespace Lumenary.PointSetTopology

-- @region point_set_topology.continuous_comp
-- @provenance library
/-- The composite of continuous maps is continuous. This applies Mathlib's `Continuous.comp`. -/
theorem continuous_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) :=
  hg.comp hf
-- @endregion

end Lumenary.PointSetTopology
```

Conventions (checked by `scripts/verify-lean.mjs`):

- One module per lesson, namespace `Lumenary.<Module>`. Region ids are `<module_snake>.<name>` (lowercase, digits, `_`, `.`), unique across the project. Exercise regions are `ex.<module_snake>.<name>`, each with `-- @solution Lumenary.<Module>.<name>`.
- **Exactly one declaration per region**, every declaration inside a region, every main-library region with `-- @provenance library|independent|definition`:
  - `library` — the proof applies an existing theorem (core Lean or Mathlib), e.g. `hg.comp hf`. Name the theorem in the docstring.
  - `independent` — proved here from more basic facts (small library lemmas as steps are fine; `rfl`/`decide`/`norm_num`/`simp`-style closing of a genuine computation counts).
  - `definition` — `def`, `structure`, `class`, `instance`, `abbrev`.
  A good lesson usually has both: an independent proof that mirrors the human proof, and (where Mathlib has it) the one-line library version, with the difference explained.
- A teaching docstring on every declaration. Readable, idiomatic code; `calc` blocks that follow the human proof are encouraged. `autoImplicit` is off: declare every variable.
- **No `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` or `set_option … maxHeartbeats` hacks in `Lumenary/`.** Exercises in `LumenaryExercises/` contain `sorry` placeholders only, and must produce no warnings other than "declaration uses `sorry`".
- **Imports.** K–8 lessons use core Lean only (no imports), so a child's family can paste the code into the web editor without Mathlib, and so the elementary library stays self-contained. From Grades 9–12 onwards import the specific Mathlib modules you need (`import Mathlib.Topology.MetricSpace.Basic`, not `import Mathlib`) — find module names by searching `formal/.lake/packages/mathlib/Mathlib/`. Do not import other new lesson modules (each lesson module is self-contained; importing the original seven core modules `Lumenary.Sets` etc. is allowed).
- Prefer Mathlib's definitions to home-made ones at undergraduate level and above, so learners meet the real library; home-made structures are fine for teaching (e.g. a minimal `Category` in a first lesson), but then say how they relate to Mathlib's. Never state a theorem in a vacuous or trivially-true way to make it compile; formalise the actual mathematics, even if only a key lemma or special case — and say precisely which.
- Find lemmas with `exact?`, `apply?`, `simp?` and by grepping Mathlib; check names exist at this Mathlib version.
- What to formalise, by level: K–5 decidable facts about small collections, counts and instructions (`decide`); 6–12 the lesson's main proofs; UG and above at least one substantial result of the lesson (independent where feasible) plus definitions and library facts that connect the lesson to Mathlib. Research lessons formalise a basic definition or lemma of the field and explain honestly how far Mathlib reaches (and what is not yet formalised).

## 7. Computation (Python)

Experiments run unchanged in the learner's browser (Pyodide 0.29.3) and are tested locally with CPython. Model them on the existing files in `compute/experiments/`.

```python
"""One-paragraph docstring: what the experiment shows and what kind of evidence it is."""

import math

EXPERIMENT = {
    "id": "point_set_topology_open_sets",        # = file name
    "title": "Open balls and open sets",         # 5–80 characters
    "evidence": ["exact", "exhaustive-finite"],  # exact | symbolic | numerical | experimental |
                                                 # exhaustive-finite | statistical | counterexample
    "lessons": ["point-set-topology"],           # lesson (and trail) slugs that show it
    "summary": "60–600 characters: what it computes and how far the evidence goes.",
    "packages": [],                              # sorted subset of ["numpy", "sympy"], matching imports
}

def pure_function(...):
    """Small, documented, tested functions."""

def main():
    ...  # prints the report
    print("Epistemic status: ...")              # the last paragraph, always

if __name__ == "__main__":
    main()
```

Rules (checked by `compute/tests/test_experiments_meta.py`): imports only from the standard-library allow-list there (`math`, `fractions`, `itertools`, `random`, `statistics`, `cmath`, `decimal`, `collections`, `functools`, `re`, …) and `numpy`/`sympy`; no I/O, `eval`/`exec`, threads or subprocesses; importing prints nothing; `main()` runs in under 2 seconds, prints 5–40 plain-text lines of at most 80 characters with no trailing spaces, is deterministic (seed any randomness, e.g. `random.Random(2024)`), and ends with a paragraph starting `Epistemic status:` that says exactly what kind of evidence this is and what it does not prove. Every experiment has `compute/tests/test_<id>.py` testing its functions (correct values, edge cases, invariants — at least 4 meaningful tests). Choose experiments that genuinely illuminate: exact computation, counterexample search, numerical approximation with error analysis, simulation versus theory, symbolic verification.

## 8. Exercises

`exercises.json`: `{ "lesson": "<slug>", "exercises": [ … ] }` with **6–10 exercises**, ids `<slug>-<name>` (lowercase, digits, hyphens; unique site-wide). Each has `type`, `difficulty` (`warm-up` | `core` | `stretch`), `mode` (`H` | `F` | `C`), `prompt`, at least two progressive `hints`, and a worked `solution` (Markdown with maths). Types:

- `choice` — `options: [{ id, label, correct, feedback }]`, `multiple: true` for select-all. Every option has specific feedback explaining why it is right or wrong.
- `integer` — `answer`, plus `feedback: [{ match: "<wrong answer>", message }]` for predictable mistakes.
- `set` — `answer: ["…", …]` (order and repetition never matter), `feedback` likewise.
- `python` — `starter` (valid Python that fails the tests), `tests` (asserts, ending with `print('All tests passed!')`), and a `solution` containing a ```` ```python ```` block that passes. Checked by `compute/tests/test_lesson_exercises.py`.

Mix difficulties (warm-up → stretch) and modes. From Grade 6 include at least one `python` exercise; at undergraduate level and above include questions that test proofs and definitions (e.g. "which step of this proof fails?", "which hypothesis is necessary — choose the counterexample"), and `F`-mode questions about formal statements (e.g. which Lean statement formalises the theorem correctly). Feedback is encouraging and specific; never shaming. No scores, streaks or rankings.

## 9. Quality, honesty and fairness

- **Correctness first.** Every definition, statement and proof must be right, with all hypotheses. State theorems at the generality you prove them. Test boundary cases. When you simplify, say so.
- **Evidence is not proof.** Say what kind of evidence each computation is.
- **Research honesty.** Separate established results (with attribution), conjectures, and open problems. Do not guess at the state of the art; when unsure, describe what is classical and well documented.
- **History** must be accurate and attributed only where the attribution is well established; include contributions from many civilisations where the evidence supports it, without inventing any.
- **Geographic fairness.** Examples, names and settings from all inhabited continents and income levels, portrayed with dignity and agency (studying, building, trading, playing, doing science), without stereotypes and without tokenism; local measures and currencies where natural.
- **References** must be real, well-known books or papers (author, year). No URLs unless they are stable official ones.
- **Tone:** clear, warm, encouraging, rigorous; joyful where appropriate; never condescending.

## 10. Checks

While writing, and before declaring a lesson done:

```bash
npm run check:lesson -- <slug> [<slug> …]
```

It runs the structural lesson rules and a full render of the MDX with the real components (unknown tags, crashing widget props and KaTeX errors all fail), builds the lesson's Lean modules and exercise files and checks every cited declaration is sorry-free with `#print axioms`, and runs pytest on the lesson's experiments (including the browser-safety checks) and Python exercises. All checks must pass. The full verification (`npm run verify`, `npm run build`) is run by the coordinator for the whole site.
