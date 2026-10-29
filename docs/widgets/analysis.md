# Analysis widgets

Six interactive explorations for functions, calculus, sequences and series, vector fields, complex numbers and matrices. They are the visual workhorses of the precalculus-to-graduate lessons. Every widget is a client component registered in `src/components/widgets/registry-analysis.ts`; you use one in a lesson by writing its tag in MDX:

| Tag | What it shows |
| --- | --- |
| [`FunctionPlot`](#functionplot) | Graphs y = f(x), parametric curves (x(t), y(t)) and polar curves r(θ), with parameter sliders, points, shading and a trace read-out. |
| [`CalculusLab`](#calculuslab) | Secant → tangent, Riemann sums, Taylor polynomials and the ε–δ game. |
| [`SequenceLab`](#sequencelab) | Sequences with an ε-band, partial sums of series, cobweb diagrams and Fourier partial sums. |
| [`VectorField`](#vectorfield) | Slope fields, phase portraits and vector fields with circulation, flux and index around a loop. |
| [`ComplexPlane`](#complexplane) | Complex arithmetic, n-th roots, conformal maps w = f(z) and winding numbers. |
| [`MatrixTransform`](#matrixtransform) | 2×2 matrices acting on the plane: determinant, orientation, eigenvectors and AB versus BA. |

## Conventions shared by all six

- **Every prop is optional.** Bad values fall back to defaults; an expression that cannot be read shows a short, translated message with a caret under the problem instead of breaking the page.
- **`title` and `subtitle`** override the default (translated) heading. Write them in English; they are not translated automatically.
- **Modes.** Widgets with several modes take `mode` (the one to show) and `modes` (the list of mode tabs to offer). If you give `mode` and no `modes`, only that mode is shown, with no tab bar. If you give neither, all modes are offered as tabs. Example: `mode="riemann" modes={["riemann", "tangent"]}` starts on Riemann sums and offers one other tab.
- **Windows** such as `x`, `y`, `t` and `interval` are `[min, max]` pairs. Reversed pairs are swapped. Entries may be numbers or constant expressions given as strings: `x={["-2*pi", "2*pi"]}`.
- **Numbers as expressions.** Every numeric prop (`a`, `x0`, `exact`, `limit`, matrix entries, complex coordinates…) accepts a number (`a={1.5}`) or a constant expression string (`exact="pi/4"`, `limit="pi^2/6"`, `z={["sqrt(2)/2", "sqrt(2)/2"]}`).
- **Honesty.** Numerical results are labelled as numerical, and finite checks are labelled "evidence, not proof". Keep your lesson text consistent with that.
- **MDX syntax.** Use `prop="text"` for plain strings and `prop={…}` for everything else: numbers, booleans, arrays and objects. Inside `{…}` you write JavaScript, so `params={[{ name: "a", min: 0, max: 2, step: 0.1, value: 1 }]}` and `params={[{"name":"a","min":0,"max":2,"step":0.1,"value":1}]}` both work.

## Expression syntax

Expressions (`fns`, `fn`, `term`, `f`, `g`, …) use a small, safe calculator language. No code is ever executed.

| Feature | Write | Notes |
| --- | --- | --- |
| Numbers | `2`, `0.5`, `.5`, `1e-3`, `6.02E23` | |
| Arithmetic | `+ - * / ^` | `^` is a power and groups to the right: `2^3^2` = 2⁹. `**` also means power. |
| Unary minus | `-x^2` | means −(x²). Write `(-x)^2` for the square of −x. `2^-x` is fine. |
| Multiplication | `2*x`, `a*sin(x)`, `(x+1)*(x-1)` | **Always explicit.** `2x`, `x(x+1)` and `xy` give the message "write 2*x". |
| Factorial | `n!`, `1/n!` | Whole numbers 0–170 only; anything else is undefined. |
| Constants | `pi` (or `π`), `tau` (= 2π), `e` | |
| Functions | `sin cos tan sec csc cot asin acos atan sinh cosh tanh asinh acosh atanh exp ln log log10 log2 sqrt cbrt abs floor ceil round sign` | `log` means the natural logarithm `ln`. One input each: `sin(x)`. |
| Two-input functions | `min(a, b)`, `max(a, b)`, `atan2(y, x)`, `mod(a, b)` | `mod(-1, 3)` = 2 (the result has the sign of b). |
| Typographic symbols | `×`, `·`, `÷`, `−` | Accepted as `*`, `*`, `/`, `-`, so text copied from prose works. |
| Left-hand sides | `y = x^2`, `f(x) = …`, `r = …`, `dy/dx = …`, `x' = …` | The left-hand side and `=` are ignored. |

Which variables you may use depends on the prop: `x` for graphs, `t` for parametric curves, `t` or `theta` (also `θ`) for polar curves, `n` for sequence terms, `x` and `y` for fields. Parameter names you declare in `params` are also allowed. Real arithmetic is used throughout. `sqrt(-1)`, `ln(0)` and `(-8)^(1/3)` are undefined, and the widget leaves a gap in the curve. Use `cbrt(x)` for the real cube root of a negative number.

## FunctionPlot

The general-purpose graphing surface. It draws up to six curves y = f(x) with a legend, or parametric curves (x(t), y(t)), or polar curves r(θ). Optional parameter sliders feed into the expressions, so learners can watch a family of curves move. You can also mark points (whose coordinates may depend on the parameters) and shade the signed area between a curve and the x-axis, with a numerical value. A trace slider, and hovering on graphs, reads off the value of every curve. Poles and jumps are detected, so `tan(x)`, `1/x` and `floor(x)` are drawn without false vertical lines. Learners can open "Edit the functions" to type their own expressions. It suits function families and transformations, polynomials, rational functions, exponentials and logarithms, trigonometry, inverse functions, conic sections and curves, polar coordinates, and area before integration.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `fns` | `string[]` (graph, polar) · `[string, string][]` (parametric) | `["sin(x)", "cos(x)"]` on [−2π, 2π] | The curves, at most 6. Graph: expressions in `x`. Polar: r in terms of `t`, `theta` or `θ`. Parametric: pairs `["x(t)", "y(t)"]`; a flat list `["x1(t)", "y1(t)", "x2(t)", "y2(t)"]` also works. A single string is accepted too. |
| `mode` | `"graph"` \| `"parametric"` \| `"polar"` | `"graph"` | What the expressions mean. |
| `x` | `[min, max]` | `[-5, 5]` (graph); fitted to the curve (parametric, polar) | Horizontal window. |
| `y` | `[min, max]` | fitted to the curves at the initial parameter values | Vertical window. Give it whenever a curve has poles or grows fast, so the picture is stable. |
| `t` | `[min, max]` | `[0, 2*pi]` | Parameter range for parametric and polar curves. |
| `params` | `{ name, min, max, step, value, label? }[]` | none | Sliders, at most 8. Names must be new identifiers: not `x`, `t`, `theta`, `pi`, `e` or a function name. `label` replaces the name above the slider. |
| `labels` | `string[]` | the expression, prettified (`y = x² − 1`) | Legend label for each curve, in order. |
| `points` | `[x, y]`, `[x, y, "label"]` or `{ x, y, label }` items | none | Marked points, at most 24. Coordinates are numbers or expressions in the parameters, e.g. `["a", "a^2", "P"]`. |
| `shade` | `number` | none | Index (0-based) of a graph-mode curve whose area to the x-axis is shaded. Above the axis is gold; below the axis is hatched. |
| `shadeRange` | `[a, b]` | the whole window | Limits of the shading. When given, the read-out shows the signed area ∫ₐᵇ f(x) dx, computed numerically. |
| `aspect` | `"equal"` | `"equal"` for parametric and polar, otherwise off | Same unit length on both axes, for geometry pictures (circles look round). |
| `editable` | `boolean` | `true` | Show the "Edit the functions" button. |
| `xLabel`, `yLabel` | `string` | `"x"`, `"y"` | Axis names. |
| `title`, `subtitle` | `string` | translated defaults per mode | Heading overrides. |

Tick labels switch to multiples of π automatically when the `x` window is given in multiples of π (for example `["-2*pi", "2*pi"]`).

**Transformations of a parabola (vertex form):**

```mdx
<FunctionPlot
  fns={["a*(x - h)^2 + k", "x^2"]}
  labels={["y = a(x − h)² + k", "y = x²"]}
  params={[
    { name: "a", min: -3, max: 3, step: 0.1, value: 1 },
    { name: "h", min: -4, max: 4, step: 0.5, value: 1 },
    { name: "k", min: -4, max: 4, step: 0.5, value: -2 },
  ]}
  points={[["h", "k", "vertex"]]}
  x={[-6, 6]}
  y={[-6, 6]}
/>
```

**Trigonometric graphs, with π on the axis:**

```mdx
<FunctionPlot fns={["sin(x)", "sin(2*x)", "2*sin(x)"]} labels={["sin x", "sin 2x", "2 sin x"]} x={["-2*pi", "2*pi"]} y={[-2.5, 2.5]} />
```

**Area under a curve, before integrals:**

```mdx
<FunctionPlot fns={["x^2"]} x={[-0.5, 2.5]} y={[-0.5, 4.5]} shade={0} shadeRange={[0, 2]} points={[[2, 4, "(2, 4)"]]} />
```

**Lissajous figures and a polar rose:**

```mdx
<FunctionPlot
  mode="parametric"
  fns={[["sin(a*t)", "sin(b*t)"]]}
  params={[
    { name: "a", min: 1, max: 6, step: 1, value: 3 },
    { name: "b", min: 1, max: 6, step: 1, value: 2 },
  ]}
  t={[0, "2*pi"]}
  x={[-1.2, 1.2]}
  y={[-1.2, 1.2]}
/>

<FunctionPlot mode="polar" fns={["cos(k*theta)"]} params={[{ name: "k", min: 1, max: 7, step: 1, value: 3 }]} x={[-1.2, 1.2]} y={[-1.2, 1.2]} />
```

## CalculusLab

Four classic pictures of single-variable calculus in one widget. **Tangent** draws the secant through P = (x₀, f(x₀)) and Q = (x₀ + h, f(x₀ + h)). The learner shrinks h on a logarithmic slider (or presses "Let h shrink to 0") and watches the secant turn into the tangent. A table of difference quotients for h = 1, 0.1, 0.01, 0.001 sits beside it. The tangent slope is a clearly labelled numerical estimate. At corners (`abs(x)` at 0), jumps, vertical tangents and points outside the domain, the widget explains why there is no derivative instead of drawing a line. **Riemann** shows left, right, midpoint and trapezoid sums with 1–200 strips. Strips below the axis are hatched and count negatively. The sum is compared with the exact integral (when you give `exact`) or with a labelled numerical reference, alongside a table of all four rules and their errors. **Taylor** plots the Maclaurin polynomials of sin, cos, eˣ, ln(1 + x), 1/(1 − x) and arctan up to degree 20. It shows each polynomial as a formula and marks the interval of convergence, open or closed at each end, with an honest sentence about what happens outside it. **ε–δ** is the limit game for lim₍ₓ→ₐ₎ f(x) = L: the learner picks ε (1 … 0.01) and δ and sees the ε-band, the δ-window and, in dashed red, the parts of the graph that escape. The verdict comes from 2,000+ sample points and says so ("evidence, not a proof"). The learner can reveal the largest working δ (a numerical search), zoom in, change L, or switch to a function with a jump where no δ works. The widget suits lessons on the derivative as a limit, differentiability, definite integrals and numerical integration, Taylor series and radius of convergence, and the formal definition of a limit or of continuity.

Without `mode`, all four tabs are shown. With `mode`, only that mode appears (no tab bar), unless `modes` lists the tabs to offer. The learner can edit f ("Change the function"; Riemann also lets them edit a and b, and ε–δ lets them edit a). Every numeric prop accepts a number or a constant expression string such as `"pi/4"` or `"sqrt(2)"`.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `mode` | `"tangent"` \| `"riemann"` \| `"taylor"` \| `"epsilon-delta"` | all four as tabs | Which exploration to show. |
| `modes` | array of the mode names | `[mode]`, or all four | Which mode tabs to offer (the first is shown unless `mode` picks another). |
| `fn` | string (expression in `x`) | tangent `"x^3/3 - x"`, riemann `"sin(x)"`, ε–δ `"x^2"` | The function f. A leading `f(x) =` or `y =` is allowed. Ignored in taylor mode. |
| `x0` | number \| string | `1.5` | Tangent: the point x₀ (clamped into the x-window). |
| `interval` | `[a, b]` | `[0, "3*pi/2"]` | Riemann: the interval of integration. |
| `exact` | number \| string | `1` for the default sin(x) on [0, 3π/2]; otherwise none | Riemann: the exact value of ∫ₐᵇ f(x) dx, e.g. `"8/3"`. Without it (or once the learner edits f, a or b), a numerical reference (adaptive Simpson) is shown and labelled. |
| `n` | integer 1–200 | `6` | Riemann: initial number of strips. |
| `method` | `"left"` \| `"right"` \| `"midpoint"` \| `"trapezoid"` | `"left"` | Riemann: initial rule. |
| `preset` | `"sin"` \| `"cos"` \| `"exp"` \| `"ln1p"` \| `"geometric"` \| `"atan"`, or `"jump"` | `"sin"` | Taylor: the function (`ln1p` = ln(1 + x), `geometric` = 1/(1 − x)). In ε–δ mode, `"jump"` starts with f(x) = x/2 + sign(x) at a = 0, where no δ works for ε < 1. Without `mode`, a Taylor preset opens the Taylor tab. |
| `degree` | integer 0–20 | `3` | Taylor: initial degree n of Tₙ. |
| `a` | number \| string | `1` | ε–δ: the point a. |
| `L` | number \| string | f(a) (rounded), else 0 | ε–δ: the claimed limit. The learner can move it to see what happens when L is wrong. |
| `epsilon` | number | `0.5` | ε–δ: the initial ε (added to the choices 1, 0.5, 0.2, 0.1, 0.05, 0.01 if it is not one of them). |
| `x`, `y` | `[min, max]` | per mode (auto y from the curve) | Viewing windows. Taylor has a sensible window for each preset; ε–δ ignores them for the jump example. |
| `title`, `subtitle` | string | translated per mode | Override the heading (write them in the lesson's language). |

Expressions use `x`, numbers, `+ - * / ^` (with `^` right-associative and `-x^2 = -(x^2)`), parentheses, `pi`, `e`, and `sin cos tan asin acos atan sinh cosh tanh exp ln log log10 sqrt abs floor ceil sign min max` (plus `sec csc cot cbrt round mod`). Multiplication must be explicit: `2*x`, not `2x`.

The derivative as a limit of secant slopes, at a point where students can predict the answer:

```mdx
<CalculusLab mode="tangent" fn="sin(x)" x0="pi/4" x={["-pi", "pi"]} />
```

Differentiability fails at a corner (the widget explains why instead of drawing a tangent):

```mdx
<CalculusLab mode="tangent" fn="abs(x - 1)" x0={1} title="Where is there no tangent line?" />
```

Riemann sums for x² on [0, 2], compared with the exact value 8/3:

```mdx
<CalculusLab mode="riemann" fn="x^2" interval={[0, 2]} exact="8/3" n={8} method="midpoint" />
```

Taylor series with a finite interval of convergence, then the ε–δ definition of a limit (including a jump where the limit fails):

```mdx
<CalculusLab mode="taylor" preset="ln1p" degree={7} />

<CalculusLab mode="epsilon-delta" fn="x^2" a={1} L={1} epsilon={0.1} />

<CalculusLab mode="epsilon-delta" preset="jump" epsilon={0.5} />
```

## SequenceLab

A lab for infinite processes, with four modes. **sequence** plots the terms aₙ and tests a candidate limit L with an ε-band: it reports the first index N from which every checked term stays inside the band. **series** plots the partial sums Sₙ (optionally with the terms as bars, and an optional logarithmic n-axis) against a known sum. It recognises the harmonic series and explains its slow divergence, and it applies the term test when the terms clearly do not shrink. **cobweb** iterates a map xₖ₊₁ = f(xₖ) (the logistic map by default) and shows a cobweb diagram, a time series, the fixed points with their stability, and a numerical verdict on the orbit (fixed point, cycle of period p, slow convergence, escape, or no pattern). **fourier** builds square, sawtooth and triangle waves from sine waves and measures the Gibbs overshoot. It suits lessons on limits of sequences and the ε–N definition, convergence tests and famous series, fixed-point iteration, the logistic map and the road to chaos, and Fourier series. Every finite computation is labelled as evidence, not proof.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `mode` | `"sequence"` \| `"series"` \| `"cobweb"` \| `"fourier"` | `"sequence"` | Which view to open. |
| `modes` | array of mode names | — | Mode tabs to offer. If omitted: only `mode` when `mode` is given (no tab bar), otherwise all four. |
| `term` | string, expression in `n` | sequence `"1 + (-1)^n/n"`, series `"1/n^2"` | General term aₙ for n = 1, 2, 3, … (sequence and series modes). |
| `limit` | number or string | sequence `"1"`, series `"pi^2/6"`, but only when `term` is omitted; otherwise none | Sequence: the candidate limit L for the ε-band (the reader can switch it on or off and edit it). Series: the known sum, drawn as a dashed line with the remaining gap. Strings such as `"e"`, `"ln(2)"`, `"pi^2/6"` are allowed. |
| `epsilon` | number | `0.1` | Initial ε in sequence mode (the slider is logarithmic). |
| `fn` | string, expression in `x` and the parameters | `"r*x*(1-x)"` | The map f in cobweb mode. |
| `x0` | number or string | 20 % into the window (0.2 for [0, 1]) | Starting value in cobweb mode. |
| `params` | array of `{"name", "min", "max", "step", "value", "label"?}` | cobweb with the default `fn`: `[{"name":"r","min":0,"max":4,"step":0.01,"value":2.8}]`; otherwise none | Parameter sliders. Their names can be used in `term` and `fn`. If you give `params` in cobweb mode without `fn`, the logistic map `r*x*(1-x)` is still used, so name your parameter `r`. |
| `wave` | `"square"` \| `"sawtooth"` \| `"triangle"` | `"square"` | Initial wave in fourier mode. |
| `N` | number | sequence 30 (1–200), series 100 (1–1000), cobweb 30 (1–200), fourier 5 (1–100) | Initial number of terms, partial sums, iterations or Fourier terms (non-zero terms). |
| `x`, `y` | `[min, max]` | sequence/series: automatic; cobweb `[0, 1]` with `y` = `x`; fourier `x` = `[-2*pi, 2*pi]`, `y` depends on the wave | Viewing windows. Ends may be expressions such as `"-2*pi"`. In series mode, `x` is ignored while the logarithmic axis is on. |
| `editable` | boolean | `true` | When `false`, the term or map is shown as a fixed formula instead of an input, and the series examples are hidden. |
| `title`, `subtitle` | string | translated default per mode | Override the heading and the line under it. |

Expressions use the same syntax as `FunctionPlot`. The variable is `n` in `term` and `x` in `fn`, and multiplication must be explicit (`2*n`, not `2n`). Powers `^`, the factorial `n!`, `pi`, `e` and functions such as `sqrt`, `ln`, `exp`, `sin`, `cos` are available. Write alternating signs as `(-1)^n`. Fourier conventions: square = sign(sin x), sawtooth = x on (−π, π), triangle = (2/π)·arcsin(sin x), all with period 2π. `N` counts the non-zero terms of the series.

```mdx
{/* The ε–N definition: (1 + 1/n)^n → e */}
<SequenceLab mode="sequence" term="(1 + 1/n)^n" limit="e" epsilon={0.05} N={60} />
```

```mdx
{/* p-series: move p across 1 and watch the partial sums; then compare with the harmonic series */}
<SequenceLab mode="series" term="1/n^p" params={[{"name":"p","min":0.5,"max":3,"step":0.1,"value":2}]} N={300} />
<SequenceLab mode="series" term="1/n" N={1000} />
```

```mdx
{/* Period doubling in the logistic map, and the fixed point of cos */}
<SequenceLab mode="cobweb" params={[{"name":"r","min":2.5,"max":4,"step":0.01,"value":3.2}]} x0={0.2} N={60} />
<SequenceLab mode="cobweb" fn="cos(x)" x={[0, 1.5]} x0={0.1} N={40} />
```

```mdx
{/* Fourier series and the Gibbs phenomenon */}
<SequenceLab mode="fourier" wave="square" N={10} />
```

## VectorField

Three pictures of planar vector fields, for differential equations, dynamical systems and vector calculus. **Slope fields** show dy/dx = f(x, y) as short segments. The learner clicks (or types a start point) to draw the solution y(x) through it in both directions; a solution honestly stops where its tangent turns vertical (it is no longer a function y(x)), where f is undefined, or where it leaves the picture. **Phase portraits** show a system x′ = f(x, y), y′ = g(x, y) as arrows whose darkness and length show speed. Trajectories start from clicked points: forward in time solid, with arrowheads; backward in time dashed. Linear systems get their matrix, trace, determinant, eigenvalues and the classification of the equilibrium (saddle, centre, spiral or node, source or sink) with a trace–determinant diagram. Nonlinear systems get their equilibria, found numerically and classified by linearisation, with a warning that a linear centre is inconclusive. **Loop in a field** lets the learner drag a circular loop through F = (P, Q). It shows the circulation ∮F·dr and the flux ∮F·n ds next to ∬curl F dA and ∬div F dA, which agree when Green's theorem applies and visibly disagree when F is singular inside the loop. It also shows the **index** of F around the loop (how many times the arrow turns as you walk round, with a compass and a "walk" slider); a non-zero index forces a zero inside. All curves and integrals are numerical (RK4, quadrature), and the widget says so. Suits lessons on first-order ODEs and existence/uniqueness, logistic growth, linear systems and eigenvalues, the pendulum and predator–prey models, limit cycles (van der Pol), and line integrals, Green's theorem, divergence and curl, and degree/index theory.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `mode` | `"slope"` \| `"phase"` \| `"field"` | none (all three offered as tabs) | The picture to show. When given (and `modes` is not), only that mode is shown, with no tab bar. |
| `modes` | string[] | all three when `mode` is omitted | Which mode tabs to offer, e.g. `{["phase", "field"]}`. |
| `f` | string | from the preset | Slope mode: the right-hand side of dy/dx = f(x, y). Phase mode: x′ = f(x, y). Field mode: the first component P(x, y). |
| `g` | string | from the preset (`"0"` if only `f` is given) | Phase mode: y′ = g(x, y). Field mode: the second component Q(x, y). Ignored in slope mode. |
| `preset` | string | `"linear"` / `"spiralSink"` / `"rotation"` | A named example (see below). Ignored when `f` or `g` is given. If `mode` is omitted, the preset decides which mode the widget opens in. |
| `x`, `y` | `[min, max]` | the preset's window (else `[-4, 4]`) | The window. Numbers or constant expressions, e.g. `x={["-2*pi", "2*pi"]}`. Units are equal on both axes, so one window may be widened to fill the plot. |
| `points` | `[[x0, y0], …]` | the preset's start points (none for custom `f`) | Start points whose solution curves/trajectories are drawn at once (up to 10). Slope and phase modes only. |
| `title`, `subtitle` | string | translated default per mode | Override the heading and the line under it. |

`f`, `g`, `preset`, `x`, `y` and `points` apply to the mode the widget **opens** in; the other tabs start from their default examples.

**Presets.** Slope: `linear` (x − y), `logistic` (y(1 − y)), `circles` (−x/y), `blowup` (x² + y²). Phase: `center` (or `centre`), `saddle`, `spiralSource`, `spiralSink`, `node`, `lotkaVolterra` (predator–prey), `pendulum` (x′ = y, y′ = −sin x), `vanDerPol` (limit cycle). Field: `rotation` (−y, x), `source` (x, y), `sink` (−x, −y), `saddleField` (x, −y; index −1), `dipole` (x² − y², 2xy; index 2), `uniform` (1, 0), `shear` (y, 0).

**Expression syntax.** Use the variables `x` and `y`, numbers, `+ - * / ^`, parentheses, `pi`, `e` and functions such as `sin cos tan exp ln sqrt abs min max`. Multiplication must be explicit (`2*x`, not `2x`). A leading left-hand side such as `dy/dx =`, `x' =`, `y' =` is allowed and ignored. Learners can edit the equations with the "Edit the equations" button; mistakes are shown inline with the position of the problem.

```mdx
<VectorField mode="slope" preset="logistic" />
```

```mdx
<VectorField
  mode="slope"
  f="x^2 - y"
  x={[-3, 3]}
  y={[-3, 3]}
  points={[[0, 0], [-2, 1], [0, 2.5]]}
  title="Solutions of y′ = x² − y"
/>
```

```mdx
<VectorField mode="phase" f="x - 2*y" g="3*x - 4*y" points={[[3, 1], [-2, 3], [1, -3]]} title="A stable node: eigenvalues −1 and −2" />
```

```mdx
<VectorField mode="phase" preset="pendulum" title="The pendulum’s phase plane" />
```

```mdx
<VectorField mode="field" f="-y/(x^2 + y^2)" g="x/(x^2 + y^2)" title="A vortex: circulation without curl" />
```

```mdx
<VectorField modes={["phase", "field"]} preset="saddle" />
```

## ComplexPlane

The complex plane as a place to think geometrically. Four explorations: **arithmetic** (drag z and w; addition is a parallelogram, multiplication multiplies lengths and adds angles, division divides lengths and subtracts angles, the conjugate is a reflection), **roots** (the n solutions of wⁿ = c form a regular n-gon on the circle of radius |c|^(1/n); roots of unity when c = 1), **map** (a square or polar grid in the z-plane and its image under w = f(z) side by side, with a draggable probe whose little right-angled cross stays right-angled wherever f′(z₀) ≠ 0, so conformality and its failure at critical points and poles are visible) and **winding** (a closed curve and a draggable point p; the winding number is counted both from the turning of the arrow from p to the curve and from signed crossings of a ray, and regions can be shaded by winding number). Suits lessons on complex numbers and their arithmetic, polar form and De Moivre, roots of unity and cyclotomic polynomials, the fundamental theorem of algebra, complex functions and conformal maps, Möbius transformations, the argument principle, Cauchy's theorem and residues, and the degree of maps of the circle in topology. Every point can also be moved with the keyboard (Tab to it, then the arrow keys; Shift for small steps) or typed into the Re/Im fields, which accept expressions such as `sqrt(2)/2`.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `mode` | `"arithmetic"` \| `"roots"` \| `"map"` \| `"winding"` | tabs for all four | Which exploration to show. If given (and `modes` is not), only that mode is shown, without a tab bar. |
| `modes` | array of mode names | all four, or just `mode` | Which mode tabs to offer, e.g. `modes={["arithmetic", "roots"]}`. Unknown names are ignored. |
| `z` | `[re, im]` (numbers or constant expressions) or a real number | arithmetic: `[1.5, 0.5]`; roots: `[1, 0]`; map: the preset's own probe; winding: `[0, 0]` | Arithmetic: the first number z. Roots: the number c whose roots are shown. Map: the starting probe point z₀. Winding: the starting point p. (For map and winding, `z` is used only when that mode is chosen with `mode`.) |
| `w` | `[re, im]` | `[0.5, 1]` | Arithmetic: the second number w. |
| `op` | `"sum"` \| `"product"` \| `"quotient"` \| `"conjugate"` | `"sum"` | Arithmetic: the operation selected at the start (the reader can switch). |
| `n` | integer 2–12 | `5` | Roots: how many roots (the reader can change it with a slider). |
| `map` | `"z^2"` \| `"z^3"` \| `"1/z"` \| `"exp"` \| `"mobius"` \| `"joukowski"` | `"z^2"` | Map: the starting function. `exp` is eᶻ, `mobius` is (z − 1)/(z + 1), `joukowski` is z + 1/z. Aliases such as `"e^z"`, `"z+1/z"`, `"inverse"` also work. |
| `grid` | `"cartesian"` \| `"polar"` | depends on the map (polar for `z^3` and `joukowski`) | Map: square grid (horizontal and vertical lines) or polar grid (circles and rays). |
| `curve` | `"circle"` \| `"ellipse"` \| `"figure8"` \| `"doubleLoop"` \| `"square"` \| `"cardioid"` | `"doubleLoop"` | Winding: the starting closed curve. `figure8` winds −1 around points in its right lobe and +1 in its left; `doubleLoop` (the limaçon r = 1 + 2 cos θ) winds twice around points in its inner loop. |
| `range` | number 1–20 | `3` | Half-width of the view in arithmetic, roots and winding modes (the map mode chooses its own windows per function). |
| `title`, `subtitle` | string | translated defaults per mode | Override the heading text. |

Notes: the probe in map mode reports f(z₀), f′(z₀), the local scale factor |f′(z₀)|, the local rotation arg f′(z₀) and the oriented angle between the images of the two small legs (90° where f is conformal; at a critical point of order k it is k·90°, e.g. 180° for z² at 0). Winding numbers are computed on the curve sampled at 720 points, and the widget says so.

```mdx
<ComplexPlane mode="arithmetic" op="product" z={[1.5, 0.5]} w={["sqrt(2)/2", "sqrt(2)/2"]} />
```

```mdx
<ComplexPlane mode="roots" z={[1, 0]} n={6} title="The sixth roots of unity" />
```

```mdx
<ComplexPlane mode="map" map="joukowski" grid="polar" />
```

```mdx
<ComplexPlane mode="winding" curve="figure8" z={[1.2, 0.2]} subtitle="Which way does the curve go around p? Move p into the other lobe." />
```

## MatrixTransform

A 2×2 real matrix acting on the plane. The widget shows four things:

- the image of the whole grid;
- the unit square becoming a parallelogram, whose area is |det A|;
- a small asymmetric flag inside it, so reflections are visible;
- a little arc from e₁ to e₂ that turns clockwise when orientation is reversed (det A < 0).

Learners edit the entries (number boxes that accept expressions like `sqrt(3)/2`, plus sliders) or pick a preset: identity, rotation, reflection, shear, scaling, projection or a singular matrix. Presets with a parameter get their own slider (angle, shear factor, stretch). A "From the identity I to A" slider and a Play button morph the picture from I to A. The read-out explains several things:

- the columns of A are the images of e₁ and e₂;
- what det A says about area and orientation, and that det A = 0 means no inverse;
- the real eigenvalues and eigenvectors, drawn as dashed invariant lines;
- when there are none: repeated eigenvalues, a defective matrix with only one invariant line, or complex eigenvalues ("A is a rotation by 30°").

The **compose** mode shows "first A, then B" (the matrix BA) beside "first B, then A" (AB), with the intermediate step dashed, and says whether they agree. It suits introductory linear algebra, linear maps and matrices, determinants, eigenvalues and eigenvectors, matrix multiplication, geometric transformations, and the classification of linear dynamical systems.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `matrix` | `[[a, b], [c, d]]` or `[a, b, c, d]` | `[[1, 1], [0.5, 1.5]]` (single); rotation by 90° (compose) | The matrix A (rows). Entries are numbers or constant expressions such as `"cos(pi/6)"`, clamped to ±100. |
| `matrix2` | same | `[[1, 0], [0, -1]]` (reflection in the x-axis) | The matrix B, used in compose mode. |
| `mode` | `"single"` \| `"compose"` | none (both tabs) | Which view to show; see "Modes" above. |
| `modes` | array of the two | see "Modes" | Which tabs to offer. |
| `showEigen` | `boolean` | `true` | Draw invariant lines and explain eigenvalues. |
| `showDet` | `boolean` | `true` | Show the determinant, area and orientation read-out. |
| `presets` | array of `"identity"`, `"rotation"`, `"reflection"`, `"shear"`, `"scale"`, `"projection"`, `"singular"` | all seven | Preset buttons to offer, in this order. Use `[]` for none. |
| `range` | `number` | `3` | Half-width of the visible square window (1.5 to 12). Use a larger value for matrices with large entries. |
| `title`, `subtitle` | `string` | translated defaults per mode | Heading overrides. |

The presets are as follows:

- **Rotation:** rotation by θ, with a slider from −180° to 180° (default 45°).
- **Reflection:** reflection in the line through 0 at angle φ (default 45°, the line y = x).
- **Shear:** `[[1, k], [0, 1]]`, default k = 1.
- **Scaling:** `[[sx, 0], [0, sy]]`, default sx = 2 and sy = 0.5.
- **Projection:** orthogonal projection onto the line at angle φ (default 30°).
- **Singular:** `[[1, 2], [0.5, 1]]`.

In compose mode, a menu under each matrix sets it to a preset: rotation by 90°, reflection in the x-axis, shear with k = 1, and so on.

**First look at linear maps:**

```mdx
<MatrixTransform />
```

**A reflection reverses orientation (det = −1):**

```mdx
<MatrixTransform matrix={[[0, 1], [1, 0]]} mode="single" presets={["reflection", "rotation"]} title="Mirror images" subtitle="Watch the flag and the little arc: which way do they turn?" />
```

**Eigenvectors as invariant lines; a rotation has none:**

```mdx
<MatrixTransform matrix={[[2, 1], [1, 2]]} mode="single" presets={["shear", "rotation", "scale", "projection"]} />
```

**Matrix multiplication is composition, and order matters:**

```mdx
<MatrixTransform mode="compose" matrix={[[1, 1], [0, 1]]} matrix2={[["cos(pi/2)", "-sin(pi/2)"], ["sin(pi/2)", "cos(pi/2)"]]} />
```
