# Shape, measurement, pattern and data widgets (K–8)

Seven generic, configurable explorations for geometry, measurement, patterns, data and chance. Tag names are registered in `src/components/widgets/registry-shape-data.ts`, so you can use them directly in lesson MDX.

**Rules that apply to every widget here**

- Every prop is optional. With no props you get a sensible, complete activity.
- MDX syntax: strings as `prop="…"`; numbers, booleans, arrays and objects as `prop={…}` (e.g. `width={6}`, `showMean={true}`, `shapes={["square", "kite"]}`, `data={[{ label: "Cats", value: 5 }]}`).
- `title` and `subtitle` replace the default (translated) heading. Write them in English; everything else the widget says is translated into all site languages. Text you pass in (titles, data labels, sector labels) is shown exactly as written.
- Bad input never breaks a page: numbers are rounded and clamped to the ranges below, unknown ids and malformed entries are ignored, and the default is used if nothing valid remains.
- What learners do (drawing, spinning, answers) is not saved. Spinner results come from a seeded random number generator, so a page always starts the same way.

---

## ShapeExplorer

2D shapes. A gallery of named shapes in which learners switch features on and off: sides (with tick marks for equal sides and arrowheads for parallel sides on quadrilaterals), vertices (lettered A, B, C…), angle measures (right angles marked with a square), lines of symmetry, rotational symmetry (a "Turn" button rotates the shape over its dashed outline, with a gold dot to track one vertex) and diagonals. A facts panel lists the counts for every feature that is switched on, plus a short property note (including both the inclusive and exclusive definitions of a trapezium/trapezoid). A second mode, **Angles of a polygon**, triangulates a regular or irregular convex n-gon (n = 3–12) from one vertex and derives the interior angle sum (n − 2) × 180°. Suits: naming and sorting 2D shapes (K–2), properties of triangles and quadrilaterals (3–5), symmetry (3–5), the quadrilateral hierarchy, angle sums in triangles and polygons (6–8).

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `shapes` | string[] | 15 shapes (see below) | Which shapes appear in the gallery, in this order. The first is selected. |
| `show` | string[] | `["sides", "vertices"]` | Features switched on at the start: any of `"sides"`, `"vertices"`, `"angles"`, `"symmetry"`, `"rotation"`, `"diagonals"`. `show={[]}` starts with everything off. In polygon mode, angle arcs are on unless `show` is given without `"angles"` (arcs are labelled up to n = 5; the panel always gives the values). |
| `mode` | `"gallery"` \| `"polygon"` | `"gallery"` | Which mode opens first (learners can switch). |
| `n` | number (3–12) | `6` | Starting number of sides in polygon mode. |
| `title`, `subtitle` | string | translated | Heading override. |

**Shape ids.** Every angle in the named shapes is a whole number of degrees, so the labels are exact.

| Id | Shape (angles) |
| --- | --- |
| `equilateral` | equilateral triangle (60°, 60°, 60°) |
| `isosceles` | isosceles triangle (70°, 70°, 40°) |
| `scalene` | scalene, acute triangle (50°, 70°, 60°) |
| `right` | right-angled scalene triangle (90°, 30°, 60°) |
| `right-isosceles` | right isosceles triangle (90°, 45°, 45°) |
| `obtuse` | obtuse triangle (25°, 35°, 120°) |
| `square`, `rectangle` | square; 1.7 : 1 rectangle |
| `rhombus` | rhombus (60°, 120°) |
| `parallelogram` | parallelogram (70°, 110°, sides 1.5 : 1) |
| `trapezoid` (alias `trapezium`) | trapezium with no equal sides (60°, 75°, 105°, 120°) |
| `isosceles-trapezoid` (alias `isosceles-trapezium`) | isosceles trapezium (65°, 65°, 115°, 115°) |
| `kite` | kite (50°, 100°, 110°, 100°) |
| `pentagon`, `hexagon`, `heptagon`, `octagon`, `nonagon`, `decagon` | regular polygons |
| `regular-N` with N = 3–12 | regular N-gon (`regular-3` = `equilateral`, `regular-4` = `square`; non-whole angles such as 900°/7 are shown as ≈128.6°) |
| `circle` | circle (no vertices; infinitely many lines of symmetry; any turn fits) |

Default gallery: `equilateral, isosceles, scalene, right, obtuse, square, rectangle, rhombus, parallelogram, trapezoid, kite, pentagon, hexagon, octagon, circle`.

```mdx
<ShapeExplorer />

<ShapeExplorer shapes={["square", "rectangle", "rhombus", "parallelogram", "trapezoid", "kite"]} show={["sides", "angles"]} title="Which quadrilateral is which?" />

<ShapeExplorer shapes={["equilateral", "isosceles", "scalene", "square", "rectangle", "hexagon", "circle"]} show={["symmetry"]} subtitle="Count the lines of symmetry, then turn on rotation." />

<ShapeExplorer mode="polygon" n={5} show={["angles"]} />
```

---

## AreaGrid

Area and perimeter on a square grid, in four modes. **Rectangle**: width × height sliders; the rectangle is drawn as rows of unit squares (optionally numbered) so area = rows × squares per row; "Trace the perimeter" animates the boundary and shows w + h + w + h = 2 × (w + h). **Draw a shape**: click or tap squares on a 10 × 7 board (mouse users can drag; arrow keys move between squares, Space/Enter toggles); area and perimeter update live, separate pieces are reported, and "Try an example" cycles through three shapes of area 12 with perimeters 14, 16 and 26. "Record this shape" builds a comparison table, so learners can see equal areas with different perimeters. **Split a rectangle**: a × (b + c) drawn as two coloured rectangles (they can be pulled apart) to show a × (b + c) = a × b + a × c, the distributive law. **Triangle**: a triangle inside its bounding rectangle; "Turn the outside pieces" rotates each outside piece half a turn onto an inside piece, showing area = ½ × base × height, and sliding the top corner shows the area does not change. Suits: area by counting and arrays (2–3), area and perimeter (3–4), distributive property (3–5), area of triangles (5–6).

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `mode` | `"rectangle"` \| `"draw"` \| `"split"` \| `"triangle"` | first offered mode | Mode shown first. |
| `modes` | string[] | all four | Which mode buttons to offer. With a single mode, no mode buttons are shown. |
| `width` | number | see table | Starting width (rectangle), total width b + c (split), or base (triangle). |
| `height` | number | see table | Starting height (rectangle, triangle) or number of rows a (split). |
| `split` | number (1–8) | `width − 2` | Split mode only: the first part b. The second part is c = width − b (at least 1, at most 8). |
| `unit` | string | — | A length unit such as `"cm"` or `"m"`: area is then shown as "24 cm²" and perimeter as "20 cm" instead of "square units"/"units". |
| `title`, `subtitle` | string | translated | Heading override. |

| Mode | `width` | `height` |
| --- | --- | --- |
| rectangle | 1–12, default 5 | 1–10, default 3 |
| split | b + c, 2–16, default 6 | rows a, 1–8, default 3 |
| triangle | base 2–10, default 6 | height 1–8, default 4 |
| draw | ignored (board is 10 × 7) | ignored |

```mdx
<AreaGrid width={6} height={4} modes={["rectangle"]} title="Rows times columns" />

<AreaGrid mode="draw" modes={["draw"]} subtitle="Make three different shapes with an area of 12 squares. Record each one." />

<AreaGrid mode="split" modes={["split"]} width={10} height={7} split={7} title="7 × 10 = 7 × 7 + 7 × 3" />

<AreaGrid mode="triangle" width={8} height={5} unit="cm" modes={["rectangle", "triangle"]} />
```

---

## AnalogClock

Reading an analogue clock. Learners drag the long minute hand (or the short hour hand, or click the face), use −/+ buttons, or focus a hand and use the arrow keys; the hour hand always moves consistently (0.5° per minute) and the hour carries when the minute hand passes 12, forwards or backwards. The panel shows the time on the 12-hour clock (with a.m./p.m.), on the 24-hour clock, and in words ("quarter to 4", "20 minutes past 5"). Digital time can be hidden for practice, and minute numbers (0, 5, …, 55) can be shown around the edge. **Elapsed time** mode keeps a faint copy of the start time's hands, shades the minute hand's sweep, and shows the count-on strategy (to the next o'clock, then whole hours, then the minutes left over) as a chain of jumps, plus the duration in hours and minutes. Suits: o'clock and half past (K–1), quarter past/to and five-minute intervals (2), to the minute and a.m./p.m. (3), 24-hour clock and elapsed time (3–5).

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `hours` | number (0–23) | `3` | Starting hour, on the 24-hour clock (`15` = 3 p.m.). In elapsed mode, the start time. |
| `minutes` | number (0–59) | `0` | Starting minutes. |
| `mode` | `"read"` \| `"elapsed"` | `"read"` | Mode shown first (learners can switch). |
| `step` | number (1–60) | `5` | Minutes per −/+ button press (and per PageUp/PageDown on the focused minute hand; arrow keys move it 1 minute). Use `1` for "to the minute", `15` for quarter hours, `30` for half hours. |
| `elapsed` | number (0–720) | `35` | Elapsed mode: starting time passed, in minutes. |
| `digital` | boolean | `true` | Show the digital time and words at the start. `digital={false}` hides them until the learner presses "Show digital time". |
| `title`, `subtitle` | string | translated | Heading override. |

```mdx
<AnalogClock hours={3} minutes={0} step={30} title="O'clock and half past" />

<AnalogClock hours={9} minutes={45} step={5} digital={false} subtitle="What time does the clock show? Check with the digital time." />

<AnalogClock mode="elapsed" hours={14} minutes={45} elapsed={50} step={5} title="How long is the film?" />

<AnalogClock hours={18} minutes={20} step={1} />
```

---

## RulerMeasure

Measuring length. In the **centimetre ruler** view an object (key 5 cm, leaf 7 cm, crayon 9 cm, feather 11 cm, spoon 13 cm, pencil 15 cm; all whole centimetres so readings are exact) sits above a 0–20 cm ruler whose end is deliberately *not* at 0. Learners slide it (drag, buttons, or arrow keys when focused), type a length and press Check. Feedback names the two classic mistakes: reading the end mark when the object does not start at 0 ("it starts at 3, so its length is 18 − 3 = 15 cm"), and counting marks instead of spaces. "Show the readings" reveals the start and end numbers and the subtraction; "Start at 0" lines the object up. In the **paper clips and hand spans** view the same object is measured with small clips (3 cm), large clips (5 cm), a child's hand spans (12 cm) and an adult's hand spans (18 cm); results are worded honestly ("exactly 5", "a bit more than 1", "less than 1"), and a table compares all four units to show why standard units matter. Suits: comparing and measuring with non-standard units (K–1), measuring in centimetres (1–2), the "start at zero" misconception (2–3).

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `units` | `"cm"` \| `"clips"` \| `"both"` | `"cm"` | Which view(s) to offer. `"both"` adds a switch between the views and shows each unit's size in cm. |
| `object` | `"key"` \| `"leaf"` \| `"crayon"` \| `"feather"` \| `"spoon"` \| `"pencil"` | `"pencil"` | Object selected first. |
| `objects` | string[] | all six | Which objects learners can choose from. |
| `start` | number (0–20) | `2` | Where the object's left end starts on the ruler, in cm (kept on the ruler). `start={0}` begins lined up. |
| `title`, `subtitle` | string | translated | Heading override. |

```mdx
<RulerMeasure units="clips" objects={["spoon", "pencil", "leaf"]} title="How many paper clips long?" />

<RulerMeasure object="crayon" start={4} subtitle="Be careful: the crayon does not start at 0." />

<RulerMeasure units="both" object="pencil" start={0} />
```

---

## PatternMaker

Patterns. **Repeating pattern**: a core unit (for example ● ▲ ▲ ■, labelled A B B C) is repeated in a numbered sequence with alternating shading for each repeat. Learners edit the core (tap a symbol to add it, "Remove last"), then predict item number k (default 20, any 1–100) by choosing a symbol; "Show how" explains it with division with remainder (k ÷ core length = q r r; remainder 0 means the last item of the core). **Growing pattern**: tile figures for steps 1, 2, 3, … following a·n² + b·n + c, drawn so the structure is visible: gold n × n squares (a of them), blue columns of n tiles (b of them) and orange single tiles (c); negative coefficients appear as dashed tiles taken away, so the number of solid tiles is always exactly a·n² + b·n + c. A table shows the number of tiles and the change from step to step; learners predict the tiles in step 10 (or any step up to 50), and "Reveal the rule" shows the rule, a colour legend, and whether the change is constant (linear) or the change of the change is constant (an n² term). Suits: repeating patterns (K–2), predicting with remainders (3–4), growing patterns and tables (4–6), linear and quadratic sequences (7–8).

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `mode` | `"repeat"` \| `"grow"` | `"repeat"` | Mode shown first (learners can switch). |
| `core` | string[] | `["circle", "triangle", "square"]` | Repeat mode: the core unit, 1–6 symbol ids (see below). Unknown ids are dropped. |
| `a`, `b`, `c` | integers | `0`, `2`, `1` | Grow mode: tiles in step n = a·n² + b·n + c. Clamped to a −3…3, b −10…10, c −20…20. If the rule gives fewer than 0 tiles at a shown step, an explanatory message replaces the figures. |
| `steps` | number | repeat: 12–18 (auto); grow: `3` | Repeat mode: how many items of the sequence to show (4–24). Grow mode: how many figures to show at first (1–6); learners can show more, up to step 6 (steps with too many tiles to draw, about 160, are left out with a note). |
| `title`, `subtitle` | string | translated | Heading override. |

**Symbol ids.** A shape, optionally followed by `-` and a colour: `circle`, `triangle`, `square`, `star`, `heart`, `diamond`; colours `red`, `orange`, `yellow`, `green`, `teal`, `blue`, `purple`. Without a colour each shape has its own default (circle orange, triangle blue, square yellow, star purple, heart red, diamond green). Examples: `"star"`, `"circle-blue"`, `"square-red"`. Shapes differ in form as well as colour, and letters (A, B, C…) can be shown under each item, so patterns never rely on colour alone; still, prefer cores that vary the shape.

```mdx
<PatternMaker core={["circle", "square"]} title="AB patterns" />

<PatternMaker core={["star", "heart", "heart", "diamond"]} steps={16} subtitle="Which shape is item 50? Use the remainder." />

<PatternMaker mode="grow" a={0} b={3} c={1} steps={4} title="Matchstick squares: 3n + 1" />

<PatternMaker mode="grow" a={1} b={1} c={0} steps={4} subtitle="Rectangles n × (n + 1). Predict step 10 before you reveal the rule." />
```

---

## DataChart

Data handling. Give it **categorical data** (`data`: labels with counts or amounts) or **numerical data** (`values`: a list of numbers) and learners switch between views of the same data. Categorical: tally chart (gates of five), pictograph (one star = 1, 2, 5 or 10, with partial stars for remainders and a key), bar chart, dot plot (one dot per item) and fair share. Numerical: dot plot on a number line, histogram (bin width slider; bins include their left edge, not their right edge), tally chart of each value, and fair share. **Fair share** draws each amount as a tower of blocks; "Level the towers" moves blocks from tall towers (dashed outlines) to short ones (striped) until all are level at the mean, showing total ÷ count. Mean, median and mode are toggles: lines on bar charts, markers under number lines and histograms, highlighted modal bars/dots, and a panel that explains each one (the sorted list with the middle value(s) highlighted, "no mode" when every value appears once, "≈" whenever a value is rounded). Learners can change the data ("Change the data": +/− per category, or add/remove numbers) and reset it. With no data, a labelled example (favourite fruit) is used. Suits: tallies and pictographs (1–2), bar charts and keys (2–3), dot plots (3–5), mean as fair share (5–6), mean/median/mode and histograms (6–8).

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `data` | `{label, value}[]` | example fruit data | Categorical data, up to 12 entries. `value` ≥ 0 (whole numbers for tally, pictograph and dot plot views; other values only allow bar chart and fair share). Labels up to 24 characters. |
| `values` | number[] | — | Numerical data, up to 120 numbers (decimals allowed). If both are given, `values` wins. |
| `view` | `"tally"` \| `"pictograph"` \| `"bar"` \| `"dot"` \| `"histogram"` \| `"fair"` | `"bar"` (categorical) / `"dot"` (numerical) | View shown first. Views that do not fit the data are not offered. |
| `views` | string[] | all that fit | Which view buttons to offer. |
| `showMean`, `showMedian`, `showMode` | boolean | `false` | Switch the statistic on at the start. |
| `per` | number | automatic | Pictograph key: what one picture stands for (1, 2, 5, 10, or any whole number up to 100 that keeps rows short). |
| `binWidth` | number | automatic (about 5–8 bins) | Starting histogram bin width. |
| `editable` | boolean | `true` | Offer "Change the data". |
| `unit` | string | — | Unit appended to the mean and median in the statistics panel, e.g. `"cm"`. |
| `title`, `subtitle` | string | translated | Heading override (`title` is the widget heading, not a chart caption). |

Statistics for categorical data: the **mean** is the fair share, total ÷ number of amounts; the **median** is the middle amount when the amounts are sorted; the **mode** is the most common category (the largest count). Fair share is offered for categorical data with at least 2 entries and amounts up to 60, and for 2–20 numerical values between 0 and 40.

```mdx
<DataChart data={[{ label: "Cats", value: 7 }, { label: "Dogs", value: 9 }, { label: "Fish", value: 3 }, { label: "Birds", value: 5 }]} view="tally" title="Our pets" />

<DataChart data={[{ label: "Mon", value: 12 }, { label: "Tue", value: 8 }, { label: "Wed", value: 10 }, { label: "Thu", value: 14 }]} view="pictograph" per={2} views={["pictograph", "bar"]} subtitle="Books borrowed from the library each day." />

<DataChart data={[{ label: "Ana", value: 3 }, { label: "Ben", value: 7 }, { label: "Chen", value: 2 }, { label: "Dina", value: 6 }]} view="fair" showMean={true} title="Share the cubes fairly" />

<DataChart values={[132, 141, 128, 150, 137, 144, 139, 146, 133, 152, 141, 138]} view="histogram" binWidth={5} showMean={true} showMedian={true} unit="cm" title="Heights in our class" />
```

---

## Spinner

Simple chance for K–5. A spinner with labelled, coloured sectors of given sizes. "Spin" spins once (the pointer animates and lands at a random angle; the sector under it is the result), "Spin k times" runs a batch. A tally table compares, for each sector, the fraction of spins (count/total and %) with the fraction of the spinner (exact fraction such as 1/4, and %), as paired bars. Recent results are listed. The text says plainly that more spins usually, not always, bring the two closer, and that this is a seeded simulation: evidence, not proof. "Start again" replays the same spins; "New run" uses a new seed. Learners can resize sectors ("Change the sizes"). Suits: certain/likely/unlikely/impossible (K–2), fair and unfair spinners (2–3), experimental vs theoretical probability as fractions (4–5).

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `sectors` | `{label, weight?, color?}[]` | Red 1, Blue 1, Green 2 | Up to 10 sectors, clockwise from the top. `weight` (> 0, default 1) sets the size: a sector's share is weight ÷ total weight. `color` is one of `red`, `orange`, `yellow`, `green`, `teal`, `blue`, `purple`; unspecified sectors get distinct colours automatically. Labels (up to 20 characters) are drawn on the spinner and in the table, so colour is never the only cue. |
| `spins` | number (1–1000) | `10` | Batch size for the "Spin k times" button (`1` hides that button). |
| `seed` | number | `1` | Starting seed (different seeds give different but reproducible runs). |
| `editable` | boolean | `true` | Offer "Change the sizes" (only when all weights are whole numbers; sizes 1–12). |
| `title`, `subtitle` | string | translated | Heading override. |

```mdx
<Spinner sectors={[{ label: "Red", weight: 1, color: "red" }, { label: "Blue", weight: 1, color: "blue" }]} spins={10} title="Is this spinner fair?" />

<Spinner sectors={[{ label: "Cat", weight: 3, color: "purple" }, { label: "Dog", weight: 2, color: "orange" }, { label: "Fish", weight: 1, color: "teal" }]} spins={100} subtitle="Which animal will win most often? Spin 100 times to check." />

<Spinner sectors={[{ label: "Yes", weight: 5, color: "green" }, { label: "No", weight: 1, color: "red" }]} spins={50} editable={false} />
```
