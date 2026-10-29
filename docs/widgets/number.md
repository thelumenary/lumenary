# Number and arithmetic widgets (K–8)

Six interactive explorations for early number, place value, fractions, number theory, equations and ratio. Use them in lesson MDX by tag name. Every prop is optional, and bad values are clamped or ignored, so a widget never crashes a lesson.

**MDX syntax.** Strings go in quotes (`mode="add"`). Everything else goes in braces: numbers (`a={47}`), booleans (`table={true}`), arrays (`fractions={["3/4", "2/3"]}`) and objects (`left={{ x: 2, units: 3 }}`; note the double braces).

**Shared props.** Every widget accepts `title` and `subtitle` (plain English strings) to replace the default translated heading. Leave them out to get the default heading in the reader's language. Only the widget's own interface is translated, never your `title`, `subtitle` or `labels`.

**Numbers in the widgets are exact.** Fractions are rational arithmetic, not floating point. Every explanation the widgets show is computed from the actual numbers on screen.

| Tag | What it is for | Typical grades |
| --- | --- | --- |
| `TenFrame` | counting to 20, "how many more make ten", the make-ten addition strategy | K–2 |
| `PlaceValue` | base-ten blocks, regrouping, why carrying and borrowing work | 1–4 |
| `FractionBars` | comparing, equivalent fractions, adding/subtracting, fractions and decimals on a number line | 3–6 |
| `NumberGrid` | multiples and common multiples, the Sieve of Eratosthenes, factor pairs, Euclid's algorithm | 3–8 |
| `BalanceScale` | solving linear equations by doing the same thing to both sides | 6–8 |
| `DoubleNumberLine` | ratios, rates, unit rates, equivalent ratios | 6–7 |

---

## TenFrame

One or two ten-frames (2 rows of 5). In **count** mode, children tap boxes to put in or take out dots. The widget shows the number, how many more make ten, and for 11–20 the split "ten and some more" (`13 = 10 + 3`). In **make-ten** mode it shows `a + b` with `a` dots in the top frame and `b` dots in the bottom frame. Pressing "Make ten" slides just enough dots up to fill the first frame, so the sum reads as `8 + 5 = 8 + 2 + 3 = 10 + 3 = 13`. The two addends use different colours and also different dot shapes (solid, and with a hole). Suits lessons on counting, subitizing, number bonds to 10, teen numbers and addition within 20.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `mode` | `"count"` \| `"make-ten"` | `"count"` | Which activity. |
| `count` | number 0–20 | `0` | Dots already placed (count mode). |
| `frames` | `1` \| `2` | `1`, or `2` if `count` > 10 | Number of ten-frames (count mode). With `frames={1}`, `count` is capped at 10. |
| `a` | number 0–10 | `8` | First addend (make-ten mode). Learners can change it. |
| `b` | number 0–10 | `5` | Second addend (make-ten mode). Learners can change it. |
| `title`, `subtitle` | string | translated | Heading overrides. |

```mdx
<TenFrame />

<TenFrame count={7} title="How many more make ten?" />

<TenFrame frames={2} count={13} subtitle="Show 13 as one full ten and some more." />

<TenFrame mode="make-ten" a={9} b={4} />
```

---

## PlaceValue

Base-ten blocks in place-value columns: small cubes (ones), rods (tens), flats (hundreds) and large cubes (thousands). Rods and flats are drawn to the same scale as the small cubes, so a rod is visibly 10 cubes and a flat 10 rods.

- **build**: learners add or remove blocks in each column and regroup with the buttons "10 ones → 1 ten" and "1 ten → 10 ones" (and the same for the other columns). Regrouping is animated. The widget shows the numeral and its expanded form (`300 + 40 + 7`). If a column holds 10 or more blocks, it writes `3 × 100 + 4 × 10 + 17 × 1 = 357` and suggests trading.
- **add** / **subtract**: a step-by-step walkthrough of the written column method beside the blocks. Each step works on one column. Combining a column that reaches 10 or more triggers a separate regroup step ("trade 10 ones for 1 ten", the carried 1). A subtraction column that is short triggers break steps, including breaking across a zero, as in 503 − 127. The written method shows carries and crossed-out digits exactly as children write them, and the active column is highlighted in both views. Learners can type their own numbers.

Suits lessons on place value, expanded form, regrouping, and multi-digit addition and subtraction.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `mode` | `"build"` \| `"add"` \| `"subtract"` | `"build"` | Which activity. |
| `start` | number | `0` | Starting number in build mode (clamped to `max`). |
| `a` | number | `47` (add), `52` (subtract) | First number. |
| `b` | number | `38` (add), `27` (subtract) | Second number. In add mode it is reduced so that `a + b ≤ max`. In subtract mode, if `b > a` the two are swapped and a note says so. |
| `max` | number 9–9999 | `999` (build), `9999` (add/subtract) | Largest number allowed. In build mode it also chooses the columns: `99` gives tens and ones, `999` adds hundreds, `9999` adds thousands. |
| `title`, `subtitle` | string | translated | Heading overrides. |

```mdx
<PlaceValue start={347} />

<PlaceValue start={1234} max={9999} title="Thousands, hundreds, tens and ones" />

<PlaceValue mode="add" a={368} b={275} />

<PlaceValue mode="subtract" a={503} b={127} subtitle="What happens when there are no tens to break?" />
```

---

## FractionBars

Fraction strips, all the same length, so "the same whole" is visible. Four modes:

- **compare**: the given fractions as bars, with dashed lines marking where each one ends. The widget states the order with `<`, `=`, `>` and rewrites every fraction over a common denominator to explain why. Learners can change any numerator or denominator.
- **equivalent**: the first fraction, in simplest form, above a copy whose parts are cut into `k` pieces by a slider. Thick lines keep the original parts visible. It shows `(2 × k)/(3 × k)` and the family `2/3 = 4/6 = 6/9 = …`, and each member of the family can be tapped. A non-simplest input such as `6/8` starts at that form, so sliding down reveals the simplest form.
- **add**: three steps for `a/b ± c/d`. Step 1 shows that the pieces differ in size. Step 2 re-cuts both into the least common denominator. Step 3 combines or takes away the pieces, with the result simplified (and given as a mixed number if it is more than 1). Learners can switch between + and − and edit both fractions.
- **line**: points on a 0–1 number line (0–2 if any value is above 1), with tick marks for a learner-chosen number of equal parts. Equal values share one point (`0.75 = 3/4`). Learners can type more numbers and remove points, and the values are listed in order with their simplest-fraction and decimal forms.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `mode` | `"compare"` \| `"equivalent"` \| `"add"` \| `"line"` | `"compare"` | Which activity. |
| `fractions` | string array (a single string also works) | compare `["3/4","2/3"]`, equivalent `["2/3"]`, add `["1/2","1/3"]`, line `["1/4","0.5","2/3","0.75"]` | The values. Accepted forms: `"3/4"`, mixed numbers `"1 1/2"`, whole numbers `"2"`, decimals `"0.75"`, `".5"` or `"0,75"`. Negative numbers and words are not accepted: unreadable entries are listed in a short notice and skipped. **compare**: up to 6 values from 0 to 2. **equivalent**: the first value only (0 to 2). **add**: the first two values, each from 0 to 1. **line**: up to 12 values, and values above 2 are listed as not shown. |
| `maxDenominator` | number 2–24 | `12` | Largest denominator the steppers allow, the largest split in equivalent mode, and the largest tick-mark count in line mode. |
| `op` | `"+"` \| `"-"` | `"+"` | Add mode only: start with addition or subtraction (`"subtract"` and `"−"` also work). If the second fraction is larger, subtraction puts the larger one first and says so. |
| `title`, `subtitle` | string | translated | Heading overrides. |

```mdx
<FractionBars mode="compare" fractions={["1/2", "2/4", "3/5"]} />

<FractionBars mode="equivalent" fractions={["6/8"]} maxDenominator={16} title="Find the simplest form" />

<FractionBars mode="add" fractions={["3/4", "1/6"]} op="-" />

<FractionBars mode="line" fractions={["0.75", "3/4", "1 1/2", "0.2"]} subtitle="Decimals and fractions share the same line." />
```

---

## NumberGrid

A numbered grid (1 to `size`, `columns` per row) plus two geometric pictures:

- **multiples**: marks the multiples of `k` with a circle. Turning on a second number `k2` marks its multiples with a square outline. Common multiples get both marks and gold text, and the widget names the least common multiple. Tapping any number explains it (`22 = 5 × 4 + 2`, so it is not a multiple of 5). Try `columns={6}` or `columns={7}` to see different patterns.
- **sieve**: the Sieve of Eratosthenes, one prime per step. 1 is crossed out first. Each step crosses out the multiples of the next prime (each prime gets its own colour of strike-through, plus a legend), highlights the newly crossed numbers, and notes that multiples below p² were already gone. The last step circles every survivor, lists the primes, and explains why we can stop at √size. Tapping a number shows which prime crossed it out (`91 = 7 × 13`).
- **factors**: `n` dots arranged with a chosen number of dots per row. Either they form a rectangle (a factor pair) or some are left over (shown with a dashed outline), as in `24 = 4 × 5 + 4`. Below are thumbnails of every factor pair as a rectangle, the list of factors, and a note on prime, composite, square, or 1.
- **gcd**: Euclid's algorithm as cutting the largest possible squares from an `a × b` rectangle, one step at a time, with the equations `36 = 2 × 15 + 6, 15 = 2 × 6 + 3, 6 = 2 × 3 + 0` alongside. At the end, an optional overlay shows that squares of side gcd(a, b) tile the whole rectangle.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `mode` | `"multiples"` \| `"sieve"` \| `"factors"` \| `"gcd"` | `"multiples"` | Which activity. |
| `size` | number 10–400 | `100` | Largest number on the grid (multiples, sieve). |
| `columns` | number 2–20 | `10` | Numbers per row (multiples, sieve). |
| `k` | number 1–50 | `3` | Number whose multiples are marked (multiples). Learners can change it. |
| `k2` | number 0–50 | none | A second number (multiples). When given, the comparison starts switched on. `0` means off. |
| `n` | number 1–200 | `24` | Number to factor (factors). Learners can change it. |
| `a`, `b` | numbers 1–300 | `36`, `15` | Rectangle width and height (gcd). Learners can change them. |
| `title`, `subtitle` | string | translated | Heading overrides. |

```mdx
<NumberGrid mode="multiples" k={4} k2={6} title="When do the two patterns meet?" />

<NumberGrid mode="multiples" k={3} columns={6} size={60} />

<NumberGrid mode="sieve" size={120} />

<NumberGrid mode="factors" n={36} />

<NumberGrid mode="gcd" a={21} b={13} subtitle="Consecutive Fibonacci numbers make Euclid work hard." />
```

---

## BalanceScale

A level balance whose pans hold x-boxes (unknown weight) and unit weights. Learners press "Add 1 to both sides", "Take 1 from both sides", "Take x from both sides" (and "Add x to both sides" when negatives are on), or "Divide both sides by k" for k = 2–9. A move that is not legal is refused with a reason. For example, dividing by 2 is refused when some amount on either side is odd, and taking a 1 away is refused when a side has none (unless negatives are on). Every legal move keeps the scale level. When x stands alone, the widget gives the solution and checks it in the original equation (`2 × 4 + 3 = 11 → 11 = 11 ✓`). Beside the scale, a record lists the equations step by step, with repeated moves merged (`− 3`, `÷ 2`). If the solution is not a whole number (`2x = 7`), the widget says so and gives `x = 7/2`. An equation with the same number of x's on both sides but different units can never balance, so the scale tilts and the widget states that there is no solution. If both sides are identical, every x works. A "Make your own equation" panel lets learners set up a new scale.

Negative amounts are drawn as **balloons** that pull upwards (red dashed `−1` balloons, purple `−x` balloons).

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `left` | `{ x: number, units: number }` | `{ x: 2, units: 3 }` | Left pan: number of x-boxes and of unit weights (each −20 to 20). |
| `right` | `{ x: number, units: number }` | `{ x: 0, units: 11 }` | Right pan. |
| `allowNegative` | boolean | `false` | Allow amounts below zero (balloons). It switches on automatically when an amount is negative or the solution is negative, because x could not be isolated otherwise. |
| `title`, `subtitle` | string | translated | Heading overrides. |

```mdx
<BalanceScale />

<BalanceScale left={{ x: 3, units: 1 }} right={{ x: 1, units: 9 }} title="x on both sides" />

<BalanceScale left={{ x: 3, units: -2 }} right={{ x: 1, units: 6 }} />

<BalanceScale left={{ x: 1, units: 2 }} right={{ x: 1, units: 5 }} subtitle="Can you make this scale level?" />
```

---

## DoubleNumberLine

Two parallel number lines, one per quantity, with matching multiples of the ratio `a : b` lined up (0, a, 2a, … above and 0, b, 2b, … below). A slider and "± a" buttons move a marker along both lines together, and the matching amounts are shown exactly. Between marks they may be decimals or fractions (`3 : 7.5`, `4 : 26 2/3`). When `a` > 1, a gold dashed tick marks the unit rate (1 on the top line). The panel shows both unit rates, the chain of equivalent ratios, the simplest form, and how many times the starting ratio the current pair is. An optional table lists the multiples, the unit-rate row and the current position. Suits lessons on ratio language, rates, unit price, scaling recipes and proportional reasoning.

| Prop | Type | Default | Meaning |
| --- | --- | --- | --- |
| `a` | whole number 1–1000 | `3` | First term of the base ratio (top line). Decimals are rounded. |
| `b` | whole number 1–1000 | `24` | Second term (bottom line). |
| `labels` | `[string, string]` | `["cups of flour", "cookies"]` (translated) | Names of the top and bottom quantities. Write them as plural nouns. |
| `max` | number 1–12 | `5` | How many multiples of the ratio the lines show. |
| `table` | boolean | `false` | Start with the table open (learners can toggle it). |
| `title`, `subtitle` | string | translated | Heading overrides. |

```mdx
<DoubleNumberLine />

<DoubleNumberLine a={2} b={5} labels={["cups of rice", "servings"]} max={8} table={true} />

<DoubleNumberLine a={4} b={3} labels={["dollars", "notebooks"]} title="Best buy?" />

<DoubleNumberLine a={60} b={1} labels={["kilometres", "hours"]} max={6} subtitle="A steady speed is a rate." />
```

---

## Notes for maintainers

- Components: `src/components/widgets/{TenFrame,PlaceValue,FractionBars,NumberGrid,BalanceScale,DoubleNumberLine}.tsx`. Registered in `src/components/widgets/registry-number.ts` (`NUMBER_WIDGETS`).
- Pure logic, unit-tested in `tests/widgets-number.test.ts`, lives in `src/components/widgets/lib/number-*.ts`: `number-fraction` (exact rationals and parsing), `number-place` (regrouping and the walkthrough generator), `number-grid` (sieve, factors, Euclid squares), `number-balance` (moves and solving), `number-ratio`, `number-tenframe` and `number-common`.
- Strings live under `w.tenFrame`, `w.placeValue`, `w.fractions`, `w.numberGrid`, `w.balance` and `w.doubleLine` in all six catalogues.
- No randomness is used, so server and client renders are identical.
