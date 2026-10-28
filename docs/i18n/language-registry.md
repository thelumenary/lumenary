# The Lumenary language registry

`content/registry/languages.json` is the machine-readable list of languages the
Lumenary knows about. Each mathematical terminology glossary lives in
`content/registry/glossaries/<tag>.json`. Both are validated against
`LanguagesFile` / `GlossaryFile` in `src/lib/schema.ts`.

The registry is a planning and labelling tool. **Listing a language does not mean
the Lumenary is available in it.** The status fields show what actually exists.
At the time of writing (October 2026) that is:

- English is the canonical source language. All of its content is AI-drafted and
  **has not been reviewed by a named human**.
- Five demo UI locales (`es`, `ar`, `hi`, `zh-Hans`, `sw`) are machine drafts that
  nobody has reviewed.
- No language has `human-reviewed` or `math-reviewed` content.
- Every other entry has `translationStatus: "none"`.

To recompute the summary at any time:

```bash
node -e 'const l=require("./content/registry/languages.json").languages;const c={};for(const x of l)c[x.translationStatus]=(c[x.translationStatus]||0)+1;console.log(l.length,c)'
```

## 1. Purpose

The registry exists so that:

1. the language selector, fallback logic and status badges can all read from one
   source of truth instead of hard-coding languages;
2. coverage claims can be checked mechanically and never inflated;
3. translation work can be planned against the goals in `prompts/init.md` §9.1:
   widely spoken languages, at least one official language for every UN member
   state, regional and Indigenous languages, Modern Standard Arabic, and the major
   spoken Arabic varieties.

## 2. Methodology and its current limits

There is **no single authoritative public "top 100 languages" list**. Published
rankings disagree because they:

- count second-language (L2) speakers differently, or not at all;
- split or merge macrolanguages and varieties differently (Arabic, Chinese,
  Persian, Serbo-Croatian, Hindi and the related languages that Indian census data
  counts under "Hindi", Malay/Indonesian, and so on);
- rely on census data of different ages and quality.

The entries tagged `top-100-seed` come from widely published total-speaker (L1+L2)
rankings, such as the summaries Ethnologue publishes. There are about 100 of them
(102 at the time of writing).

**Known limitation (TODO):** the seed list has **not** been reconciled against a
single cited, dated dataset. Until it is, `top-100-seed` means "appears in
commonly published top-100 rankings", not "verified rank N". The registry
deliberately records **no speaker counts**, so that no unsourced numbers end up
on the site. To close this TODO:

1. choose one dataset with a stable citation (title, edition or date, publisher);
2. record the citation in the `methodology` field;
3. add or remove `top-100-seed` tags to match it, and list the changes in the
   pull request;
4. keep varieties that the dataset counts separately (e.g. `arz`, `apc`) as
   separate entries, and record the dataset's choice in their notes.

The other inclusion reasons are mechanical:

| `inclusion` value     | Meaning |
|-----------------------|---------|
| `top-100-seed`        | In the seed list above (methodology not yet reconciled). |
| `un-official`         | One of the six official languages of the United Nations (ar, zh, en, fr, ru, es). |
| `national-official`   | A de jure official language, or the constitutionally named national/state language, of at least one entry in `countries.json`. The country entry gives the legal detail. |
| `regional-indigenous` | A regional, minority or Indigenous language included for coverage across all inhabited continents, including the 22 languages in the Eighth Schedule of India's constitution. |
| `variety`             | A spoken variety (or regional standard) whose `variantOf` points at its standard/macrolanguage entry, e.g. `arz` → `ar`, `prs` → `fa`, `yue` → `zh-Hant`. |
| `demo`                | One of the six locales the website ships as a demonstration. |

Every country entry's `officialLanguages`, `deFactoLanguages` and
`primaryLumenaryLanguage` must refer to a tag in this registry, every `variantOf`
must name an existing tag, and tags must be unique. Re-check these whenever either
file changes.

## 3. Field definitions (`LanguageEntry`)

| Field | Meaning |
|-------|---------|
| `tag` | BCP 47 tag (see §5). Unique, and stable once published: it is a join key. |
| `name` | English name, chosen for clarity (e.g. "Arabic (Modern Standard)", "Punjabi (Shahmukhi)"). |
| `nativeName` | The language's name for itself, in its own script. The default is the CLDR autonym where CLDR has one; otherwise the most widely attested form, with a note asking a speaker to confirm it. Deliberate departures from CLDR are explained in `notes` (e.g. `ki`). Sign languages have no written autonym, so the English name is shown. |
| `script` | ISO 15924 code of the script used for Lumenary content in this language (`Arab`, `Deva`, `Hans`, …). `Zxxx` (unwritten) is used for sign languages. A language written in several scripts records the one the registry targets, and `notes` names the others. |
| `direction` | `rtl` or `ltr` for running text in that script. This applies to prose; see §7 for mathematics. |
| `family` | Broad genealogical label, for information only (not authoritative, and some groupings are debated). |
| `regions` | ISO 3166-1 alpha-2 codes where the language is official or widely used. Indicative, not exhaustive. |
| `variantOf` | Tag of the standard/macrolanguage entry to fall back to (§8). Only set when that fallback is genuinely readable for the learner. |
| `inclusion` | Why the language is listed (table above). |
| `ui` | State of interface strings: `available`, `machine-draft` or `not-started`. |
| `translationStatus` | Roll-up state of mathematical content in this language (§4). |
| `reviewStatus` | The highest human review that **all** published content in this language has passed: `unreviewed`, `language-reviewed` or `math-reviewed`. |
| `glossary` | Repository path of the terminology glossary, or `null`. |
| `lastReviewed` | ISO date of the most recent completed human review, or `null`. It is `null` everywhere today. |
| `notes` | Caveats: tagging decisions, script choices, uncertainty. |

## 4. Status definitions

The same words are used for individual content files (the `translation` block in
lesson and trail frontmatter, see `Translation` in `src/lib/schema.ts`) and, as a
roll-up, for whole languages in this registry.

| Status | Meaning | Who can set it |
|--------|---------|----------------|
| `canonical` | The source text that every translation is made from. Today this is English. **Canonical does not mean reviewed**: English content is AI-drafted and unreviewed. | Set by the project structure. |
| `machine-draft` | Produced by machine translation or an AI model, with no human review. It must be visibly labelled on the site. | Anyone; it is the default for AI-assisted output. |
| `partial` (registry roll-up only; files use `incomplete`) | Some content exists in the language but not all of it, or some files are incomplete. The site falls back for the missing parts (§8). | Computed. |
| `human-reviewed` | A named human fluent in the language has reviewed the text for language quality, readability and the agreed glossary terms. This does **not** certify the mathematics. | Only with a reviewer record (name, date, scope, `sourceHash` reviewed). |
| `math-reviewed` | A named human who is both fluent in the language and mathematically qualified has checked definitions, theorem statements, proofs, exercises and solutions **in this language** against the canonical source. | Only with a reviewer record. |
| `none` (registry only) | No content in this language. | Default. |

Roll-up rule: a language's `translationStatus` and `reviewStatus` are the
**minimum** over its published content. One reviewed lesson does not make a
language "reviewed". Agreement between several AI models is **not** a review.

## 5. Tagging conventions (BCP 47 and Unicode CLDR)

- Tags follow [BCP 47](https://www.rfc-editor.org/info/bcp47) in the form CLDR
  uses: language (2–3 lowercase letters), optional script (4 letters, Title
  case), optional region (2 uppercase letters or 3 digits, e.g. `es-419`). The
  schema regex allows nothing else. Variants and `-u-` extensions are runtime
  preferences (e.g. `ar-EG-u-nu-latn` for Western digits), not registry entries.
- **Prefer the code CLDR uses.** CLDR often uses the macrolanguage code for the
  dominant individual language: `ar` (= Standard Arabic, ISO 639-3 `arb`), `zh`,
  `sw` (`swh`), `fa` (`pes`), `ms` (`zsm`), `uz`, `ps`, `ne`, `or`, `om`, `ff`,
  `qu`, `mg`, `sq`, `et`, `lv`, `mn`, `ku` (= Kurmanji, `kmr`) and others. Other
  conventions used: `fil` (not `tl`), `nb`/`nn` (not `no`), `ckb` for Sorani,
  `pa` (Gurmukhi) and `pa-Arab` (Shahmukhi; ISO 639-3 also has `pnb`), `prs`
  for Dari (CLDR models it as `fa-AF`; we use `prs` so that it can be its own
  translation target), `cnr` for Montenegrin (code assigned in 2017; CLDR coverage
  is minimal).
- **Add a script subtag only when the script is not implied**, or when the
  registry needs both scripts: `zh-Hans`/`zh-Hant`, `sr`/`sr-Latn`, `pa`/`pa-Arab`.
  In CLDR's parent-locale data a script variant does **not** inherit from the
  default-script locale (`zh-Hant` does not fall back to `zh-Hans`, nor `sr-Latn`
  to `sr`), and the registry follows suit: script variants never have `variantOf`.
- **Collective codes are placeholders.** `ber` (Berber languages) stands in for
  Algeria's constitutionally official "Tamazight", and `nah` (Nahuatl languages)
  for Nahuatl. Before any translation, replace them with an individual language
  code for the variety actually used (e.g. `kab`, `nhe`).
- **Retired codes:** ISO 639-3 change request 2022-006 (effective 2023-01-20)
  merged South Levantine Arabic `ajp` into `apc`, which is now called "Levantine
  Arabic". Normalise incoming `ajp` tags to `apc`; the IANA registry gives
  `apc` as the Preferred-Value of `ajp`.
- Sign languages (`nzs`, `sfs`) are listed because they are official languages of
  countries in `countries.json`. Sign-language content needs video and is outside
  the current text pipeline.

## 6. A region subtag is not a dialect translation

`ar-EG` means **Modern Standard Arabic as localised for Egypt**: the CLDR `ar-EG`
locale uses Egyptian conventions for numbers, dates and currency, but the text is
still MSA. It does **not** mean Egyptian Arabic. Egyptian Arabic is a different
language variety with its own ISO 639-3 code, `arz`, and an `arz` translation is
a separately written text.

Rules:

1. Never label MSA content `arz` (or `ary`, `apc`, …), and never label dialect
   content `ar-XX`.
2. Use a region subtag only when the content really was adapted for that region
   (terminology, notation, currency, examples), and record what changed.
3. The same applies elsewhere: `es-MX` is Spanish adapted for Mexico, not a
   separate language; `zh-Hant-HK` is not Cantonese (`yue`); `pt-BR` and `pt-PT`
   differ in some vocabulary and conventions but are one language.
4. A locale code alone never shows that a genuine dialect translation exists.
   Only `translationStatus` shows that.

The varieties currently listed under `ar` are: `arz` (Egyptian), `apc`
(Levantine, including former `ajp`), `afb` (Gulf), `acm` (Mesopotamian/Iraqi),
`ary` (Moroccan), `arq` (Algerian), `aeb` (Tunisian), `ayl` (Libyan), `apd`
(Sudanese) and `mey` (Hassaniya). They are useful mainly for explanations, audio
and early-years material. Formal mathematics schooling across the Arabic-speaking
world is normally written in MSA.

## 7. Right-to-left scripts and mixed-direction mathematics

The registry includes 25 right-to-left entries (Arabic, Hebrew and Thaana scripts).
Requirements for the site:

- Set `lang` and `dir` on the element that contains the translated text (the
  `<html>` element for a whole page; an inner element for a fallback block). Use
  CSS logical properties (`margin-inline-start`, etc.) rather than left/right.
- **Isolate every formula.** Inline mathematics inside RTL prose must be
  bidi-isolated (`<span dir="ltr">`, `<bdi>`, or `unicode-bidi: isolate`) so that
  surrounding punctuation and numbers are not reordered. In plain strings (UI
  messages, alt text) use the Unicode isolates FSI/LRI … PDI.
- **Mathematical notation direction varies, and the Lumenary must not assume one
  convention.** The W3C Interest Group Note
  [*Arabic mathematical notation*](https://www.w3.org/TR/arabic-math/) (31 January
  2006) describes several styles. It stresses that "there are no clearly defined
  borders between the regions":
  - a **Moroccan style**, close to French usage: left-to-right formulas with Latin
    letters (f, x) and Western digits, embedded in right-to-left Arabic text;
  - a **"Maghreb" style**, which the note says is widely used in North Africa: the
    mirror image, laid out right to left, with Arabic letters for function names
    and some symbols (∑, <, ∈) mirrored;
  - a **"Machrek" (Mashriq) style**, described as generally used in the Middle
    East, with Arabic letters for functions and operators and Arabic-Indic digits
    (the note's example country is Egypt);
  - **Persian**: left-to-right mathematics inside right-to-left text, with Latin
    variables and Eastern Arabic-Indic digits.

  In practice, left-to-right notation with Latin letters is used wherever
  mathematics is taught in French or English, which includes much secondary and
  higher education in the region. Right-to-left Arabic-letter notation is used in
  some school systems. The note dates from 2006 and practice varies by country,
  level and textbook series, so it must be confirmed with educators in each
  country before the Lumenary describes or defaults to any national convention.
  Hebrew and Urdu materials generally embed left-to-right notation in
  right-to-left text.

  MathML supports `dir="rtl"` on `<math>`. The site's current renderer, KaTeX,
  lays mathematics out left to right only, so **RTL Arabic-letter notation is not
  supported yet** (documented TODO). Until it is, Arabic pages use LTR formulas
  and say so.
- Ask native-speaking educators to review mirrored symbols (brackets, arrows,
  ∑, √), the placement of punctuation next to formulas, and line breaking.

## 8. Regional numerals and locale-sensitive formatting

Digits and separators come from CLDR numbering systems through the browser's
`Intl` APIs. Do not use hand-written digit tables.

| CLDR numbering system | Digits | Notes |
|-----------------------|--------|-------|
| `latn` | 0123456789 | Western digits |
| `arab` | ٠١٢٣٤٥٦٧٨٩ (Arabic-Indic) | Used in much of the Mashriq and Gulf |
| `arabext` | ۰۱۲۳۴۵۶۷۸۹ (Extended Arabic-Indic) | Persian, Dari, Pashto; also Urdu, whose fonts select different glyph shapes for some digits when text is tagged `lang="ur"` |
| `deva` | ०१२३४५६७८९ | Devanagari digits |
| `beng`, `guru`, `gujr`, `orya`, `tamldec`, `telu`, `knda`, `mlym` | native digits | Indian scripts |
| `thai`, `laoo`, `khmr`, `mymr`, `tibt` | native digits | Southeast Asian and Tibetan scripts |
| `hanidec` | 〇一二三四五六七八九 | Decimal Han numerals; Chinese mathematics uses Western digits |

The defaults are not uniform even within one language. With CLDR 46 (the version
in Node 22's ICU 76.1), `Intl.NumberFormat` gives:

- Western digits for `ar`, `ar-AE` and the Maghreb locales `ar-MA`, `ar-DZ`,
  `ar-TN` and `ar-LY`. The Maghreb locales also use a decimal comma (1.234,5).
- Arabic-Indic digits for `ar-EG`, `ar-SA`, `ar-IQ`, `ar-SY`, `ar-JO`, `ar-LB`,
  `ar-PS`, `ar-SD`, `ar-KW`, `ar-QA`, `ar-OM`, `ar-YE`, `ar-BH` and `ar-MR`
  (١٬٢٣٤٫٥).
- Extended Arabic-Indic digits for `fa`, `fa-AF` and `ps`, but Western digits for
  `ur`.
- Native digits by default for `bn`, `mr`, `ne` and `my`, but Western digits for
  `hi` and `th`.

These defaults have changed between CLDR releases. Always format with
`Intl.NumberFormat(locale)` and test the output; never hard-code assumptions. A
learner preference can override the default with `-u-nu-latn`, `-u-nu-arab`, and
so on.
- Ethiopic numerals (`ethi`) are additive rather than positional. Use them for
  cultural or historical material only, never to replace place-value digits in
  exercises.
- **Separators matter mathematically.** Locales differ on the decimal separator
  (3.5, 3,5, or ٣٫٥ with the Arabic decimal separator ٫) and the grouping separator. Where the
  decimal separator is a comma, coordinate pairs and lists usually use a semicolon:
  (2,5 ; 3). Interval notation also varies (e.g. ]a, b[ in French-influenced
  curricula). The glossary or a per-locale notation note should record these
  choices; exercises must accept the learner's locale form wherever the answer is
  numeric.
- One expression must not mix digit systems. If a page shows localised digits in
  prose, formulas should either match or follow a documented exception.
- Use `Intl.PluralRules` for counts, and `Intl.DateTimeFormat`, `Intl.ListFormat`
  and `Intl.DisplayNames` for dates, lists and language/region names.

## 9. Fallback policy

When content is not available in the requested locale:

1. **Requested locale**, e.g. `arz`.
2. **Its `variantOf` standard**, e.g. `arz` → `ar`, `prs` → `fa`, `yue` → `zh-Hant`,
   `wuu` → `zh-Hans`. This step only happens along an explicit `variantOf` edge.
   It never happens between scripts (`sr-Latn` ↛ `sr`, `zh-Hant` ↛ `zh-Hans`,
   `pa-Arab` ↛ `pa`) or between distinct languages that happen to be related.
3. **English** (`en`), the canonical source.

Always:

- show a **visible notice** naming both languages ("This lesson is not yet
  available in Egyptian Arabic; showing Modern Standard Arabic"), localised into
  the requested language if a reviewed UI string exists, otherwise into the
  fallback language;
- mark the fallback block with the **correct `lang` and `dir`** attributes of the
  language actually shown, so that screen readers, hyphenation and fonts behave
  correctly;
- show the translation status badge (`machine-draft`, etc.) of what is actually
  displayed;
- fall back per block, not per site: a partly translated lesson shows the
  translated blocks and falls back only for the rest, each block labelled.

## 10. Typography and accessibility

- Use fonts that cover each script (the Noto family covers almost every registry
  script). Urdu needs a Nastaliq face with enough line height; Arabic, Devanagari,
  Thai and Tibetan need room for stacked marks.
- KaTeX emits MathML alongside its visual HTML. Check that `lang` is set on the
  surrounding text so that assistive technology reads the prose in the right
  language. Spoken mathematics in languages other than English is poorly
  supported by today's screen readers; do not claim otherwise.
- Do not convey translation status by colour alone.

## 11. Changing the registry

- Never rename or delete a published `tag`. If a tag was wrong, add the correct
  one and add a note to the old entry.
- Status fields change only through the workflow in
  [translation-workflow.md](translation-workflow.md).
- When you add a language, give a source for any official status claim (in the
  country entry), mark uncertainty in `notes`, and run the content tests.
