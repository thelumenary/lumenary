# Translation workflow

How mathematical content moves from the canonical English source to other
languages, and how its status is recorded. The aim (see `prompts/init.md` §9.3
and §15) is mathematical correctness first. A large number of unreviewed
translations is worth less than a small number of correct ones.

**Current state (October 2026):** no translation has been reviewed by a human,
and the English source itself is AI-drafted and unreviewed. There are no
registered reviewers yet. Every status shown on the site must reflect this.

## 1. Stable content identifiers

Every translatable unit has an identifier that never changes and is never
translated:

| Unit | Identifier | Example |
|------|------------|---------|
| Topic (knowledge graph) | `TopicId` | `math.found.sets` |
| Lesson / trail | `slug` | as in the lesson's frontmatter |
| Exercise | `id` within the lesson's exercise file | `union-basics-1` |
| Glossary term | term id (English kebab-case key) | `empty-set`, `injective` |
| Language | BCP 47 tag from `content/registry/languages.json` | `sw`, `zh-Hans` |

Rules:

- Identifiers are join keys for translations, progress records and the knowledge
  graph. **Never rename or reuse one.** If a unit is replaced, give it a new
  identifier and mark the old one as removed.
- A translated file keeps the **same** slug, topic id and exercise ids as its
  source. Only human-readable fields (titles, prose, hints, feedback, solutions)
  are translated.
- Exercise answers that are data (integers, sets of strings) stay identical. If
  an answer string is language-dependent (for example a set of words), the
  exercise must be redesigned so that the answer is not, or the translated
  answer must be reviewed as part of the mathematics.

## 2. Canonical source and synchronised translations

- English (`en`) is the canonical source. Its files carry
  `translation.status: "canonical"`.
- **Canonical does not mean correct.** The English content is AI-drafted and
  awaits human mathematical and pedagogical review. Fixing the source comes first,
  because every translation inherits its errors.
- Each translation records, in its frontmatter `translation` block (see
  `Translation` in `src/lib/schema.ts`):
  - `status`: `machine-draft`, `human-reviewed`, `math-reviewed` or `incomplete`;
  - `source`: the source language tag (normally `en`);
  - `sourceHash`: the first 12 hex characters of the SHA-256 of the canonical file
    the translation was made from;
  - `translatedAt`: ISO date;
  - `reviewers`: the named reviewers, empty until a human review has happened.

## 3. Staleness detection with `sourceHash`

When the canonical file changes, every translation made from the old version is
**stale**.

```bash
# hash of the current canonical file (first 12 hex chars); in the current layout
# the canonical lesson is content/math/lessons/<slug>/en.mdx
sha256sum content/math/lessons/<slug>/en.mdx | cut -c1-12
```

- If a translation's `sourceHash` differs from the current hash, it is stale. The
  site must say so ("The English original has changed since this translation was
  made") and offer the canonical version.
- A stale translation keeps its recorded status, because that status describes the
  text that was reviewed, but it must not be presented as current. Re-review covers
  at least the changed passages; then update `sourceHash`.
- Build checks should list stale translations rather than fail silently.

## 4. AI-assisted drafts

AI-assisted and machine translation is **allowed**, under these conditions:

1. The output is labelled `machine-draft`, both in the file and visibly on the
   site, until a named human reviews it.
2. It uses the language's glossary (`content/registry/glossaries/<tag>.json`). If
   the glossary lacks a term, the draft flags it instead of inventing one.
3. Mathematical notation, Lean code, Python code, identifiers and answer data are
   copied unchanged; only natural-language text is translated.
4. The pull request says which tool or model produced the draft.
5. **Agreement among several AI models is not review.** Back-translation and
   cross-model comparison can find problems, but they cannot raise a status.

## 5. What requires review

Prose can be improved iteratively. The following must be reviewed before a file
can be `math-reviewed`:

| Content | What the reviewer checks |
|---------|--------------------------|
| **Definitions** | The translated definition is logically equivalent to the source: quantifiers, "or" vs "exclusive or", "at least" vs "exactly", inclusive vs strict inequalities. |
| **Theorem statements** | Hypotheses and conclusions are preserved exactly; no hypothesis has been dropped or strengthened. |
| **Proofs** | Every step still follows; connectives ("therefore", "suppose", "it suffices to show") carry the right logical force. |
| **Terminology** | Terms match the glossary. Regional conventions (e.g. whether 0 ∈ ℕ, "rango" vs "recorrido", "مبرهنة" vs "نظرية") are stated, not silently changed. |
| **Exercises, hints, feedback and solutions** | The question asks the same thing; numeric answers remain correct under the locale's number formatting; feedback for wrong answers still matches the wrong answers it targets; hints do not give away more or less than the source. |
| **Notation and direction** | Formulas render correctly in RTL pages; digits and separators follow the locale decision in [language-registry.md](language-registry.md) §8. |

`human-reviewed` (language quality) may come before `math-reviewed`, but the site
must make clear that `human-reviewed` alone does not certify the mathematics.

## 6. Status transitions

```
none ──► machine-draft ──► human-reviewed ──► math-reviewed
              │                  │                  │
              └──── incomplete ◄─┴──────────────────┘   (content missing or partly translated)

any status ──(canonical changes)──► stale flag (status kept, shown as out of date)
any status ──(error found)──────► downgraded to the highest status still true
```

- **none → machine-draft:** a draft exists and is labelled.
- **machine-draft → human-reviewed:** a named reviewer fluent in the language has
  reviewed it. Add them to `reviewers` and record the date.
- **human-reviewed → math-reviewed:** a named reviewer who is fluent in the
  language **and** mathematically qualified has checked the items in §5 against
  the canonical source. Record the `sourceHash` they reviewed.
- **Skipping:** a single reviewer with both competences may go straight from
  `machine-draft` to `math-reviewed` by recording both checks.
- **Downgrades:** if an error is found, lower the status to whatever is still
  true and record why in the pull request. Never leave an inflated status in place
  while a fix is pending.
- **Registry roll-up:** `translationStatus`/`reviewStatus` in `languages.json`
  are the minimum over all published content in that language (`partial` if some
  content is missing). `lastReviewed` is the date of the most recent completed
  review.
- Glossaries follow the same ladder (`machine-draft` → `human-reviewed` →
  `math-reviewed`). Review a language's glossary first: reviewed content in that
  language should rest on a reviewed glossary.

## 7. Becoming a reviewer

The project has **no registered reviewers yet**. Proposed process (to be adopted
when the repository accepts contributions):

1. Open an issue (or use the Contribute page) saying which language(s) and
   region(s) you can review, and whether you offer language review, mathematical
   review or both. Mention relevant experience (teaching mathematics in that
   language, a degree in mathematics, translation work). The project does not
   verify credentials and will not claim to.
2. Start with the glossary for your language: check every term, add regional
   alternatives, and flag terms with no established equivalent.
3. Review content in a pull request. Write your review notes in the pull request
   and add your name (or the public handle you choose) to `reviewers` only for the
   files you actually reviewed.
4. Reviews are public and attributable. A reviewer may withdraw their name, and
   the status then drops accordingly.

## 8. Never inflate counts

- A language is **"available"** only for what its status says: "5 machine-drafted
  demo locales", not "6 languages supported".
- Count reviewed languages by the roll-up statuses, not by the number of registry
  entries, UI string files or locale codes.
- A region subtag (`ar-EG`) is never a separate language in counts, and a dialect
  (`arz`) counts only if `arz` content exists.
- Fallback content is not translated content.
- Site copy, README badges and reports must compute these numbers from the
  registry and from the frontmatter, not hand-write them.

## 9. Localisation beyond words

Examples, names, currencies, measurement units and contexts may be adapted for a
locale, following [../geography.md](../geography.md). Adaptations are part of the
translation and are reviewed in the same way. An adapted exercise must keep the
same mathematical content and difficulty.
