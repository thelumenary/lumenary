# Design system

The Lumenary should feel like a well-lit study: warm paper and deep ink by day, a night sky and lamplight by night. It should be calm, scholarly and joyful, never noisy.

## Brand

- **Name:** The Lumenary (public brand). Mathematics curriculum: **Lumenary Math**.
- **Mark:** a four-pointed star of light inside a ring (`src/components/brand/Logo.tsx`). It reads as a lamp, a compass rose or a point of wonder, and it works at 16 px.
- **Mottos:** "One mathematics. Many languages. Every nation." · "Understand. Prove. Compute. Verify." · "Master the present. Glimpse the future. Never require the future to understand the present."

## Colour tokens

Defined as CSS custom properties in `src/app/globals.css` and exposed to Tailwind via `@theme inline`. Every token has a light and a dark value, and dark mode follows `prefers-color-scheme` unless the reader picks a theme.

| Token | Role |
| --- | --- |
| `paper`, `paper-2`, `card` | Backgrounds |
| `ink`, `ink-2`, `muted` | Text, from strongest to quietest |
| `line`, `line-2` | Borders and rules |
| `gold`, `gold-ink`, `gold-soft` | "Lumen": Wonder Trails, implemented topics, highlights |
| `sky`, `sky-ink`, `sky-soft` | Links, focus, definitions |
| `human`, `formal`, `compute` (+ `-soft`) | The three reasoning modes: terracotta, violet, teal |
| `good`, `warn`, `bad` (+ `-soft`) | Feedback. Never the only signal: always paired with text or an icon |

Colour is never the only carrier of meaning. Mode badges include a letter and an icon, statuses include words, and feedback includes a sentence.

## Typography

| Use | Family |
| --- | --- |
| Display headings | Source Serif 4 (its optical-size axis selects the display cut at large sizes) |
| Interface | Inter |
| Lesson prose | Source Serif 4, paired with KaTeX's Computer Modern style |
| Code | JetBrains Mono |
| Arabic, Devanagari | Noto Sans Arabic, Noto Sans Devanagari (loaded only when glyphs are needed) |
| Chinese | System CJK fonts (PingFang SC, Noto Sans CJK SC, Microsoft YaHei) to avoid multi-megabyte downloads |

Mathematics and code are always isolated as left-to-right runs, including inside right-to-left text.

## Components

- **Section** — a lesson section with its kind label and mode badge, so the lens can highlight it.
- **Blocks** — Definition (sky), Theorem (ink), Proof (rule with ∎), Example, Misconception (warn), Note, Analogy (dashed gold: "analogy, not a formal construction"), Reflection (collapsed and clearly optional), For grown-ups.
- **Narrators** — vector portraits of Chloe (terracotta, Human), Margaret (teal, Computational) and Gideon (violet, Formal, a black tomcat with a bow tie). They appear at every level, as brief substantive asides that never infantilise advanced material. They are shown by default; the cat button in the header hides them site-wide (`<html data-cats="hidden">` hides every element marked `data-cat`, leaving each aside's role label and text), and the choice is remembered in the browser.
- **Verified code frames** — Lean frames carry the verification badge, provenance (library or independent), axioms and a link to the web editor. Python frames carry the evidence type and the test status.
- **Widget frame** — the shared chrome for interactive explorations. Every exploration can be operated with clicks or a keyboard; none requires dragging.

## Motion

Motion is minimal and purposeful: hands on the clock turn, the constellation draws itself, hints float in. All motion is disabled under `prefers-reduced-motion`.

## Voice

Warm, precise, encouraging. Mistakes are "not yet". No exclamation-mark inflation, no shame, no streaks, no leaderboards. Say what is uncertain.
