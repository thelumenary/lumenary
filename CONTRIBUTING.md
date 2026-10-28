# Contributing to The Lumenary

Thank you! The most valuable contributions right now are **mathematical reviews**, **pedagogical reviews** and **translation reviews** — no content has yet been reviewed by a human. See the Contribute page on the site (`content/pages/contribute/en.mdx`) for details.

Before opening a pull request:

```bash
npm run verify   # Lean build, Python experiments, typecheck and tests
npm run build
```

Principles:

- Never claim a proof, test, review, translation or deployment that has not happened.
- Keep identifiers stable (topic ids, lesson slugs, exercise ids, Lean region ids).
- Keep required prerequisites acyclic and honest; use optional discovery edges for "interesting" connections.
- Learner code must only ever run in the learner's own browser sandbox.
- Be kind and precise. Everyone is welcome, whatever their country, culture or belief.

Code is licensed under Apache-2.0; educational content under CC BY-SA 4.0.
