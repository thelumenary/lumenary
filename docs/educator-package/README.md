# Educator evaluation package

The evaluation package is a page on the site, so its figures always come from the current build:

- **Web:** `/en/educators/overview/` (and the same path in every demo locale; the prose falls back to English with a notice). The page prints cleanly on A4 or Letter.
- **Source:** `content/pages/overview/en.mdx` for the prose; live sections such as the curriculum summary, the progressions and the verification results are generated from `content/` and `content/verification/` by `src/app/[locale]/educators/overview/page.tsx`.
- **Screenshots:** `public/educators/screenshots/`, produced by `npm run screenshots` from the exported site. They include light, dark and right-to-left (Arabic) pages.

Contents, following the project brief:

1. Mission and philosophy
2. The three reasoning modes
3. Curriculum map (topic counts per level; implemented lessons)
4. Set-theory and category-theory progressions
5. Representative lessons
6. Wonder Trail demonstrations
7. Website screenshots
8. Verification results (Lean build, Python tests, human review status)
9. Accessibility overview
10. Internationalisation overview
11. Known limitations
12. Areas requiring human review

The package names no private recipient and implies no institutional endorsement.
