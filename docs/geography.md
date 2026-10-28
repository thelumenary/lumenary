# Geography and fairness

> **Mathematics belongs to everyone. Human dignity does not depend on national wealth.**
> (`prompts/init.md` §10)

This document covers three things:

1. the geographic registry, `content/registry/countries.json`;
2. the fairness principles of §10, written as concrete authoring guidance;
3. the procedure for auditing curriculum content. **No audit has been run yet.**

## 1. The geographic registry

### Purpose

The registry lets the Lumenary:

- pick a first language for each country (`primaryLumenaryLanguage`) and show
  learners the languages relevant to them;
- check, mechanically, that every UN member state has at least one registry
  language (this is the §9.1 "at least one official language for every UN member
  state" target);
- group content by UN M49 region when auditing for geographic balance (§3 below).

It is **not** a statement about politics, sovereignty or borders. It follows the
classification sources listed in its `sources` field and describes legal language
status factually.

### Contents (October 2026)

| `status` | Count | Meaning |
|----------|------:|---------|
| `un-member` | 193 | All UN Member States |
| `un-observer` | 2 | UN non-member observer States: Holy See (VA), State of Palestine (PS) |
| `territory` | 18 | Non-sovereign territories and dependencies chosen for language relevance (e.g. Hong Kong SAR and Macao SAR of China, Puerto Rico, Greenland, Faroe Islands, New Caledonia, French Polynesia, Guam, Réunion, French Guiana, Aruba, Curaçao, Bermuda) |
| `other` | 3 | Entities that are neither UN members/observers nor dependent territories: Taiwan, Cook Islands, Niue |

The extra entries were chosen because they have their own official languages or
distinct language situations. The selection is not exhaustive, and adding more is
welcome.

**Known gaps:** Kosovo and Western Sahara are not listed. Kosovo has no ISO 3166-1
code or M49 code, and the schema requires both. Western Sahara was simply not
selected. These are data-model and selection limits, not positions.

### Field conventions

- **`m49`, `region`, `subregion`:** from UN M49. `subregion` is the
  *intermediate region* where M49 defines one (Eastern/Middle/Southern/Western
  Africa; Caribbean; Central America; South America), and otherwise the
  sub-region (e.g. Northern Africa, Northern America, Western Asia, Polynesia).
  The numeric code equals the ISO 3166-1 numeric code. Taiwan is not listed
  separately in M49, so its ISO 3166-1 code (158) is used and its region is
  assigned geographically. Its note explains this neutrally.
- **Names:** UN short names for UN members and observers (e.g. "Türkiye",
  "Viet Nam", "Bolivia (Plurinational State of)"), M49 names for Hong Kong and
  Macao, and the common short name for Taiwan with the ISO 3166-1 name in its note.
- **`officialLanguages`: de jure only.** A language is listed only when a
  constitution or statute designates it. When the constitution names a "national"
  or "state" language and designates no separate official language, that language
  is recorded and the wording is given in `notes` (e.g. Bhutan, Viet Nam,
  Seychelles). When a text distinguishes a "national" language from "working"
  languages and calls neither official (Niger's 2025 charter), the list is left
  empty and `notes` explains.
- **Empty `officialLanguages`** means no legal designation applies or has been
  found. `deFactoLanguages` then lists the languages actually used nationally or
  administratively, and `notes` explains the situation (e.g. United Kingdom,
  Australia, Mexico, Japan, Eritrea, Bosnia and Herzegovina at state level).
  `deFactoLanguages` is also used, with an explanation, where de jure languages
  exist but the main working language is a different one (New Zealand: English;
  Mali and Burkina Faso: French as a working language).
- **Partial lists:** some countries designate more official languages than the
  language registry contains (Bolivia, Zimbabwe, Mali, Burkina Faso, Guinea). Their
  `notes` begin with "Partial list." and name the missing languages where known.
- **`needsReview: true`** means a fact in the entry is uncertain or unverified.
  Most commonly the note says "Legal basis not verified", meaning the language is
  universally treated as official but the drafter has not checked which provision
  makes it so. Other flags cover recent constitutional changes that have not been
  re-checked, and situations still in flux. These entries must be checked against
  primary legal texts before the site makes any claim about them.
- **`primaryLumenaryLanguage`** is a provisional planning choice. Normally it is
  the most widely used de jure official language (or, where there is none, the most
  widely used national/de facto language). Where the main medium of school
  mathematics differs (e.g. English in Kenya and Zimbabwe, French in Mali and
  Niger), `notes` says so, and a second pathway in that language matters just as
  much. It is never a judgement about which language is more important.

## 2. Fairness principles as authoring guidance

The goal is a curriculum where no country, region, culture, ethnicity or income
group is treated as the default representation of humanity. These are working
rules for authors and reviewers. Each one has an example to avoid and a better
alternative.

### Universal dignity

Portray people everywhere as capable individuals with agency.

- **Avoid:** "Help the poor villagers count how many bags of donated rice they received."
- **Better:** "Amara runs a rice stall at the Kumasi market. She has 3 sacks of 25 kg. How many 2 kg bags can she fill?"

### Balanced representation

Across a course (not within every lesson), include people and settings from high-,
middle- and low-income countries on all inhabited continents.

- **Avoid:** every named character in a unit has an English or Western European name.
- **Better:** across the unit, the names and settings vary (Lagos, Lima, Lahore,
  Lyon, Ulaanbaatar, Auckland, Detroit, Hanoi…), and each one is chosen because it
  fits the problem, not to fill a quota.

### No geographic favouritism

Do not make one region the unmarked default.

- **Avoid:** "a typical school day starts in September" or "in winter (December)"
  as if this were universal; using "$" without saying which dollar.
- **Better:** state the place when it matters ("In Santiago, winter starts in
  June"), and name currencies explicitly (USD, KES, INR, MXN).

### No development stereotypes

Wealthier and poorer countries both appear in every kind of context: science,
business, art, sport, everyday life, and problems.

- **Avoid:** Germany appears only in engineering problems and Malawi only in
  problems about disease or aid.
- **Better:** a Malawian software developer optimises a delivery route; a German
  town plans flood defences on a budget.

### Factual accuracy

Do not pretend conditions are identical everywhere, and do not exaggerate
differences either.

- **Avoid:** "Every student can check this on their laptop", or invented
  statistics such as "Only 10% of people in X have electricity".
- **Better:** offer a pencil-and-paper path alongside the computational one. Use
  real data only with a cited source and year; otherwise use clearly invented,
  neutral numbers ("Suppose a town has 12,000 households…").

### Ordinary life everywhere

Show people studying, working, building, playing and creating everywhere.

- **Avoid:** non-Western settings appear only as festivals, safaris or exotic
  travel.
- **Better:** a bus timetable in Nairobi, a cricket score in Dhaka, a bakery in
  Montréal, a tiling pattern for a new school in Marrakech. All are ordinary
  scenes.

### Historical accuracy

Credit mathematical contributions from all civilisations, based on reliable
evidence. Never invent or inflate attributions.

- **Avoid:** "Pythagoras discovered the Pythagorean theorem", and equally,
  unsupported claims that some other civilisation "really" invented a result first.
- **Better:** "The theorem is named after Pythagoras, but the relationship was
  known much earlier, for example in Old Babylonian mathematics, and it appears in
  ancient Indian and Chinese texts. A proof appears in Euclid's *Elements*."
  Other well-documented examples: Brahmagupta's *Brāhmasphuṭasiddhānta* (628 CE)
  gives rules for arithmetic with zero and negative numbers; the word "algebra"
  comes from *al-jabr* in the title of al-Khwārizmī's 9th-century book; a
  simultaneous-remainder problem of the kind solved by the Chinese remainder
  theorem appears in the *Sunzi Suanjing*. Cite a scholarly source for every
  historical claim in a lesson, and use hedged language ("the earliest known
  surviving text…") where the evidence is incomplete.

### Local relevance

Adapt names, currencies, units and contexts in translations and regional editions
where it helps understanding.

- **Avoid:** translating "a quarter (25¢)" literally into a locale without
  quarters, or using miles and Fahrenheit in a problem meant for everyone.
- **Better:** SI units by default, with customary units where a locale really
  uses them; currency problems written so that the currency can be swapped without
  changing the mathematics. Adaptations are reviewed with the translation (see
  [i18n/translation-workflow.md](i18n/translation-workflow.md) §9).

### No tokenism

A geographic detail must serve the mathematics or the learner's engagement.

- **Avoid:** "In Kenya, Juma has 5 apples and eats 2." Here the country adds
  nothing, and it is there only to tick a box.
- **Better:** use the location when it brings real structure, such as the
  Kenyan shilling, Nairobi's matatu routes for a graph problem, or the Swahili
  number words for a counting-systems lesson. Otherwise use a name alone.

### Equal dignity is not identical circumstances

Do not erase real differences, and do not define people by them. A lesson may
discuss real inequality, for example by using cited data to teach statistics, but
those same countries must also appear in all the other kinds of context.

## 3. Audit procedure

> **Status: this process has not yet been run.** No geographic audit of
> Lumenary content exists, and no results should be cited.

The audit looks for omissions, narrow portrayals and systematic bias across the
whole curriculum. It does **not** require any particular country in any
particular lesson (§10: "Do not require a fixed set of countries in every
lesson").

### When

- Before each roadmap phase is declared complete (`prompts/init.md` §18), and at
  least once per year after that.
- In addition, for any single unit with more than about 20 contextualised
  examples, when it is first published.

### What to count

For each lesson, exercise file, trail and image, record every **contextual
reference**: a named person, a place, a currency, a unit system, an institution,
a cultural practice or a depicted setting. For each reference, note:

| Column | Values |
|--------|--------|
| `content_id` | lesson slug / exercise id / trail slug |
| `kind` | person-name, place, currency, unit, institution, practice, image |
| `country` | ISO 3166-1 alpha-2 (or `none`/`fictional`) |
| `m49_region` / `subregion` | from `countries.json` |
| `income_group` | from a cited, dated external classification (e.g. the World Bank's), recorded in the audit report rather than the registry |
| `role` | the portrayal category: everyday life, work/business, science/technology, art/culture, sport/play, history of mathematics, hardship/aid/disaster, other |
| `purpose` | why the reference is there (mathematical structure, data, engagement, none) |

### Checks

1. **Coverage by M49 region and subregion:** counts and shares, set against a
   simple baseline. Report regions with no references at all.
2. **Default checks:** are unmarked defaults (seasons, currencies, units, school
   calendars) region-specific?
3. **Narrow-portrayal check:** for each region and income group, what is the
   distribution of `role`? Flag any group whose references are dominated by
   hardship, aid or disaster, or any group that appears only in science and
   prosperity contexts.
4. **Names check:** variety of personal names by cultural origin; no group used
   only for minor or negative roles.
5. **History check:** every historical attribution has a citation, and claims are
   hedged appropriately.
6. **Tokenism check:** references whose `purpose` is "none".
7. **Translation check:** whether localised editions keep or adapt contexts, and
   whether adaptations are reviewed.

### Output

An audit report in `docs/audits/geography-<YYYY-MM-DD>.md` (to be created when
the first audit is run) containing: scope and content version (commit), method,
raw counts, findings, and remediation issues with owners. Findings lead to edits
or new examples, never to quotas. The report must state its own limits (e.g.
"images not yet audited").
