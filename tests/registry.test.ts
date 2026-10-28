import { describe, expect, it } from "vitest";
import { CountriesFile, GlossaryFile, LanguagesFile } from "@/lib/schema";
import { exists, json } from "./helpers";

const langs = LanguagesFile.parse(json("content/registry/languages.json")).languages;
const countries = CountriesFile.parse(json("content/registry/countries.json")).countries;
const tags = new Set(langs.map((l) => l.tag));

describe("language registry", () => {
  it("has unique tags", () => expect(tags.size).toBe(langs.length));
  it("resolves every variantOf", () => {
    for (const l of langs) if (l.variantOf) expect(tags.has(l.variantOf), l.tag).toBe(true);
  });
  it("includes Modern Standard Arabic and the major spoken varieties", () => {
    for (const t of ["ar", "arz", "apc", "afb", "acm", "ary"]) expect(tags.has(t), t).toBe(true);
  });
  it("uses rtl exactly for right-to-left scripts", () => {
    for (const l of langs) if (["Arab", "Hebr", "Thaa", "Syrc", "Nkoo"].includes(l.script)) expect(l.direction, l.tag).toBe("rtl");
  });
  it("never claims review without a review date", () => {
    for (const l of langs) if (l.reviewStatus !== "unreviewed") expect(l.lastReviewed, l.tag).not.toBeNull();
  });
  it("has glossaries for languages that point to one", () => {
    for (const l of langs.filter((x) => x.glossary)) {
      expect(exists(l.glossary!), l.glossary!).toBe(true);
      const g = GlossaryFile.parse(json(l.glossary!));
      expect(g.language).toBe(l.tag);
      expect(Object.keys(g.terms).length).toBeGreaterThan(20);
    }
  });
});

describe("country registry", () => {
  it("covers all 193 UN member states and both observer states", () => {
    expect(countries.filter((c) => c.status === "un-member")).toHaveLength(193);
    expect(countries.filter((c) => c.status === "un-observer").map((c) => c.iso2).sort()).toEqual(["PS", "VA"]);
  });
  it("has unique ISO and M49 codes", () => {
    for (const key of ["iso2", "iso3", "m49"] as const) expect(new Set(countries.map((c) => c[key])).size, key).toBe(countries.length);
  });
  it("references only registered languages", () => {
    for (const c of countries) {
      for (const t of [...c.officialLanguages, ...c.deFactoLanguages, c.primaryLumenaryLanguage]) expect(tags.has(t), `${c.iso2}: ${t}`).toBe(true);
    }
  });
  it("explains every country without a de jure official language", () => {
    for (const c of countries.filter((x) => x.officialLanguages.length === 0)) {
      expect(c.deFactoLanguages.length, c.iso2).toBeGreaterThan(0);
      expect(c.notes, c.iso2).toBeTruthy();
    }
  });
  it("gives every UN member state a target language", () => {
    for (const c of countries.filter((x) => x.status === "un-member")) expect(c.primaryLumenaryLanguage, c.iso2).toBeTruthy();
  });
});
