import { describe, expect, it } from "vitest";
import { LOCALES, negotiateLocale } from "@/i18n/config";
import { LanguagesFile } from "@/lib/schema";
import { json } from "./helpers";

type Tree = { [k: string]: string | Tree };
const en = json<Tree>("src/i18n/messages/en.json");

function flatten(tree: Tree, prefix = ""): Map<string, string> {
  const out = new Map<string, string>();
  for (const [k, v] of Object.entries(tree)) {
    const key = prefix ? `${prefix}.${k}` : k;
    if (typeof v === "string") out.set(key, v);
    else for (const [kk, vv] of flatten(v, key)) out.set(kk, vv);
  }
  return out;
}
const placeholders = (s: string) => [...s.matchAll(/\{(\w+)\}/g)].map((m) => m[1]).sort();
const enFlat = flatten(en);

describe("message catalogues", () => {
  it("English has only string leaves (no arrays)", () => {
    const walk = (t: unknown): void => {
      expect(Array.isArray(t)).toBe(false);
      if (t && typeof t === "object") Object.values(t).forEach(walk);
    };
    walk(en);
  });

  for (const locale of LOCALES.filter((l) => l !== "en")) {
    describe(locale, () => {
      const flat = flatten(json<Tree>(`src/i18n/messages/${locale}.json`));
      it("has no keys that English lacks", () => {
        for (const k of flat.keys()) expect(enFlat.has(k), `${locale}: orphan key ${k}`).toBe(true);
      });
      it("keeps the same {placeholders}", () => {
        for (const [k, v] of flat) if (enFlat.has(k)) expect(placeholders(v), `${locale}: ${k}`).toEqual(placeholders(enFlat.get(k)!));
      });
      it("translates most of the interface (coverage is reported, gaps fall back to English)", () => {
        const coverage = flat.size / enFlat.size;
        console.info(`[i18n] ${locale}: ${(coverage * 100).toFixed(1)}% of ${enFlat.size} strings`);
        expect(coverage).toBeGreaterThan(0.9);
      });
    });
  }
});

describe("locale negotiation", () => {
  it("matches base languages and falls back to English", () => {
    expect(negotiateLocale(["es-MX", "en"])).toBe("es");
    expect(negotiateLocale(["fr-FR"])).toBe("en");
    expect(negotiateLocale(["sw-KE"])).toBe("sw");
    expect(negotiateLocale(["zh-CN"])).toBe("zh-Hans");
  });
  it("sends Arabic varieties to Modern Standard Arabic", () => {
    expect(negotiateLocale(["arz"])).toBe("ar");
    expect(negotiateLocale(["ar-EG"])).toBe("ar");
  });
  it("does not silently convert Traditional Chinese preferences to Simplified", () => {
    expect(negotiateLocale(["zh-TW"])).toBe("en");
    expect(negotiateLocale(["zh-Hant-HK", "zh-Hans"])).toBe("zh-Hans");
  });
});

describe("demo locales and the registry agree", () => {
  const reg = LanguagesFile.parse(json("content/registry/languages.json"));
  it("lists every UI locale as a demo language with honest status", () => {
    for (const l of LOCALES) {
      const entry = reg.languages.find((x) => x.tag === l);
      expect(entry, l).toBeDefined();
      expect(entry!.inclusion).toContain("demo");
      if (l === "en") expect(entry!.translationStatus).toBe("canonical");
      else expect(entry!.translationStatus).toBe("machine-draft");
      expect(entry!.reviewStatus).toBe("unreviewed");
    }
  });
});
