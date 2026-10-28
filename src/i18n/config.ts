/**
 * Demonstration UI locales. These six were chosen to exercise the
 * architecture across language families, scripts, writing directions and
 * regions — they are NOT a claim of global coverage. The full registry of
 * target languages lives in content/registry/languages.json.
 */
export const LOCALES = ["en", "es", "ar", "hi", "zh-Hans", "sw"] as const;
export type Locale = (typeof LOCALES)[number];
export const DEFAULT_LOCALE: Locale = "en";

export interface LocaleMeta {
  tag: Locale;
  name: string;
  nativeName: string;
  dir: "ltr" | "rtl";
  script: string;
  family: string;
  /** Intl locale used for number/date formatting. */
  intl: string;
}

export const LOCALE_META: Record<Locale, LocaleMeta> = {
  en: { tag: "en", name: "English", nativeName: "English", dir: "ltr", script: "Latn", family: "Indo-European · Germanic", intl: "en" },
  es: { tag: "es", name: "Spanish", nativeName: "Español", dir: "ltr", script: "Latn", family: "Indo-European · Romance", intl: "es" },
  ar: { tag: "ar", name: "Arabic", nativeName: "العربية", dir: "rtl", script: "Arab", family: "Afro-Asiatic · Semitic", intl: "ar" },
  hi: { tag: "hi", name: "Hindi", nativeName: "हिन्दी", dir: "ltr", script: "Deva", family: "Indo-European · Indo-Aryan", intl: "hi" },
  "zh-Hans": { tag: "zh-Hans", name: "Chinese (Simplified)", nativeName: "简体中文", dir: "ltr", script: "Hans", family: "Sino-Tibetan · Sinitic", intl: "zh-Hans" },
  sw: { tag: "sw", name: "Swahili", nativeName: "Kiswahili", dir: "ltr", script: "Latn", family: "Niger-Congo · Bantu", intl: "sw" },
};

export function isLocale(value: string): value is Locale {
  return (LOCALES as readonly string[]).includes(value);
}

/** Best supported locale for a list of browser preferences (BCP 47 tags). */
export function negotiateLocale(preferences: readonly string[]): Locale {
  for (const pref of preferences) {
    const lower = pref.toLowerCase();
    if (lower.startsWith("zh")) {
      // Traditional-script preferences fall back to English rather than silently converting script.
      if (lower.includes("hant") || lower.endsWith("-tw") || lower.endsWith("-hk") || lower.endsWith("-mo")) continue;
      return "zh-Hans";
    }
    const base = lower.split("-")[0];
    // Arabic varieties (arz, apc, ary, …) fall back to Modern Standard Arabic.
    if (["arz", "apc", "afb", "acm", "ary", "arq", "aeb", "ayl", "apd"].includes(base)) return "ar";
    const match = LOCALES.find((l) => l.toLowerCase() === base);
    if (match) return match;
  }
  return DEFAULT_LOCALE;
}
