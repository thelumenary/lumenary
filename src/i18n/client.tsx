"use client";

import { createContext, useContext, useMemo } from "react";
import type { Locale } from "./config";
import { LOCALE_META } from "./config";
import { makeT, type Messages, type TFunction } from "./dictionary";

interface I18nValue {
  locale: Locale;
  messages: Partial<Messages>;
  dir: "ltr" | "rtl";
  t: TFunction;
  /** Locale-aware number formatting (regional numerals come from CLDR via Intl). */
  n: (value: number) => string;
}

const I18nContext = createContext<I18nValue | null>(null);

/** Provides messages to client components. Nested providers add namespaces to their parent's. */
export function I18nProvider({ locale, messages, children }: { locale: Locale; messages: Partial<Messages>; children: React.ReactNode }) {
  const parent = useContext(I18nContext);
  const value = useMemo<I18nValue>(() => {
    const merged = { ...(parent?.messages ?? {}), ...messages };
    const fmt = new Intl.NumberFormat(LOCALE_META[locale].intl);
    return { locale, messages: merged, dir: LOCALE_META[locale].dir, t: makeT(merged as Messages), n: (v) => fmt.format(v) };
  }, [locale, messages, parent]);
  return <I18nContext.Provider value={value}>{children}</I18nContext.Provider>;
}

export function useI18n(): I18nValue {
  const ctx = useContext(I18nContext);
  if (!ctx) throw new Error("useI18n must be used inside <I18nProvider>");
  return ctx;
}
