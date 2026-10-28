import "server-only";
import { notFound } from "next/navigation";
import { isLocale, LOCALE_META, type Locale } from "./config";
import { getMessages, makeT, type TFunction } from "./dictionary";

export async function resolveLocale(params: Promise<{ locale: string }>): Promise<Locale> {
  const { locale } = await params;
  if (!isLocale(locale)) notFound();
  return locale;
}

export async function getT(locale: Locale): Promise<TFunction> {
  return makeT(await getMessages(locale));
}

export function formatNumber(locale: Locale, value: number): string {
  return new Intl.NumberFormat(LOCALE_META[locale].intl).format(value);
}

export { href } from "@/lib/href";
