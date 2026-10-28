import en from "./messages/en.json";
import type { Locale } from "./config";

export type Messages = typeof en;
type Json = string | { [key: string]: Json };

/**
 * Message catalogues. Missing keys in a locale fall back, key by key, to the
 * canonical English source — a partially translated locale still renders.
 */
const loaders: Record<Locale, () => Promise<{ default: unknown }>> = {
  en: () => import("./messages/en.json"),
  es: () => import("./messages/es.json"),
  ar: () => import("./messages/ar.json"),
  hi: () => import("./messages/hi.json"),
  "zh-Hans": () => import("./messages/zh-Hans.json"),
  sw: () => import("./messages/sw.json"),
};

function deepMerge(base: Json, over: Json | undefined): Json {
  if (over === undefined) return base;
  if (typeof base === "string" || typeof over === "string") return typeof over === "string" ? over : base;
  const out: { [key: string]: Json } = {};
  for (const key of Object.keys(base)) out[key] = deepMerge(base[key], over[key]);
  return out;
}

export async function getMessages(locale: Locale): Promise<Messages> {
  if (locale === "en") return en;
  try {
    const mod = await loaders[locale]();
    return deepMerge(en as Json, mod.default as Json) as Messages;
  } catch {
    return en;
  }
}

/** Look up a dotted key and interpolate `{name}` placeholders. */
export function translate(messages: Messages, key: string, vars?: Record<string, string | number>): string {
  let node: unknown = messages;
  for (const part of key.split(".")) {
    if (node && typeof node === "object" && part in (node as object)) node = (node as Record<string, unknown>)[part];
    else {
      node = undefined;
      break;
    }
  }
  let text = typeof node === "string" ? node : key;
  if (vars) for (const [k, v] of Object.entries(vars)) text = text.replaceAll(`{${k}}`, String(v));
  return text;
}

export type TFunction = (key: string, vars?: Record<string, string | number>) => string;

export function makeT(messages: Messages): TFunction {
  return (key, vars) => translate(messages, key, vars);
}

/** Namespaces every page's client components need (header, language menu, theme). */
export const CORE_NAMESPACES = ["meta", "nav", "theme", "language", "modes", "common", "levels", "status"] as const;

/** A subset of the catalogue, so each page only ships the strings its client components use. */
export function pickMessages(messages: Messages, namespaces: readonly string[]): Partial<Messages> {
  const out: Record<string, unknown> = {};
  for (const ns of namespaces) if (ns in messages) out[ns] = (messages as Record<string, unknown>)[ns];
  return out as Partial<Messages>;
}
