"use client";

import { Check, Globe } from "lucide-react";
import Link from "next/link";
import { usePathname } from "next/navigation";
import { useEffect, useId, useRef, useState } from "react";
import { LOCALES, LOCALE_META, type Locale } from "@/i18n/config";
import { useI18n } from "@/i18n/client";
import { href, pageLocale } from "@/lib/href";

const STATUS: Record<Locale, "canonical" | "machine-draft"> = {
  en: "canonical",
  es: "machine-draft",
  ar: "machine-draft",
  hi: "machine-draft",
  "zh-Hans": "machine-draft",
  sw: "machine-draft",
};

/** For a page that does not exist in locale `l` (an untranslated lesson, a lab detail page), the nearest page that does. */
function sectionHref(l: Locale, rest: string): string {
  if (rest.startsWith("math/lessons/")) return href(l, "math");
  return href(l, rest.split("/")[0]);
}

export function LanguageSelector() {
  const { locale, t } = useI18n();
  const pathname = usePathname() ?? `/${locale}/`;
  const [open, setOpen] = useState(false);
  const ref = useRef<HTMLDivElement>(null);
  const menuId = useId();

  useEffect(() => {
    if (!open) return;
    const onDown = (e: MouseEvent) => {
      if (ref.current && !ref.current.contains(e.target as Node)) setOpen(false);
    };
    const onKey = (e: KeyboardEvent) => e.key === "Escape" && setOpen(false);
    document.addEventListener("mousedown", onDown);
    document.addEventListener("keydown", onKey);
    return () => {
      document.removeEventListener("mousedown", onDown);
      document.removeEventListener("keydown", onKey);
    };
  }, [open]);

  const rest = pathname.split("/").slice(2).join("/");
  const remember = (l: Locale) => {
    try {
      localStorage.setItem("lumenary:locale", l);
    } catch {}
  };

  return (
    <div className="relative" ref={ref}>
      <button
        type="button"
        className="inline-flex h-9 items-center gap-1.5 rounded-full px-2.5 text-sm font-medium text-ink-2 hover:bg-paper-2 hover:text-ink"
        aria-haspopup="true"
        aria-expanded={open}
        aria-controls={menuId}
        aria-label={t("language.choose")}
        onClick={() => setOpen((o) => !o)}
      >
        <Globe size={17} aria-hidden="true" />
        <span lang={locale}>{LOCALE_META[locale].nativeName}</span>
      </button>
      {open && (
        <div id={menuId} className="card absolute end-0 top-11 z-50 w-72 p-2 animate-float-up" role="menu">
          <p className="px-2.5 pb-2 pt-1 text-xs leading-relaxed text-muted">{t("language.demoNote")}</p>
          <ul>
            {LOCALES.map((l) => (
              <li key={l}>
                <Link
                  role="menuitem"
                  href={pageLocale(l, rest) === l ? `/${l}/${rest}` : sectionHref(l, rest)}
                  hrefLang={l}
                  lang={l}
                  onClick={() => {
                    remember(l);
                    setOpen(false);
                  }}
                  className={`flex items-center justify-between gap-3 rounded-lg px-2.5 py-2 text-sm hover:bg-paper-2 ${l === locale ? "bg-paper-2" : ""}`}
                >
                  <span className="flex flex-col">
                    <span className="font-semibold text-ink">{LOCALE_META[l].nativeName}</span>
                    <span className="text-xs text-muted" lang={locale}>
                      {LOCALE_META[l].name} · {t(`language.status.${STATUS[l]}`)}
                    </span>
                  </span>
                  {l === locale && <Check size={16} className="text-good" aria-hidden="true" />}
                </Link>
              </li>
            ))}
          </ul>
          <Link href={href(locale, "languages")} className="link mt-1 block px-2.5 py-2 text-xs" onClick={() => setOpen(false)}>
            {t("language.allLanguages")} →
          </Link>
        </div>
      )}
    </div>
  );
}
