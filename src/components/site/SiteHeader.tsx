"use client";

import { Menu, X } from "lucide-react";
import Link from "next/link";
import { usePathname } from "next/navigation";
import { useEffect, useState } from "react";
import { useI18n } from "@/i18n/client";
import { href } from "@/lib/href";
import { LogoMark, Wordmark } from "@/components/brand/Logo";
import { LanguageSelector } from "./LanguageSelector";
import { CatToggle } from "./CatToggle";
import { ThemeToggle } from "./ThemeToggle";

const NAV = [
  { key: "learn", path: "math" },
  { key: "graph", path: "math/graph" },
  { key: "trails", path: "math/trails" },
  { key: "lab", path: "lab" },
  { key: "formal", path: "formal" },
  { key: "practice", path: "practice" },
  { key: "educators", path: "educators" },
  { key: "about", path: "about" },
] as const;

export function SiteHeader() {
  const { locale, t } = useI18n();
  const pathname = usePathname() ?? "";
  const [open, setOpen] = useState(false);
  const [scrolled, setScrolled] = useState(false);

  useEffect(() => setOpen(false), [pathname]);
  useEffect(() => {
    const onScroll = () => setScrolled(window.scrollY > 8);
    onScroll();
    window.addEventListener("scroll", onScroll, { passive: true });
    return () => window.removeEventListener("scroll", onScroll);
  }, []);

  const isActive = (path: string) => {
    const target = `/${locale}/${path}`;
    if (path === "math") return pathname === `${target}/` || pathname === target || pathname.startsWith(`/${locale}/math/lessons`) || pathname.startsWith(`/${locale}/math/topics`);
    return pathname.startsWith(target);
  };

  return (
    <header
      data-site-header
      className={`sticky top-0 z-40 border-b transition-colors ${scrolled ? "border-line bg-paper/85 backdrop-blur-md" : "border-transparent bg-paper/60 backdrop-blur-sm"}`}
    >
      <div className="container-page flex h-16 items-center gap-4">
        <Link href={href(locale)} className="flex shrink-0 items-center gap-2.5 text-ink" aria-label={`${t("meta.siteName")} — ${t("nav.home")}`}>
          <LogoMark size={30} />
          <Wordmark />
        </Link>
        <nav className="ms-2 hidden items-center gap-0.5 lg:flex" aria-label="Primary">
          {NAV.map((item) => (
            <Link
              key={item.key}
              href={href(locale, item.path)}
              aria-current={isActive(item.path) ? "page" : undefined}
              title={t(`nav.${item.key}`)}
              className={`whitespace-nowrap rounded-full px-3 py-1.5 text-[0.9rem] font-medium transition-colors ${
                isActive(item.path) ? "bg-ink text-paper" : "text-ink-2 hover:bg-paper-2 hover:text-ink"
              }`}
            >
              {t(`nav.short.${item.key}`)}
            </Link>
          ))}
        </nav>
        <div className="ms-auto flex items-center gap-1">
          <LanguageSelector />
          <CatToggle />
          <ThemeToggle />
          <button
            type="button"
            className="inline-flex h-9 w-9 items-center justify-center rounded-full text-ink-2 hover:bg-paper-2 lg:hidden"
            aria-expanded={open}
            aria-controls="mobile-nav"
            aria-label={open ? t("nav.close") : t("nav.menu")}
            onClick={() => setOpen((o) => !o)}
          >
            {open ? <X size={20} /> : <Menu size={20} />}
          </button>
        </div>
      </div>
      {open && (
        <nav id="mobile-nav" className="border-t border-line bg-paper lg:hidden" aria-label="Primary">
          <ul className="container-page grid grid-cols-2 gap-1 py-3 sm:grid-cols-4">
            {[...NAV, { key: "progress", path: "progress" }, { key: "languages", path: "languages" }, { key: "contribute", path: "contribute" }, { key: "verification", path: "verification" }].map((item) => (
              <li key={item.key}>
                <Link
                  href={href(locale, item.path)}
                  aria-current={isActive(item.path) ? "page" : undefined}
                  className={`block rounded-lg px-3 py-2.5 text-sm font-medium ${isActive(item.path) ? "bg-ink text-paper" : "text-ink-2 hover:bg-paper-2"}`}
                >
                  {t(`nav.${item.key}`)}
                </Link>
              </li>
            ))}
          </ul>
        </nav>
      )}
    </header>
  );
}
