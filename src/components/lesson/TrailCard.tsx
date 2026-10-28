import Link from "next/link";
import { ArrowRight, Sparkles } from "lucide-react";
import type { Locale } from "@/i18n/config";
import type { TFunction } from "@/i18n/dictionary";
import { getTrail, trailSlugs } from "@/lib/content";
import { href } from "@/lib/href";
import { mdInline } from "@/lib/markdown";

export function TrailCard({ locale, t, slug, compact = false }: { locale: Locale; t: TFunction; slug: string; compact?: boolean }) {
  if (!trailSlugs().includes(slug)) return null;
  const trail = getTrail(slug, locale).frontmatter;
  return (
    <Link
      href={href(locale, `math/trails/${slug}`)}
      className="group relative !mt-5 block overflow-hidden rounded-2xl border border-gold/40 bg-gradient-to-br from-gold-soft via-card to-card p-5 font-sans no-underline shadow-[var(--shadow)] transition-shadow hover:shadow-[var(--shadow-lg)]"
      style={{ textDecoration: "none" }}
    >
      <span className="pointer-events-none absolute -end-6 -top-6 h-24 w-24 rounded-full bg-gold/20 blur-2xl transition-opacity group-hover:opacity-100" aria-hidden="true" />
      <span className="flex items-center gap-2 text-xs font-bold uppercase tracking-[0.12em] text-gold-ink">
        <Sparkles size={14} aria-hidden="true" /> {t("trail.badge")} <span className="font-medium normal-case tracking-normal text-muted">· {t("trail.optional")}</span>
      </span>
      <span className="mt-2 block font-display text-xl font-semibold leading-snug text-ink">{trail.title}</span>
      {!compact && <span className="mt-1.5 block text-[0.95rem] leading-relaxed text-ink-2" dangerouslySetInnerHTML={{ __html: mdInline(trail.question) }} />}
      <span className="mt-3 inline-flex items-center gap-1.5 text-sm font-semibold text-gold-ink">
        {t("trail.begin")} <ArrowRight size={15} className="transition-transform group-hover:translate-x-0.5 rtl:rotate-180" aria-hidden="true" />
      </span>
    </Link>
  );
}
