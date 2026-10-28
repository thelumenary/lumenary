import Link from "next/link";
import type { Locale } from "@/i18n/config";
import type { TFunction } from "@/i18n/dictionary";
import { href } from "@/lib/href";
import { LogoMark, Wordmark } from "@/components/brand/Logo";

export function SiteFooter({ locale, t }: { locale: Locale; t: TFunction }) {
  const learn = [
    ["learn", "math"],
    ["graph", "math/graph"],
    ["trails", "math/trails"],
    ["lab", "lab"],
    ["formal", "formal"],
    ["practice", "practice"],
  ];
  const project = [
    ["about", "about"],
    ["educators", "educators"],
    ["contribute", "contribute"],
    ["languages", "languages"],
    ["verification", "verification"],
    ["progress", "progress"],
  ];
  return (
    <footer data-site-footer className="mt-24 border-t border-line bg-paper-2/60">
      <div className="container-page grid gap-10 py-14 md:grid-cols-[1.4fr_1fr_1fr]">
        <div className="max-w-sm">
          <div className="flex items-center gap-2.5">
            <LogoMark size={28} />
            <Wordmark />
          </div>
          <p className="mt-4 text-sm leading-relaxed text-ink-2">{t("footer.mission")}</p>
          <p className="mt-4 font-display text-lg italic text-ink">{t("meta.tagline")}</p>
          <p className="mt-1 text-sm font-semibold tracking-wide text-gold-ink">{t("footer.motto")}</p>
        </div>
        {[
          [t("footer.learn"), learn],
          [t("footer.project"), project],
        ].map(([title, links]) => (
          <div key={title as string}>
            <h2 className="eyebrow">{title as string}</h2>
            <ul className="mt-4 space-y-2.5">
              {(links as string[][]).map(([key, path]) => (
                <li key={key}>
                  <Link href={href(locale, path)} className="text-sm text-ink-2 hover:text-ink hover:underline">
                    {t(`nav.${key}`)}
                  </Link>
                </li>
              ))}
            </ul>
          </div>
        ))}
      </div>
      <div className="border-t border-line">
        <div className="container-page flex flex-col gap-2 py-5 text-xs text-muted sm:flex-row sm:justify-between">
          <span>{t("footer.license")}</span>
          <span>{t("footer.noEndorsement")}</span>
        </div>
      </div>
    </footer>
  );
}
