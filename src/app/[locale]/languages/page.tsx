import type { Metadata } from "next";
import { Messages } from "@/i18n/Messages";
import { getT, resolveLocale } from "@/i18n/server";
import { LOCALES, LOCALE_META } from "@/i18n/config";
import { getCountries, getLanguages } from "@/lib/content";
import { PageHeader } from "@/components/ui/PageHeader";
import { LanguageTable } from "@/components/registry/LanguageTable";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  const t = await getT(await resolveLocale(params));
  return { title: t("languages.title") };
}

const REGIONS = ["Africa", "Americas", "Asia", "Europe", "Oceania"] as const;

export default async function LanguagesPage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  const languages = getLanguages();
  const countries = getCountries();
  const langName = new Map((languages?.languages ?? []).map((l) => [l.tag, l.name]));
  const sample = 1234567.89;

  return (
    <Messages locale={locale} ns={["languages"]}>
    <>
      <PageHeader eyebrow={t("nav.languages")} title={t("languages.title")} lead={t("languages.lead")} />
      <div className="container-page space-y-16 py-12">
        {languages && (
          <section>
            <LanguageTable
              rows={languages.languages.map((l) => ({
                tag: l.tag,
                name: l.name,
                nativeName: l.nativeName,
                script: l.script,
                direction: l.direction,
                inclusion: l.inclusion,
                translationStatus: l.translationStatus,
                reviewStatus: l.reviewStatus,
                regions: l.regions,
                variantOf: l.variantOf,
              }))}
            />
            <details className="mt-4 rounded-xl border border-line bg-card px-5 py-4 text-sm text-ink-2">
              <summary className="cursor-pointer font-semibold text-ink">{t("languages.methodology")}</summary>
              <p className="mt-3 leading-relaxed">{languages.methodology}</p>
            </details>
          </section>
        )}

        <section>
          <h2 className="text-3xl font-semibold text-ink">{t("languages.numeralsTitle")}</h2>
          <p className="mt-2 max-w-3xl text-ink-2">{t("languages.numeralsLead")}</p>
          <div className="mt-5 grid gap-3 sm:grid-cols-2 lg:grid-cols-3">
            {LOCALES.map((l) => {
              const meta = LOCALE_META[l];
              return (
                <div key={l} className="card p-4" lang={l} dir={meta.dir}>
                  <p className="font-semibold text-ink">{meta.nativeName}</p>
                  <p className="mt-1 text-xs text-muted" lang="en" dir="ltr">
                    {meta.family} · {meta.script} · {meta.dir.toUpperCase()}
                  </p>
                  <p className="mt-3 font-mono text-lg text-ink">{new Intl.NumberFormat(meta.intl).format(sample)}</p>
                  {l === "ar" && <p className="mt-1 font-mono text-lg text-ink">{new Intl.NumberFormat("ar-u-nu-arab").format(sample)}</p>}
                  {l === "hi" && <p className="mt-1 font-mono text-lg text-ink">{new Intl.NumberFormat("hi-u-nu-deva").format(sample)}</p>}
                </div>
              );
            })}
          </div>
        </section>

        {countries && (
          <section>
            <h2 className="text-3xl font-semibold text-ink">{t("languages.countriesTitle")}</h2>
            <p className="mt-2 max-w-3xl text-ink-2">{t("languages.countriesLead")}</p>
            <p className="mt-2 text-sm text-muted">
              {t("languages.countSummary", {
                members: countries.countries.filter((c) => c.status === "un-member").length,
                observers: countries.countries.filter((c) => c.status === "un-observer").length,
                other: countries.countries.filter((c) => c.status === "territory" || c.status === "other").length,
                review: countries.countries.filter((c) => c.needsReview).length,
              })}
            </p>
            <div className="mt-5 space-y-3">
              {REGIONS.map((region) => {
                const list = countries.countries.filter((c) => c.region === region).sort((a, b) => a.name.localeCompare(b.name));
                return (
                  <details key={region} className="group rounded-xl border border-line bg-card">
                    <summary className="cursor-pointer px-5 py-3.5 font-semibold text-ink">
                      {region} <span className="font-normal text-muted">· {list.length}</span>
                    </summary>
                    <div className="overflow-x-auto border-t border-line">
                      <table className="w-full min-w-[40rem] text-sm">
                        <tbody>
                          {list.map((c) => (
                            <tr key={c.iso2} className="border-t border-line first:border-t-0 align-top">
                              <td className="px-4 py-2 font-semibold text-ink">
                                {c.name} <span className="font-mono text-xs font-normal text-muted">{c.iso2}</span>
                                {c.needsReview && <span className="ms-2 rounded-full bg-warn-soft px-2 py-0.5 text-[0.7rem] font-semibold text-warn">{t("languages.needsReview")}</span>}
                              </td>
                              <td className="px-4 py-2 text-xs text-muted">{c.subregion}</td>
                              <td className="px-4 py-2 text-ink-2">
                                {c.officialLanguages.length ? c.officialLanguages.map((x) => langName.get(x) ?? x).join(", ") : <em className="text-muted">{t("languages.noOfficial")} — {c.deFactoLanguages.map((x) => langName.get(x) ?? x).join(", ")}</em>}
                              </td>
                            </tr>
                          ))}
                        </tbody>
                      </table>
                    </div>
                  </details>
                );
              })}
            </div>
          </section>
        )}
      </div>
    </>
    </Messages>
  );
}
