import type { Metadata } from "next";
import Link from "next/link";
import { FlaskConical, Sparkles } from "lucide-react";
import { Messages } from "@/i18n/Messages";
import { getT, resolveLocale } from "@/i18n/server";
import { getComputeReport, getLesson, getTrailList, lessonSlugs } from "@/lib/content";
import { LEVEL_IDS, type LevelId } from "@/lib/schema";
import { highlight } from "@/lib/highlight";
import { href } from "@/lib/href";
import { PageHeader } from "@/components/ui/PageHeader";
import { PythonRunner } from "@/components/python/PythonRunner";
import { EVIDENCE_TYPES } from "@/lib/schema";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  const t = await getT(await resolveLocale(params));
  return { title: t("lab.title") };
}

const SCRATCH = `# A scratchpad with SymPy and NumPy. Try changing anything!
import sympy as sp

x = sp.symbols("x")
expr = (x + 1) ** 5
print("Expanded:", sp.expand(expr))
print("Roots of x^2 - 2:", sp.solve(x**2 - 2, x))

# Exact versus floating point
from fractions import Fraction
print("0.1 + 0.2 as floats:   ", 0.1 + 0.2)
print("1/10 + 2/10 as fractions:", Fraction(1, 10) + Fraction(2, 10))
`;

const LADDER = ["exact", "symbolic", "exhaustive-finite", "counterexample", "numerical", "experimental", "statistical", "proof"] as const;

export default async function LabPage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  const report = getComputeReport();
  const scratchHtml = await highlight(SCRATCH, "python");
  const trails = getTrailList(locale).map((x) => x.frontmatter);
  void EVIDENCE_TYPES;
  // Group experiments by the level of the first lesson (or trail) that uses them.
  const slugs = new Set(lessonSlugs());
  const levelOf = (slug: string): LevelId | undefined => (slugs.has(slug) ? getLesson(slug, locale).frontmatter.level : trails.find((tr) => tr.slug === slug)?.level);
  const byLevel = new Map<LevelId, NonNullable<typeof report>["experiments"]>();
  for (const e of report?.experiments ?? []) {
    const level = e.lessons.map(levelOf).find(Boolean) ?? "research";
    byLevel.set(level, [...(byLevel.get(level) ?? []), e]);
  }

  return (
    <Messages locale={locale} ns={["python", "exercise"]}>
    <>
      <PageHeader eyebrow={t("modes.C")} title={t("lab.title")} lead={t("lab.lead")} />
      <div className="container-page space-y-16 py-12">
        <section>
          <h2 className="text-3xl font-semibold text-ink">{t("lab.ladderTitle")}</h2>
          <p className="mt-3 max-w-3xl text-ink-2">{t("lab.ladderLead")}</p>
          <ol className="mt-6 grid gap-3 sm:grid-cols-2 lg:grid-cols-4">
            {LADDER.map((e) => (
              <li key={e} className={`rounded-xl border p-4 ${e === "proof" ? "border-formal/40 bg-formal-soft" : "border-line bg-card"}`}>
                <p className={`text-sm font-bold ${e === "proof" ? "text-formal" : "text-ink"}`}>{t(`evidence.${e}`)}</p>
                <p className="mt-1.5 text-sm leading-relaxed text-ink-2">{t(`lab.ladder.${e}`)}</p>
              </li>
            ))}
          </ol>
        </section>

        <section>
          <h2 className="text-3xl font-semibold text-ink">{t("lab.experiments")}</h2>
          {report && (
            <p className="mt-2 text-sm text-muted">
              Python {report.python} · {Object.entries(report.packages).map(([k, v]) => `${k} ${v}`).join(" · ")} · pytest: {report.pytest.passed} passed, {report.pytest.failed} failed
            </p>
          )}
          <p className="mt-3 max-w-3xl text-ink-2">{t("lab.experimentsLead")}</p>
          <div className="mt-6 space-y-10">
            {LEVEL_IDS.filter((l) => byLevel.has(l)).map((level) => (
              <div key={level}>
                <h3 className="font-display text-xl font-semibold text-ink">{t(`levels.${level}`)}</h3>
                <ul className="mt-3 grid gap-3 md:grid-cols-2">
                  {byLevel.get(level)!.map((e) => (
                    <li key={e.id}>
                      <Link prefetch={false} href={href(locale, `lab/${e.id}`)} className="card flex h-full flex-col gap-2 p-4 hover:shadow-[var(--shadow-lg)]">
                        <span className="flex items-start gap-2.5">
                          <FlaskConical size={17} className="mt-0.5 shrink-0 text-compute" aria-hidden="true" />
                          <span className="font-semibold text-ink">{e.title}</span>
                        </span>
                        <span className="flex flex-wrap gap-1.5">
                          {e.evidence.map((ev) => (
                            <span key={ev} className="chip">
                              {t(`evidence.${ev}`)}
                            </span>
                          ))}
                        </span>
                      </Link>
                    </li>
                  ))}
                </ul>
              </div>
            ))}
          </div>
        </section>

        <section>
          <h2 className="text-3xl font-semibold text-ink">{t("lab.scratch")}</h2>
          <p className="mt-2 text-ink-2">{t("lab.scratchLead")}</p>
          <div className="mt-5 overflow-hidden rounded-xl border border-compute/25 bg-card shadow-[var(--shadow)]">
            <PythonRunner code={SCRATCH} highlighted={<div dangerouslySetInnerHTML={{ __html: scratchHtml }} />} />
          </div>
        </section>

        <section>
          <h2 className="text-3xl font-semibold text-ink">{t("lab.visualTitle")}</h2>
          <ul className="mt-5 grid gap-3 sm:grid-cols-2 lg:grid-cols-4">
            {trails.map((tr) => (
              <li key={tr.slug}>
                <Link prefetch={false} href={href(locale, `math/trails/${tr.slug}`)} className="card flex h-full items-start gap-3 p-4 hover:shadow-[var(--shadow-lg)]">
                  <Sparkles size={17} className="mt-0.5 shrink-0 text-gold-ink" aria-hidden="true" />
                  <span className="font-semibold text-ink">{tr.title}</span>
                </Link>
              </li>
            ))}
          </ul>
        </section>
      </div>
    </>
    </Messages>
  );
}
