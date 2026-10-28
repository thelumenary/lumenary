import type { Metadata } from "next";
import Link from "next/link";
import { ChevronDown, FlaskConical, Sparkles } from "lucide-react";
import { Messages } from "@/i18n/Messages";
import { getT, resolveLocale } from "@/i18n/server";
import { getComputeReport, getTrailList } from "@/lib/content";
import { highlight } from "@/lib/highlight";
import { href } from "@/lib/href";
import { PageHeader } from "@/components/ui/PageHeader";
import { PythonBlock } from "@/components/lesson/PythonBlock";
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
          <div className="mt-6 space-y-3">
            {(report?.experiments ?? []).map((e) => (
              <details key={e.id} className="group card overflow-hidden" id={e.id}>
                <summary className="flex cursor-pointer list-none flex-wrap items-center gap-3 px-5 py-4 [&::-webkit-details-marker]:hidden">
                  <FlaskConical size={18} className="text-compute" aria-hidden="true" />
                  <span className="font-semibold text-ink">{e.title}</span>
                  <span className="flex flex-wrap gap-1.5">
                    {e.evidence.map((ev) => (
                      <span key={ev} className="chip">
                        {t(`evidence.${ev}`)}
                      </span>
                    ))}
                  </span>
                  <ChevronDown size={18} className="ms-auto text-muted transition-transform group-open:rotate-180" aria-hidden="true" />
                </summary>
                <div className="border-t border-line px-5 pb-5">
                  <p className="pt-4 text-sm leading-relaxed text-ink-2">{e.summary}</p>
                  <PythonBlock t={t} id={e.id} />
                </div>
              </details>
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
                <Link href={href(locale, `math/trails/${tr.slug}`)} className="card flex h-full items-start gap-3 p-4 hover:shadow-[var(--shadow-lg)]">
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
