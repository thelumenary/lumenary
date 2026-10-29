import type { Metadata } from "next";
import fs from "node:fs";
import path from "node:path";
import Link from "next/link";
import { AlertTriangle, CheckCircle2, ShieldCheck, FlaskConical, ListChecks, UserX, XCircle } from "lucide-react";
import { getT, resolveLocale } from "@/i18n/server";
import { getComputeReport, getLeanReport, lessonSlugs, ROOT, trailSlugs } from "@/lib/content";
import { href } from "@/lib/href";
import { PageHeader } from "@/components/ui/PageHeader";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  const t = await getT(await resolveLocale(params));
  return { title: t("verification.title") };
}

interface VitestSummary {
  numPassedTests: number;
  numFailedTests: number;
  startTime: number;
}

function readE2e(): { passed: number; failed: number; generatedAt: string } | null {
  const p = path.join(ROOT, "content/verification/e2e-report.json");
  if (!fs.existsSync(p)) return null;
  try {
    return JSON.parse(fs.readFileSync(p, "utf8"));
  } catch {
    return null;
  }
}

function readVitest(): VitestSummary | null {
  const p = path.join(ROOT, "content/verification/vitest-report.json");
  if (!fs.existsSync(p)) return null;
  try {
    return JSON.parse(fs.readFileSync(p, "utf8")) as VitestSummary;
  } catch {
    return null;
  }
}

export default async function VerificationPage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  const lean = getLeanReport();
  const compute = getComputeReport();
  const vitest = readVitest();
  const e2e = readE2e();
  const Card = ({ Icon, title, ok, children }: { Icon: typeof ShieldCheck; title: string; ok: boolean | null; children: React.ReactNode }) => (
    <section className="card p-6">
      <div className="flex items-center gap-3">
        <Icon size={20} className="text-ink-2" aria-hidden="true" />
        <h2 className="text-xl font-semibold text-ink">{title}</h2>
        <span className="ms-auto">{ok === null ? <AlertTriangle size={18} className="text-warn" /> : ok ? <CheckCircle2 size={18} className="text-good" /> : <XCircle size={18} className="text-bad" />}</span>
      </div>
      <div className="mt-3 text-sm leading-relaxed text-ink-2">{children}</div>
    </section>
  );
  const count = (k: "library" | "independent" | "definition") => lean?.declarations.filter((d) => d.provenance === k).length ?? 0;

  return (
    <>
      <PageHeader title={t("verification.title")} lead={t("verification.lead")} />
      <div className="container-page space-y-6 py-12">
        <div className="grid gap-5 lg:grid-cols-2">
          <Card Icon={ShieldCheck} title={t("verification.lean")} ok={lean ? lean.build.success : null}>
            {lean ? (
              <>
                <p>
                  {t("verification.leanSummary", {
                    n: lean.declarations.length,
                    toolchain: lean.toolchain,
                    sorry: lean.declarations.filter((d) => d.usesSorry).length,
                    library: count("library"),
                    independent: count("independent"),
                    definition: count("definition"),
                  })}
                </p>
                <p className="mt-2 text-xs text-muted">{t("verification.generated", { date: lean.generatedAt.slice(0, 16).replace("T", " ") })}</p>
                <Link href={href(locale, "formal")} className="link mt-2 inline-block">
                  {t("nav.formal")} →
                </Link>
              </>
            ) : (
              t("verification.notRun")
            )}
          </Card>
          <Card Icon={FlaskConical} title={t("verification.compute")} ok={compute ? compute.pytest.failed === 0 && compute.experiments.every((e) => e.ran && e.testsPassed) : null}>
            {compute ? (
              <>
                <p>
                  {t("verification.computeSummary", {
                    passed: compute.experiments.filter((e) => e.ran && e.testsPassed).length,
                    total: compute.experiments.length,
                    tests: compute.pytest.passed,
                    failed: compute.pytest.failed,
                  })}
                </p>
                <p className="mt-2 text-xs text-muted">
                  Python {compute.python} · {Object.entries(compute.packages).map(([k, v]) => `${k} ${v}`).join(" · ")} · {t("verification.generated", { date: compute.generatedAt.slice(0, 16).replace("T", " ") })}
                </p>
              </>
            ) : (
              t("verification.notRun")
            )}
          </Card>
          <Card Icon={ListChecks} title={t("verification.content")} ok={vitest ? vitest.numFailedTests === 0 : null}>
            {vitest ? (
              <>
                <p>{t("verification.contentSummary", { passed: vitest.numPassedTests, failed: vitest.numFailedTests })}</p>
                {e2e && <p className="mt-2">{t("verification.e2eSummary", { passed: e2e.passed, failed: e2e.failed })}</p>}
                <p className="mt-2 text-xs text-muted">{t("verification.generated", { date: new Date(vitest.startTime).toISOString().slice(0, 16).replace("T", " ") })}</p>
              </>
            ) : (
              t("verification.notRun")
            )}
          </Card>
          <Card Icon={UserX} title={t("verification.human")} ok={null}>
            {t("verification.humanText")}
          </Card>
        </div>

        {compute && (
          <section className="card overflow-hidden">
            <table className="w-full text-sm">
              <thead className="bg-paper-2 text-ink-2">
                <tr>
                  <th className="px-4 py-2.5 text-start font-semibold">{t("verification.experiment")}</th>
                  <th className="px-4 py-2.5 text-start font-semibold">{t("verification.evidenceCol")}</th>
                  <th className="px-4 py-2.5 text-start font-semibold">{t("verification.statusCol")}</th>
                </tr>
              </thead>
              <tbody>
                {compute.experiments.map((e) => (
                  <tr key={e.id} className="border-t border-line">
                    <td className="px-4 py-2">
                      <Link href={`${href(locale, "lab")}#${e.id}`} className="font-semibold text-ink hover:underline">
                        {e.title}
                      </Link>
                    </td>
                    <td className="px-4 py-2 text-xs text-ink-2">{e.evidence.map((x) => t(`evidence.${x}`)).join(", ")}</td>
                    <td className={`px-4 py-2 text-xs font-semibold ${e.ran && e.testsPassed ? "text-good" : "text-bad"}`}>{e.ran && e.testsPassed ? t("verification.passed") : t("verification.failed")}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </section>
        )}

        <div className="grid gap-5 lg:grid-cols-2">
          <section className="card p-6">
            <h2 className="text-xl font-semibold text-ink">{t("verification.limitations")}</h2>
            <ul className="prose-ui mt-3 text-sm">
              {[1, 2, 3, 4, 5].map((i) => (
                <li key={i}>{t(`verification.limitationsList.l${i}`, { lessons: lessonSlugs().length, trails: trailSlugs().length })}</li>
              ))}
            </ul>
          </section>
          <section className="card p-6">
            <h2 className="text-xl font-semibold text-ink">{t("verification.needsReview")}</h2>
            <ol className="prose-ui mt-3 text-sm">
              {[1, 2, 3, 4, 5, 6].map((i) => (
                <li key={i}>{t(`verification.reviewList.r${i}`)}</li>
              ))}
            </ol>
          </section>
        </div>
      </div>
    </>
  );
}
