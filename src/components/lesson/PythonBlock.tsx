import { FlaskConical } from "lucide-react";
import type { TFunction } from "@/i18n/dictionary";
import { experimentStatus, getExperimentSource } from "@/lib/content";
import { highlight } from "@/lib/highlight";
import { PythonRunner } from "@/components/python/PythonRunner";
import { VerificationBadge } from "@/components/ui/Badges";

/** Remove the EXPERIMENT metadata dict from displayed/run source (it is for the test harness). */
export function stripMetadata(source: string): string {
  const lines = source.split("\n");
  const start = lines.findIndex((l) => /^EXPERIMENT\s*=\s*\{/.test(l));
  if (start < 0) return source.trim();
  let depth = 0;
  let end = start;
  for (let i = start; i < lines.length; i++) {
    for (const ch of lines[i]) {
      if (ch === "{") depth++;
      else if (ch === "}") depth--;
    }
    if (depth === 0) {
      end = i;
      break;
    }
  }
  return [...lines.slice(0, start), ...lines.slice(end + 1)].join("\n").replace(/\n{3,}/g, "\n\n").trim();
}

export async function PythonBlock({ t, id, title }: { t: TFunction; id: string; title?: string }) {
  const raw = getExperimentSource(id);
  const status = experimentStatus(id);
  if (!raw) {
    return (
      <div className="!mt-6 rounded-xl border border-dashed border-compute/40 px-5 py-4 font-sans text-sm text-muted" data-mode="C">
        Experiment <code>{id}</code> is not available yet.
      </div>
    );
  }
  const code = stripMetadata(raw);
  const html = await highlight(code, "python");
  return (
    <figure className="!mt-6 overflow-hidden rounded-xl border border-compute/25 bg-card font-sans shadow-[var(--shadow)]" data-mode="C">
      <figcaption className="flex flex-wrap items-center gap-2 border-b border-compute/20 bg-compute-soft/60 px-4 py-2.5">
        <FlaskConical size={15} className="text-compute" aria-hidden="true" />
        <span className="text-sm font-semibold text-ink">{title ?? status?.title ?? id}</span>
        <span className="text-xs text-muted">Python</span>
        <span className="ms-auto flex flex-wrap gap-1.5">
          {status?.evidence.map((e) => (
            <span key={e} className="chip">
              {t(`evidence.${e}`)}
            </span>
          ))}
          {status?.verified ? (
            <VerificationBadge label="computationally-tested" text={t("verify.computationally-tested")} />
          ) : (
            <VerificationBadge label="incomplete" text={t("verify.testsFailed")} />
          )}
        </span>
      </figcaption>
      <PythonRunner code={code} highlighted={<div dangerouslySetInnerHTML={{ __html: html }} />} />
    </figure>
  );
}
