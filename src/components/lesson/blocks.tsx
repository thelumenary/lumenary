import { ChevronDown, Heart, Users } from "lucide-react";
import type { TFunction } from "@/i18n/dictionary";
import { NarratorAvatar, type NarratorId } from "@/components/brand/Narrators";
import { ModeBadge } from "@/components/ui/ModeBadge";
import { LENSES, SECTION_KINDS, type Lens, type SectionKind } from "./kinds";

type P = { children?: React.ReactNode };

export function makeBlocks(t: TFunction) {
  function Section({ id, kind, title, children }: P & { id: string; kind: SectionKind; title: string }) {
    const meta = SECTION_KINDS[kind] ?? SECTION_KINDS.human;
    const { Icon } = meta;
    return (
      <section id={id} data-kind={kind} {...(meta.mode ? { "data-mode": meta.mode } : {})} className="scroll-mt-24 border-t border-line py-12 first:border-t-0 first:pt-2">
        <div className="mb-3 flex flex-wrap items-center gap-2.5">
          <span className={`inline-flex items-center gap-1.5 text-xs font-bold uppercase tracking-[0.12em] ${kind === "trails" ? "text-gold-ink" : "text-muted"}`}>
            <Icon size={14} aria-hidden="true" />
            {t(`sections.${kind}`)}
          </span>
          {meta.mode && <ModeBadge mode={meta.mode} label={t(`modes.${meta.mode}`)} compact />}
        </div>
        <h2 className="text-[1.85rem] font-semibold leading-tight text-ink">{title}</h2>
        <div className="prose-lumen mt-6">{children}</div>
      </section>
    );
  }

  const NARRATOR_MODE = { chloe: "H", margaret: "C", gideon: "F" } as const;
  const NARRATOR_BG = { chloe: "bg-human-soft", margaret: "bg-compute-soft", gideon: "bg-formal-soft" } as const;
  const NARRATOR_FG = { chloe: "text-human", margaret: "text-compute", gideon: "text-formal" } as const;

  function Narrator({ who, children }: P & { who: NarratorId }) {
    return (
      <aside className="!mt-7 flex items-start gap-3.5" data-mode={NARRATOR_MODE[who]}>
        <NarratorAvatar who={who} size={46} className="mt-1 shrink-0" />
        <div className={`relative min-w-0 flex-1 rounded-2xl rounded-ss-md px-4 py-3 font-sans text-[0.98rem] leading-relaxed text-ink ${NARRATOR_BG[who]}`}>
          <p className={`text-xs font-bold ${NARRATOR_FG[who]}`}>
            {t(`narrators.${who}`)} <span className="font-medium opacity-80">· {t(`narrators.${who}Role`)}</span>
          </p>
          <div className="mt-1 [&>p]:m-0 [&>p+p]:mt-2">{children}</div>
        </div>
      </aside>
    );
  }

  function Box({ label, tone, children, title }: P & { label: string; tone: string; title?: string }) {
    return (
      <div className={`!mt-6 rounded-xl border-s-4 px-5 py-4 ${tone}`}>
        <p className="font-sans text-xs font-bold uppercase tracking-[0.1em] opacity-90">
          {label}
          {title && <span className="ms-1.5 normal-case tracking-normal">— {title}</span>}
        </p>
        <div className="mt-2 text-ink [&>*+*]:mt-3">{children}</div>
      </div>
    );
  }

  return {
    Section,
    Narrator,
    Definition: ({ term, children }: P & { term?: string }) => (
      <Box label={t("blocks.definition")} title={term} tone="border-sky bg-sky-soft/70 text-sky-ink">
        {children}
      </Box>
    ),
    Theorem: ({ name, children }: P & { name?: string }) => (
      <Box label={t("blocks.theorem")} title={name} tone="border-ink bg-paper-2 text-ink">
        {children}
      </Box>
    ),
    Proof: ({ children }: P) => (
      <div className="!mt-4 border-s border-line-2 ps-5">
        <p className="font-sans text-xs font-bold uppercase tracking-[0.1em] text-muted">{t("blocks.proof")}</p>
        <div className="mt-2 [&>*+*]:mt-3">{children}</div>
        <p className="mt-1 text-end text-ink" aria-label="end of proof">
          {t("blocks.qed")}
        </p>
      </div>
    ),
    Example: ({ title, children }: P & { title?: string }) => (
      <Box label={t("blocks.example")} title={title} tone="border-line-2 bg-card text-ink-2">
        {children}
      </Box>
    ),
    Misconception: ({ children }: P) => (
      <Box label={t("blocks.misconception")} tone="border-warn bg-warn-soft/70 text-warn">
        {children}
      </Box>
    ),
    Note: ({ children }: P) => (
      <Box label={t("blocks.note")} tone="border-line-2 bg-paper-2/70 text-muted">
        {children}
      </Box>
    ),
    Analogy: ({ children }: P) => (
      <div className="!mt-6 rounded-xl border border-dashed border-gold/60 px-5 py-4">
        <p className="font-sans text-xs font-bold uppercase tracking-[0.1em] text-gold-ink">{t("blocks.analogy")}</p>
        <div className="mt-2 [&>*+*]:mt-3">{children}</div>
      </div>
    ),
    Reflection: ({ children, title }: P & { title?: string }) => (
      <details className="group !mt-8 rounded-xl border border-line bg-paper-2/50 font-sans" data-reflection>
        <summary className="flex cursor-pointer list-none items-center gap-3 px-5 py-3.5 text-sm [&::-webkit-details-marker]:hidden">
          <Heart size={16} className="shrink-0 text-human" aria-hidden="true" />
          <span className="flex-1">
            <span className="font-semibold text-ink">{t("blocks.reflection")}</span>
            {title && <span className="text-muted"> · {title}</span>}
          </span>
          <ChevronDown size={16} className="text-muted transition-transform group-open:rotate-180" aria-hidden="true" />
        </summary>
        <div className="border-t border-line px-5 py-4 font-serif text-[1.02rem] leading-relaxed text-ink-2">
          <p className="mb-3 font-sans text-xs text-muted">{t("blocks.reflectionNote")}</p>
          <div className="[&>*+*]:mt-3">{children}</div>
        </div>
      </details>
    ),
    Viewpoint: ({ lens, title, children }: P & { lens: Lens; title?: string }) => {
      const { Icon } = LENSES[lens] ?? LENSES.sets;
      return (
        <div className="!mt-6 rounded-xl border border-line bg-card px-5 py-4" data-lens={lens}>
          <p className="flex flex-wrap items-center gap-2 font-sans text-xs font-bold uppercase tracking-[0.1em] text-sky-ink">
            <Icon size={15} aria-hidden="true" />
            {t(`lenses.${lens}`)}
            {title && <span className="normal-case tracking-normal text-ink-2">— {title}</span>}
          </p>
          <div className="mt-2 text-ink [&>*+*]:mt-3">{children}</div>
        </div>
      );
    },
    /** A typeset formula (see src/lib/rehype-katex-html.ts): KaTeX's own HTML, as one string. */
    KatexHtml: ({ className, html }: { className: string; html: string }) => <span className={className} dangerouslySetInnerHTML={{ __html: html }} />,
    Figure: ({ caption, children }: P & { caption?: string }) => (
      <figure className="not-prose !mt-7 rounded-xl border border-line bg-card px-4 py-4 text-ink">
        <div className="flex justify-center [&_svg]:h-auto [&_svg]:max-w-full" dir="ltr">
          {children}
        </div>
        {caption && <figcaption className="mt-3 text-center font-sans text-sm leading-snug text-muted">{caption}</figcaption>}
      </figure>
    ),
    ForGrownUps: ({ children, title }: P & { title?: string }) => (
      <details className="group !mt-6 rounded-xl border border-line bg-card font-sans">
        <summary className="flex cursor-pointer list-none items-center gap-3 px-5 py-3.5 text-sm [&::-webkit-details-marker]:hidden">
          <Users size={16} className="shrink-0 text-muted" aria-hidden="true" />
          <span className="flex-1 font-semibold text-ink">
            {t("blocks.forGrownUps")}
            {title && <span className="font-normal text-muted"> · {title}</span>}
          </span>
          <ChevronDown size={16} className="text-muted transition-transform group-open:rotate-180" aria-hidden="true" />
        </summary>
        <div className="prose-lumen border-t border-line px-5 py-4 text-[1rem]">{children}</div>
      </details>
    ),
  };
}
