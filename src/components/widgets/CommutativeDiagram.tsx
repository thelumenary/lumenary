import { Fragment } from "react";
import katex from "katex";
import { describeDiagram, layoutDiagram, normaliseDiagram, type DiagramSize } from "./lib/diagram-core";
import { KATEX_MACROS } from "@/lib/katex-macros";

/** KaTeX output is generated and escaped by KaTeX itself (trust disabled), never raw author HTML. */
function texHtml(tex: string): string {
  return katex.renderToString(tex, { throwOnError: false, output: "htmlAndMathml", macros: { ...KATEX_MACROS }, strict: "ignore", trust: false, maxExpand: 300, maxSize: 8 });
}

function Caption({ text }: { text: string }) {
  const parts = text.split(/(\$[^$]+\$)/g);
  return (
    <>
      {parts.map((p, i) =>
        p.length > 2 && p.startsWith("$") && p.endsWith("$") ? <span key={i} dangerouslySetInnerHTML={{ __html: texHtml(p.slice(1, -1)) }} /> : <Fragment key={i}>{p}</Fragment>,
      )}
    </>
  );
}

export interface CommutativeDiagramProps {
  objects?: unknown;
  arrows?: unknown;
  caption?: string;
  size?: DiagramSize;
  /** Optional hand-written description that replaces the generated aria-label. */
  ariaLabel?: string;
}

/**
 * Commutative diagrams for category theory, algebra and topology lessons.
 * A server component: the diagram is laid out and typeset at build time, so it
 * costs no client JavaScript. Labels are KaTeX inside <foreignObject>.
 */
export function CommutativeDiagram({ objects, arrows, caption, size, ariaLabel }: CommutativeDiagramProps) {
  const norm = normaliseDiagram(objects, arrows);
  const sz: DiagramSize = size === "sm" || size === "lg" ? size : "md";
  const L = layoutDiagram(norm.objects, norm.arrows, sz);
  const k = L.font / 17;
  const vb = L.viewBox;
  const label = (typeof ariaLabel === "string" && ariaLabel.trim()) || describeDiagram(norm.objects, norm.arrows);

  const box = (tex: string, cx: number, cy: number, hw: number, hh: number, font: number, key: string) => {
    const w = 2 * hw + 48;
    const h = 2 * hh + 24;
    return (
      <foreignObject key={key} x={cx - w / 2} y={cy - h / 2} width={w} height={h} style={{ overflow: "visible" }}>
        <div
          style={{ width: "100%", height: "100%", display: "flex", alignItems: "center", justifyContent: "center", fontSize: `${font}px`, lineHeight: 1.2, whiteSpace: "nowrap", color: "currentColor" }}
          dangerouslySetInnerHTML={{ __html: texHtml(tex) }}
        />
      </foreignObject>
    );
  };

  return (
    <figure className="not-prose !mt-7 mb-2 flex flex-col items-center font-sans">
      <div dir="ltr" className="max-w-full overflow-x-auto px-1">
        <svg
          viewBox={`${vb.x.toFixed(2)} ${vb.y.toFixed(2)} ${vb.w.toFixed(2)} ${vb.h.toFixed(2)}`}
          width={Math.round(vb.w)}
          height={Math.round(vb.h)}
          role="img"
          aria-label={label}
          className="block h-auto max-w-full text-ink"
          style={{ minWidth: Math.min(Math.round(vb.w), 240) }}
        >
          <g fill="none" stroke="currentColor" strokeWidth={1.15 * k} strokeLinecap="round" strokeLinejoin="round">
            {L.arrows.map((s, i) => (
              <g key={i}>
                {s.shafts.map((d, j) => (
                  <path key={j} d={d} strokeDasharray={s.arrow.style === "dashed" ? `${(4.5 * k).toFixed(2)} ${(3.2 * k).toFixed(2)}` : undefined} />
                ))}
                {s.hook && <path d={s.hook} />}
                {s.heads.map((d, j) => (
                  <path key={`h${j}`} d={d} />
                ))}
              </g>
            ))}
          </g>
          {L.arrows.map((s, i) =>
            s.iso ? (
              <text key={`iso${i}`} x={s.iso.x} y={s.iso.y} textAnchor="middle" dominantBaseline="central" fontSize={L.labelFont * 1.1} fill="currentColor" className="font-serif">
                ≅
              </text>
            ) : null,
          )}
          {L.nodes.map((n) => box(n.tex, n.cx, n.cy, n.hw, n.hh, L.font, `n-${n.id}`))}
          {L.arrows.map((s, i) => (s.label ? box(s.label.tex, s.label.cx, s.label.cy, s.label.hw, s.label.hh, L.labelFont, `l-${i}`) : null))}
        </svg>
      </div>
      {norm.ignored > 0 && (
        <p className="mt-1 text-xs text-warn" dir="ltr">
          {norm.ignored} malformed object(s) or arrow(s) skipped — check ids, rows and columns.
        </p>
      )}
      {caption && (
        <figcaption className="mt-2 max-w-prose text-center text-sm leading-snug text-muted">
          <Caption text={caption} />
        </figcaption>
      )}
    </figure>
  );
}
