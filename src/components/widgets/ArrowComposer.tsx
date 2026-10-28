"use client";

import { RotateCcw, Undo2 } from "lucide-react";
import { useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";

const OBJECTS: Record<string, string[]> = { A: ["1", "2", "3"], B: ["a", "b"], C: ["x", "y", "z"], D: ["0", "1"] };
type Arrow = { name: string; src: string; dst: string; map: Record<string, string> };
const ARROWS: Arrow[] = [
  { name: "f", src: "A", dst: "B", map: { "1": "a", "2": "b", "3": "a" } },
  { name: "g", src: "B", dst: "C", map: { a: "x", b: "z" } },
  { name: "h", src: "C", dst: "D", map: { x: "1", y: "0", z: "0" } },
  ...Object.entries(OBJECTS).map(([o, els]) => ({ name: `id_${o}`, src: o, dst: o, map: Object.fromEntries(els.map((e) => [e, e])) })),
];
const POS: Record<string, { x: number; y: number }> = { A: { x: 60, y: 70 }, B: { x: 220, y: 40 }, C: { x: 380, y: 70 }, D: { x: 520, y: 40 } };

const apply = (path: Arrow[], x: string) => path.reduce((v, a) => a.map[v], x);
const label = (path: Arrow[]) => [...path].reverse().map((a) => a.name.replace("id_", "id")).join(" ∘ ");

/** Build composites along paths in a small diagram of finite sets; compare the two bracketings of h ∘ g ∘ f. */
export function ArrowComposer() {
  const { t } = useI18n();
  const [path, setPath] = useState<Arrow[]>([]);
  const [error, setError] = useState<string | null>(null);
  const end = path.length ? path[path.length - 1].dst : null;

  const push = (a: Arrow) => {
    if (end && a.src !== end) {
      setError(t("w.cat.cannot", { last: path[path.length - 1].name, end, next: a.name, start: a.src }));
      return;
    }
    setError(null);
    setPath((p) => [...p, a]);
  };

  const f = ARROWS[0];
  const g = ARROWS[1];
  const h = ARROWS[2];

  return (
    <WidgetFrame tone="gold" title={t("w.cat.title")} subtitle={t("w.cat.subtitle")}>
      <div dir="ltr">
        <svg viewBox="0 0 580 120" className="w-full" role="img" aria-label="A → B → C → D">
          <defs>
            <marker id="ac-a" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">
              <path d="M0 0 10 5 0 10z" fill="var(--ink-2)" />
            </marker>
          </defs>
          {ARROWS.slice(0, 3).map((a) => {
            const s = POS[a.src];
            const d = POS[a.dst];
            const used = path.includes(a);
            return (
              <g key={a.name}>
                <line x1={s.x + 26} y1={s.y} x2={d.x - 28} y2={d.y} stroke={used ? "var(--gold)" : "var(--ink-2)"} strokeWidth={used ? 3.5 : 2} markerEnd="url(#ac-a)" />
                <text x={(s.x + d.x) / 2} y={(s.y + d.y) / 2 - 10} textAnchor="middle" fontStyle="italic" fontFamily="var(--font-serif)" fontSize="18" fill="var(--ink)">
                  {a.name}
                </text>
              </g>
            );
          })}
          {Object.keys(OBJECTS).map((o) => (
            <g key={o}>
              <path d={`M${POS[o].x - 10} ${POS[o].y + 22} C${POS[o].x - 30} ${POS[o].y + 62}, ${POS[o].x + 30} ${POS[o].y + 62}, ${POS[o].x + 10} ${POS[o].y + 22}`} fill="none" stroke="var(--line-2)" strokeWidth="1.5" markerEnd="url(#ac-a)" />
              <circle cx={POS[o].x} cy={POS[o].y} r={24} fill={end === o ? "var(--gold-soft)" : "var(--card)"} stroke={end === o ? "var(--gold)" : "var(--ink-2)"} strokeWidth="2" />
              <text x={POS[o].x} y={POS[o].y + 6} textAnchor="middle" fontWeight="700" fontSize="17" fill="var(--ink)">
                {o}
              </text>
              <text x={POS[o].x} y={POS[o].y + 74} textAnchor="middle" fontSize="11" fill="var(--muted)">
                id{o}
              </text>
            </g>
          ))}
        </svg>
      </div>
      <div className="mt-2 flex flex-wrap gap-1.5" dir="ltr">
        {ARROWS.map((a) => (
          <button key={a.name} type="button" className="btn btn-sm btn-ghost font-serif italic" onClick={() => push(a)}>
            {a.name.replace("id_", "id")} : {a.src} → {a.dst}
          </button>
        ))}
        <button type="button" className="btn btn-sm btn-ghost ms-auto" disabled={!path.length} onClick={() => setPath((p) => p.slice(0, -1))} aria-label={t("w.common.undo")}>
          <Undo2 size={14} />
        </button>
        <button type="button" className="btn btn-sm btn-ghost" disabled={!path.length} onClick={() => (setPath([]), setError(null))} aria-label={t("w.common.reset")}>
          <RotateCcw size={14} />
        </button>
      </div>
      <div className="mt-4 grid gap-4 md:grid-cols-2" aria-live="polite">
        <div className="rounded-xl border border-line bg-card p-4">
          <p className="text-xs font-semibold uppercase tracking-wide text-muted">{t("w.cat.yourPath")}</p>
          {path.length === 0 ? (
            <p className="mt-2 text-sm text-ink-2">{t("w.cat.start")}</p>
          ) : (
            <>
              <p className="mt-1 font-serif text-xl text-ink" dir="ltr">
                {label(path)} : {path[0].src} → {end}
              </p>
              <table className="mt-2 font-mono text-sm" dir="ltr">
                <tbody>
                  {OBJECTS[path[0].src].map((x) => (
                    <tr key={x}>
                      <td className="pe-3 text-ink-2">{x}</td>
                      <td className="pe-3 text-muted">↦</td>
                      <td className="font-bold text-gold-ink">{apply(path, x)}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </>
          )}
          {error && <p className="mt-2 rounded-lg bg-warn-soft px-3 py-2 text-sm text-warn">{error}</p>}
        </div>
        <div className="rounded-xl border border-line bg-card p-4">
          <p className="text-xs font-semibold uppercase tracking-wide text-muted">{t("w.cat.brackets")}</p>
          <table className="mt-2 w-full text-center font-mono text-sm" dir="ltr">
            <thead>
              <tr className="text-xs text-muted">
                <th className="py-1">x</th>
                <th>(g∘f)(x)</th>
                <th>h((g∘f)(x))</th>
                <th>(h∘g)(f(x))</th>
              </tr>
            </thead>
            <tbody>
              {OBJECTS.A.map((x) => {
                const gf = g.map[f.map[x]];
                return (
                  <tr key={x} className="border-t border-line">
                    <td className="py-1.5">{x}</td>
                    <td>{gf}</td>
                    <td className="font-bold text-gold-ink">{h.map[gf]}</td>
                    <td className="font-bold text-gold-ink">{h.map[g.map[f.map[x]]]}</td>
                  </tr>
                );
              })}
            </tbody>
          </table>
          <p className="mt-2 text-sm text-ink-2">{t("w.cat.same")}</p>
        </div>
      </div>
    </WidgetFrame>
  );
}
