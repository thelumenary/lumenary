"use client";

import { ArrowRight } from "lucide-react";
import { useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";

const MACHINES = {
  add1: { f: (x: number) => x + 1, sym: "x + 1" },
  double: { f: (x: number) => 2 * x, sym: "2x" },
  square: { f: (x: number) => x * x, sym: "x²" },
  negate: { f: (x: number) => -x, sym: "−x" },
  sub3: { f: (x: number) => x - 3, sym: "x − 3" },
  id: { f: (x: number) => x, sym: "x" },
} as const;
type MachineId = keyof typeof MACHINES;
const fmt = (v: number) => (v < 0 ? `−${-v}` : `${v}`);

const A = ["1", "2", "3"];
const B = ["a", "b", "c"];
const C = ["★", "●"];

export function CompositionMachine() {
  const { t } = useI18n();
  const [tab, setTab] = useState<"machines" | "chains">("machines");
  return (
    <WidgetFrame title={t("w.comp.title")} subtitle={t("w.comp.subtitle")}>
      <div className="flex gap-2">
        {(["machines", "chains"] as const).map((k) => (
          <button key={k} type="button" aria-pressed={tab === k} className={`btn btn-sm ${tab === k ? "btn-primary" : "btn-ghost"}`} onClick={() => setTab(k)}>
            {t(`w.comp.tab.${k}`)}
          </button>
        ))}
      </div>
      <div className="mt-5">{tab === "machines" ? <Machines /> : <Chains />}</div>
    </WidgetFrame>
  );
}

function Machines() {
  const { t } = useI18n();
  const [first, setFirst] = useState<MachineId>("add1");
  const [second, setSecond] = useState<MachineId>("double");
  const [x, setX] = useState(3);
  const f = MACHINES[first].f;
  const g = MACHINES[second].f;
  const gf = g(f(x));
  const fg = f(g(x));
  const range = Array.from({ length: 11 }, (_, i) => i - 5);
  const agreeEverywhere = range.every((v) => g(f(v)) === f(g(v)));

  const Box = ({ id, value }: { id: MachineId; value: number }) => (
    <div className="flex flex-col items-center">
      <div className="rounded-xl border-2 border-ink bg-card px-3 py-2 text-center shadow-[var(--shadow)]">
        <p className="text-[0.7rem] font-bold uppercase tracking-wide text-muted">{t(`w.comp.machine.${id}`)}</p>
        <p className="font-serif text-lg text-ink" dir="ltr">
          x ↦ {MACHINES[id].sym}
        </p>
      </div>
      <p className="mt-1 font-mono text-sm text-ink-2" dir="ltr">
        → {fmt(value)}
      </p>
    </div>
  );

  const select = (value: MachineId, onChange: (v: MachineId) => void, label: string) => (
    <label className="block text-sm font-semibold text-ink-2">
      {label}
      <select className="input mt-1" value={value} onChange={(e) => onChange(e.target.value as MachineId)}>
        {(Object.keys(MACHINES) as MachineId[]).map((id) => (
          <option key={id} value={id}>
            {t(`w.comp.machine.${id}`)} ({MACHINES[id].sym})
          </option>
        ))}
      </select>
    </label>
  );

  return (
    <div>
      <div className="grid gap-3 sm:grid-cols-3">
        {select(first, setFirst, t("w.comp.firstF"))}
        {select(second, setSecond, t("w.comp.thenG"))}
        <label className="block text-sm font-semibold text-ink-2">
          {t("w.comp.input")} <span className="font-mono text-ink">{fmt(x)}</span>
          <input type="range" min={-5} max={5} value={x} onChange={(e) => setX(Number(e.target.value))} className="mt-3 w-full accent-[var(--gold)]" dir="ltr" />
        </label>
      </div>
      <div className="mt-5 grid gap-4 lg:grid-cols-2" dir="ltr">
        {[
          { label: "g ∘ f", steps: [first, second] as MachineId[], out: gf },
          { label: "f ∘ g", steps: [second, first] as MachineId[], out: fg },
        ].map((row) => (
          <div key={row.label} className="rounded-2xl border border-line bg-paper-2/50 p-4">
            <p className="font-serif text-lg font-semibold text-ink">
              {row.label}
              <span className="ms-2 font-sans text-xs font-medium text-muted">{row.label === "g ∘ f" ? t("w.comp.fFirst") : t("w.comp.gFirst")}</span>
            </p>
            <div className="mt-3 flex flex-wrap items-start gap-2">
              <div className="mt-3 rounded-full bg-gold-soft px-3 py-1 font-mono text-sm text-ink">{fmt(x)}</div>
              <ArrowRight size={16} className="mt-4 text-muted" />
              <Box id={row.steps[0]} value={MACHINES[row.steps[0]].f(x)} />
              <ArrowRight size={16} className="mt-4 text-muted" />
              <Box id={row.steps[1]} value={row.out} />
            </div>
          </div>
        ))}
      </div>
      <p className="mt-4 text-sm leading-relaxed text-ink-2" aria-live="polite">
        {gf === fg ? (agreeEverywhere ? t("w.comp.sameEverywhere") : t("w.comp.sameHere")) : t("w.comp.different", { a: fmt(gf), b: fmt(fg) })}
      </p>
    </div>
  );
}

function Chains() {
  const { t } = useI18n();
  const [f, setF] = useState<number[]>([0, 2, 2]);
  const [g, setG] = useState<number[]>([1, 0, 1]);
  const yA = (i: number) => 60 + i * 80;
  const yC = (k: number) => 100 + k * 80;
  const XA = 60;
  const XB = 230;
  const XC = 400;

  return (
    <div className="grid gap-5 md:grid-cols-[1.3fr_1fr]">
      <div dir="ltr">
        <svg viewBox="0 0 460 260" className="w-full" role="img" aria-label="g ∘ f">
          <defs>
            <marker id="cm-a" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">
              <path d="M0 0 10 5 0 10z" fill="var(--ink-2)" />
            </marker>
            <marker id="cm-g" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">
              <path d="M0 0 10 5 0 10z" fill="var(--gold)" />
            </marker>
          </defs>
          {[
            [XA, "A", "var(--human)"],
            [XB, "B", "var(--compute)"],
            [XC, "C", "var(--formal)"],
          ].map(([x, label, color]) => (
            <g key={label as string}>
              <rect x={(x as number) - 34} y={22} width={68} height={228} rx={34} fill="var(--paper-2)" stroke={color as string} strokeWidth="1.5" />
              <text x={x as number} y={14} textAnchor="middle" fontWeight="700" fontSize="14" fill={color as string}>
                {label}
              </text>
            </g>
          ))}
          {f.map((b, i) => (
            <line key={`f${i}`} x1={XA + 15} y1={yA(i)} x2={XB - 17} y2={yA(b)} stroke="var(--ink-2)" strokeWidth="2" markerEnd="url(#cm-a)" />
          ))}
          {g.map((c, j) => (
            <line key={`g${j}`} x1={XB + 15} y1={yA(j)} x2={XC - 17} y2={yC(c)} stroke="var(--ink-2)" strokeWidth="2" markerEnd="url(#cm-a)" />
          ))}
          {f.map((b, i) => {
            const c = g[b];
            const x1 = XA;
            const y1 = yA(i) - 15;
            const x2 = XC;
            const y2 = yC(c) - 15;
            return <path key={`gf${i}`} d={`M${x1} ${y1} C${x1 + 90} ${y1 - 70 - i * 6}, ${x2 - 90} ${y2 - 70 - i * 6}, ${x2 - 6} ${y2 - 2}`} fill="none" stroke="var(--gold)" strokeWidth="2.2" strokeDasharray="6 4" markerEnd="url(#cm-g)" opacity="0.9" />;
          })}
          {A.map((a, i) => (
            <g key={a}>
              <circle cx={XA} cy={yA(i)} r={14} fill="var(--card)" stroke="var(--human)" strokeWidth="2" />
              <text x={XA} y={yA(i) + 5} textAnchor="middle" fontWeight="700" fill="var(--ink)">
                {a}
              </text>
            </g>
          ))}
          {B.map((b, j) => (
            <g key={b}>
              <circle cx={XB} cy={yA(j)} r={14} fill="var(--card)" stroke="var(--compute)" strokeWidth="2" />
              <text x={XB} y={yA(j) + 5} textAnchor="middle" fontWeight="700" fill="var(--ink)">
                {b}
              </text>
            </g>
          ))}
          {C.map((c, k) => (
            <g key={c}>
              <circle cx={XC} cy={yC(k)} r={14} fill="var(--card)" stroke="var(--formal)" strokeWidth="2" />
              <text x={XC} y={yC(k) + 5} textAnchor="middle" fontWeight="700" fill="var(--ink)">
                {c}
              </text>
            </g>
          ))}
        </svg>
        <p className="text-center text-xs text-muted">{t("w.comp.goldIs")}</p>
      </div>
      <div className="space-y-4 text-sm">
        <div>
          <p className="mb-1.5 font-semibold text-ink-2">f : A → B</p>
          <div className="flex flex-wrap gap-2" dir="ltr">
            {A.map((a, i) => (
              <label key={a} className="flex items-center gap-1.5 font-mono">
                f({a}) =
                <select className="input w-auto py-1" value={f[i]} onChange={(e) => setF(f.map((v, k) => (k === i ? Number(e.target.value) : v)))}>
                  {B.map((b, j) => (
                    <option key={b} value={j}>
                      {b}
                    </option>
                  ))}
                </select>
              </label>
            ))}
          </div>
        </div>
        <div>
          <p className="mb-1.5 font-semibold text-ink-2">g : B → C</p>
          <div className="flex flex-wrap gap-2" dir="ltr">
            {B.map((b, j) => (
              <label key={b} className="flex items-center gap-1.5 font-mono">
                g({b}) =
                <select className="input w-auto py-1" value={g[j]} onChange={(e) => setG(g.map((v, k) => (k === j ? Number(e.target.value) : v)))}>
                  {C.map((c, k) => (
                    <option key={c} value={k}>
                      {c}
                    </option>
                  ))}
                </select>
              </label>
            ))}
          </div>
        </div>
        <table className="w-full text-center font-mono" dir="ltr">
          <thead>
            <tr className="text-xs text-muted">
              <th className="py-1">x</th>
              <th>f(x)</th>
              <th className="text-gold-ink">(g ∘ f)(x)</th>
            </tr>
          </thead>
          <tbody>
            {A.map((a, i) => (
              <tr key={a} className="border-t border-line">
                <td className="py-1.5">{a}</td>
                <td>{B[f[i]]}</td>
                <td className="font-bold text-gold-ink">{C[g[f[i]]]}</td>
              </tr>
            ))}
          </tbody>
        </table>
        <p className="leading-relaxed text-ink-2">{t("w.comp.chainNote")}</p>
      </div>
    </div>
  );
}
