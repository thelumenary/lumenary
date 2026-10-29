"use client";

import { ArrowLeftRight, Play, RotateCcw } from "lucide-react";
import { useEffect, useRef, useState, type ReactNode } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { toNumber } from "./lib/expr";
import { fmt, type Range } from "./lib/plot-core";
import { Plot, arrowPath, type PlotView } from "./lib/plot-svg";
import { ModeTabs, NumberField, Readout, Slider, useReducedMotion } from "./lib/plot-ui";
import {
  FLAG,
  IDENTITY,
  PRESET_PARAMS,
  UNIT_SQUARE,
  apply,
  defaultParams,
  det,
  eigen,
  equalM,
  gridImage,
  isPresetId,
  lerpM,
  mul,
  orientationArc,
  presetMatrix,
  rotationAngle,
  toMatrix,
  toPresetList,
  type Mat2,
  type PresetId,
  type Vec2,
} from "./lib/plot-matrix";

type Mode = "single" | "compose";
const MODES: readonly Mode[] = ["single", "compose"];
const DEFAULT_A: Mat2 = [
  [1, 1],
  [0.5, 1.5],
];
const COMPOSE_A: Mat2 = presetMatrix("rotation", { theta: 90 });
const COMPOSE_B: Mat2 = presetMatrix("reflection", { phi: 0 });

const C_E1 = "var(--formal)";
const C_E2 = "var(--compute)";
const C_EIG = "var(--good)";

interface MatrixTransformProps {
  matrix?: unknown;
  matrix2?: unknown;
  mode?: string;
  modes?: unknown;
  showEigen?: boolean;
  showDet?: boolean;
  presets?: unknown;
  range?: unknown;
  title?: string;
  subtitle?: string;
}

/**
 * 2×2 real matrices acting on the plane: the image of the grid, the unit
 * square (area |det|, orientation), an asymmetric flag, invariant lines
 * (real eigenvectors) and composition AB versus BA.
 */
export function MatrixTransform(props: MatrixTransformProps) {
  const { t } = useI18n();
  const given = MODES.includes(props.mode as Mode) ? (props.mode as Mode) : null;
  const listed = Array.isArray(props.modes) ? MODES.filter((m) => (props.modes as unknown[]).includes(m)) : [];
  const offered: readonly Mode[] = listed.length ? listed : given ? [given] : MODES;
  const [mode, setMode] = useState<Mode>(given && offered.includes(given) ? given : offered[0]);
  const R = Math.min(12, Math.max(1.5, toNumber(props.range, 3)));

  return (
    <WidgetFrame title={props.title ?? t(`w.matrix.title.${mode}`)} subtitle={props.subtitle ?? t(`w.matrix.subtitle.${mode}`)}>
      {offered.length > 1 && (
        <div className="mb-4">
          <ModeTabs value={mode} options={offered} onChange={setMode} label={t("w.matrix.modesLabel")} render={(m) => t(`w.matrix.mode.${m}`)} />
        </div>
      )}
      {mode === "single" ? (
        <Single matrix={props.matrix} presets={toPresetList(props.presets)} showEigen={props.showEigen ?? true} showDet={props.showDet ?? true} R={R} />
      ) : (
        <Compose matrix={props.matrix} matrix2={props.matrix2} presets={toPresetList(props.presets)} showDet={props.showDet ?? true} R={R} />
      )}
    </WidgetFrame>
  );
}

/* ---------------------------------------------------------------------------
 * Single matrix
 * ------------------------------------------------------------------------- */

function Single({ matrix, presets, showEigen, showDet, R }: { matrix: unknown; presets: PresetId[]; showEigen: boolean; showDet: boolean; R: number }) {
  const { t, n } = useI18n();
  const initial = toMatrix(matrix, DEFAULT_A);
  const [A, setA] = useState<Mat2>(initial);
  const [preset, setPreset] = useState<PresetId | "custom">("custom");
  const [params, setParams] = useState<Record<string, number>>({});
  const [s, setS] = useState(1);
  const [playing, setPlaying] = useState(false);
  const reduced = useReducedMotion();
  const raf = useRef<number | null>(null);

  useEffect(() => {
    if (!playing) return;
    if (reduced) {
      setS(1);
      setPlaying(false);
      return;
    }
    const start = performance.now();
    const DURATION = 1400;
    const tick = (now: number) => {
      const u = Math.min(1, (now - start) / DURATION);
      setS(u < 0.5 ? 2 * u * u : 1 - Math.pow(-2 * u + 2, 2) / 2);
      if (u < 1) raf.current = requestAnimationFrame(tick);
      else setPlaying(false);
    };
    raf.current = requestAnimationFrame(tick);
    return () => {
      if (raf.current !== null) cancelAnimationFrame(raf.current);
    };
  }, [playing, reduced]);

  const choose = (id: PresetId) => {
    const p = defaultParams(id);
    setPreset(id);
    setParams(p);
    setA(presetMatrix(id, p));
    setS(0);
    setPlaying(true);
  };
  const setParam = (key: string, v: number) => {
    if (preset === "custom") return;
    const p = { ...params, [key]: v };
    setParams(p);
    setA(presetMatrix(preset, p));
    setPlaying(false);
    setS(1);
  };
  const setEntry = (i: number, j: number, v: number) => {
    setA((old) => old.map((row, r) => row.map((x, c) => (r === i && c === j ? Math.max(-100, Math.min(100, v)) : x))) as Mat2);
    setPreset("custom");
    setPlaying(false);
    setS(1);
  };
  const reset = () => {
    setA(initial);
    setPreset("custom");
    setParams({});
    setPlaying(false);
    setS(1);
  };

  // During the transition from I to A, rotations turn rigidly; everything else moves along the straight path (1 − s)I + sA.
  const M: Mat2 = s >= 1 ? A : preset === "rotation" ? presetMatrix("rotation", { theta: (params.theta ?? 0) * s }) : lerpM(IDENTITY, A, s);
  const d = det(A);
  const eig = eigen(A);
  const rot = rotationAngle(A);
  const [[a, b], [c, dd]] = A;

  return (
    <div>
      <div role="group" aria-label={t("w.matrix.presetsLabel")} className="flex flex-wrap gap-2">
        {presets.map((id) => (
          <button key={id} type="button" aria-pressed={preset === id} className={`btn btn-sm ${preset === id ? "btn-primary" : "btn-ghost"}`} onClick={() => choose(id)}>
            {t(`w.matrix.preset.${id}`)}
          </button>
        ))}
        {preset === "custom" && <span className="chip self-center">{t("w.matrix.preset.custom")}</span>}
      </div>

      <div className="mt-4 grid gap-5 md:grid-cols-[minmax(0,1.25fr)_minmax(0,1fr)]">
        <div className="min-w-0">
          <Plot
            x={[-R, R]}
            y={[-R, R]}
            aspect="equal"
            maxHeight={440}
            ariaLabel={t("w.matrix.aria.single", { a: fmt(a, 3), b: fmt(b, 3), c: fmt(c, 3), d: fmt(dd, 3), det: fmt(d, 3) })}
          >
            {(view) => <Scene view={view} M={M} R={R} eig={showEigen && s >= 1 ? eig : null} />}
          </Plot>
          <SceneLegend showEigen={showEigen && s >= 1 && (eig.kind === "distinct" || eig.kind === "defective")} />
          <div className="mt-3 flex flex-wrap items-end gap-3">
            <Slider
              className="min-w-40 flex-1"
              label={t("w.matrix.morph")}
              value={s}
              min={0}
              max={1}
              step={0.01}
              onChange={(v) => {
                setPlaying(false);
                setS(v);
              }}
              display={`s = ${fmt(s, 2)}`}
              accent="var(--gold)"
            />
            <button type="button" className="btn btn-sm btn-gold" onClick={() => (setS(0), setPlaying(true))}>
              <Play size={14} aria-hidden="true" /> {t("w.matrix.play")}
            </button>
          </div>
          {d < 0 && <p className="mt-2 text-xs text-muted">{t("w.matrix.morphFlip")}</p>}
        </div>

        <div className="min-w-0 space-y-4">
          {preset !== "custom" && PRESET_PARAMS[preset].length > 0 && (
            <div className="space-y-3">
              {PRESET_PARAMS[preset].map((p) => (
                <Slider
                  key={p.key}
                  label={t(`w.matrix.param.${p.key}`)}
                  value={params[p.key] ?? p.value}
                  min={p.min}
                  max={p.max}
                  step={p.step}
                  onChange={(v) => setParam(p.key, v)}
                  display={p.unit === "deg" ? `${fmt(params[p.key] ?? p.value, 0)}°` : fmt(params[p.key] ?? p.value, 2)}
                />
              ))}
            </div>
          )}

          <MatrixEditor label="A" m={A} onEntry={setEntry} sliders />

          <Readout className="space-y-2.5 text-sm">
            <p className="text-ink-2">
              {t("w.matrix.columns")}{" "}
              <span className="whitespace-nowrap font-serif text-[0.95rem] text-ink" dir="ltr">
                <span style={{ color: C_E1 }}>Ae₁</span> = ({fmt(a, 3)}, {fmt(c, 3)}), <span style={{ color: C_E2 }}>Ae₂</span> = ({fmt(b, 3)}, {fmt(dd, 3)})
              </span>
            </p>
            {showDet && (
              <div>
                <p className="font-serif text-base text-ink" dir="ltr">
                  det A = ad − bc = <strong>{fmt(d, 4)}</strong>
                </p>
                <p className="mt-0.5 text-ink-2">
                  {Math.abs(d) < 1e-9 ? t("w.matrix.det.zero") : `${t("w.matrix.det.area", { area: n(Number(Math.abs(d).toFixed(4))) })} ${d < 0 ? t("w.matrix.det.flip") : t("w.matrix.det.keep")}`}
                </p>
              </div>
            )}
            {showEigen && (
              <div>
                <p className="font-semibold text-ink">{t("w.matrix.eig.label")}</p>
                <EigenText eig={eig} rot={rot} />
              </div>
            )}
          </Readout>
          <button type="button" className="btn btn-sm btn-ghost" onClick={reset}>
            <RotateCcw size={14} aria-hidden="true" /> {t("w.common.reset")}
          </button>
        </div>
      </div>
    </div>
  );
}

function EigenText({ eig, rot }: { eig: ReturnType<typeof eigen>; rot: number | null }) {
  const { t, n } = useI18n();
  const r3 = (v: number) => n(Number(v.toFixed(3)));
  if (eig.kind === "distinct") {
    return (
      <>
        <ul className="mt-1 space-y-0.5 font-serif text-[0.95rem] text-ink" dir="ltr">
          {eig.values.map((l, i) => (
            <li key={i}>
              λ{i === 0 ? "₁" : "₂"} = {fmt(l, 3)}, v{i === 0 ? "₁" : "₂"} = ({fmt(eig.vectors[i][0], 3)}, {fmt(eig.vectors[i][1], 3)})
            </li>
          ))}
        </ul>
        <p className="mt-1 text-ink-2">
          {t("w.matrix.eig.distinct", { l1: r3(eig.values[0]), l2: r3(eig.values[1]) })}
          {eig.values.some((l) => Math.abs(l) < 1e-9) ? ` ${t("w.matrix.eig.zero")}` : ""}
          {eig.values.some((l) => l < -1e-9) ? ` ${t("w.matrix.eig.negative")}` : ""}
        </p>
      </>
    );
  }
  if (eig.kind === "scalar") return <p className="mt-1 text-ink-2">{t("w.matrix.eig.scalar", { l: r3(eig.value) })}</p>;
  if (eig.kind === "defective")
    return (
      <>
        <p className="mt-1 font-serif text-[0.95rem] text-ink" dir="ltr">
          λ = {fmt(eig.value, 3)}, v = ({fmt(eig.vector[0], 3)}, {fmt(eig.vector[1], 3)})
        </p>
        <p className="mt-1 text-ink-2">{t("w.matrix.eig.defective", { l: r3(eig.value) })}</p>
      </>
    );
  return (
    <>
      <p className="mt-1 font-serif text-[0.95rem] text-ink" dir="ltr">
        λ = {fmt(eig.re, 3)} ± {fmt(eig.im, 3)}i
      </p>
      <p className="mt-1 text-ink-2">
        {t("w.matrix.eig.complex")}
        {rot !== null ? ` ${t("w.matrix.eig.rotation", { deg: n(Number(((rot * 180) / Math.PI).toFixed(1))) })}` : ""}
      </p>
    </>
  );
}

/* ---------------------------------------------------------------------------
 * Composition
 * ------------------------------------------------------------------------- */

function Compose({ matrix, matrix2, presets, showDet, R }: { matrix: unknown; matrix2: unknown; presets: PresetId[]; showDet: boolean; R: number }) {
  const { t } = useI18n();
  const initA = toMatrix(matrix, COMPOSE_A);
  const initB = toMatrix(matrix2, COMPOSE_B);
  const [A, setA] = useState<Mat2>(initA);
  const [B, setB] = useState<Mat2>(initB);
  const BA = mul(B, A);
  const AB = mul(A, B);
  const same = equalM(AB, BA);
  const edit = (set: (f: (m: Mat2) => Mat2) => void) => (i: number, j: number, v: number) =>
    set((old) => old.map((row, r) => row.map((x, c) => (r === i && c === j ? Math.max(-100, Math.min(100, v)) : x))) as Mat2);

  return (
    <div>
      <div className="grid gap-4 sm:grid-cols-2">
        {(
          [
            ["A", A, setA],
            ["B", B, setB],
          ] as const
        ).map(([name, m, set]) => (
          <div key={name} className="rounded-xl border border-line px-3 py-3">
            <MatrixEditor label={name} m={m} onEntry={edit(set)} />
            <PresetSelect presets={presets} onPick={(id) => set(() => presetMatrix(id, composeParams(id)))} label={t("w.matrix.choose", { name })} />
          </div>
        ))}
      </div>
      <div className="mt-3 flex flex-wrap gap-2">
        <button
          type="button"
          className="btn btn-sm btn-ghost"
          onClick={() => {
            setA(B);
            setB(A);
          }}
        >
          <ArrowLeftRight size={14} aria-hidden="true" /> {t("w.matrix.compose.swap")}
        </button>
        <button
          type="button"
          className="btn btn-sm btn-ghost"
          onClick={() => {
            setA(initA);
            setB(initB);
          }}
        >
          <RotateCcw size={14} aria-hidden="true" /> {t("w.common.reset")}
        </button>
      </div>

      <div className="mt-4 grid gap-5 sm:grid-cols-2">
        {(
          [
            ["BA", A, B, BA, "thenB"],
            ["AB", B, A, AB, "thenA"],
          ] as const
        ).map(([name, first, , product, key]) => (
          <figure key={name} className="min-w-0">
            <figcaption className="mb-2 text-sm font-semibold text-ink-2">{t(`w.matrix.compose.${key}`)}</figcaption>
            <Plot
              x={[-R, R]}
              y={[-R, R]}
              aspect="equal"
              minHeight={200}
              maxHeight={360}
              defaultWidth={340}
              ariaLabel={t("w.matrix.aria.compose", { first: name === "BA" ? "A" : "B", second: name === "BA" ? "B" : "A", product: name })}
            >
              {(view) => <Scene view={view} M={product} R={R} ghost={first} compact />}
            </Plot>
            <div className="mt-2 flex justify-center">
              <MatrixView label={name} m={product} />
            </div>
          </figure>
        ))}
      </div>
      <SceneLegend compose />

      <Readout className="mt-4 space-y-1.5 text-sm">
        <p className={`font-semibold ${same ? "text-good" : "text-ink"}`}>{same ? t("w.matrix.compose.equal") : t("w.matrix.compose.notEqual")}</p>
        <p className="text-ink-2">{t("w.matrix.compose.read")}</p>
        {showDet && (
          <p className="text-ink-2">
            <span className="font-serif text-[0.95rem] text-ink" dir="ltr">
              det(AB) = det(BA) = det A · det B = {fmt(det(A), 3)} · {fmt(det(B), 3)} = {fmt(det(A) * det(B), 3)}
            </span>{" "}
            {t("w.matrix.compose.det")}
          </p>
        )}
      </Readout>
    </div>
  );
}

/** Parameters used when a preset is picked from the compose menus (no sliders there). */
function composeParams(id: PresetId): Record<string, number> {
  if (id === "rotation") return { theta: 90 };
  if (id === "reflection") return { phi: 0 };
  if (id === "projection") return { phi: 0 };
  return defaultParams(id);
}

function PresetSelect({ presets, onPick, label }: { presets: PresetId[]; onPick: (id: PresetId) => void; label: string }) {
  const { t } = useI18n();
  return (
    <label className="mt-3 flex items-center gap-2 text-sm text-ink-2">
      <span className="shrink-0">{label}</span>
      <select
        className="input w-auto min-w-0 flex-1 py-1 text-sm"
        value=""
        onChange={(e) => {
          if (isPresetId(e.target.value)) onPick(e.target.value);
        }}
      >
        <option value="">—</option>
        {presets.map((id) => (
          <option key={id} value={id}>
            {t(`w.matrix.presetShort.${id}`)}
          </option>
        ))}
      </select>
    </label>
  );
}

/* ---------------------------------------------------------------------------
 * Matrix display and editing
 * ------------------------------------------------------------------------- */

function Brackets({ children, label }: { children: ReactNode; label: ReactNode }) {
  return (
    <div className="flex items-center gap-2" dir="ltr">
      <span className="font-serif text-xl italic text-ink">{label} =</span>
      <div className="relative px-2.5 py-1">
        <span aria-hidden="true" className="absolute inset-y-0 start-0 w-2 rounded-s-md border-y-2 border-s-2 border-ink-2" />
        <span aria-hidden="true" className="absolute inset-y-0 end-0 w-2 rounded-e-md border-y-2 border-e-2 border-ink-2" />
        {children}
      </div>
    </div>
  );
}

function MatrixView({ m, label }: { m: Mat2; label: string }) {
  return (
    <Brackets label={label}>
      <div className="grid grid-cols-2 gap-x-4 gap-y-0.5 text-center font-serif text-base text-ink">
        {m.flat().map((v, k) => (
          <span key={k} className="min-w-10">
            {fmt(v, 3)}
          </span>
        ))}
      </div>
    </Brackets>
  );
}

const ENTRY_NAMES = [
  ["a", "b"],
  ["c", "d"],
] as const;

function MatrixEditor({ m, onEntry, label, sliders }: { m: Mat2; onEntry: (i: number, j: number, v: number) => void; label: string; sliders?: boolean }) {
  const { t } = useI18n();
  return (
    <fieldset>
      <legend className="sr-only">{t("w.matrix.entries", { name: label })}</legend>
      <Brackets label={label}>
        <div className="grid grid-cols-2 gap-x-3 gap-y-2">
          {[0, 1].map((i) =>
            [0, 1].map((j) => (
              <div key={`${i}${j}`} className="flex min-w-0 flex-col items-center">
                <NumberField
                  label={<span className="sr-only">{t("w.matrix.entry", { name: ENTRY_NAMES[i][j], matrix: label })}</span>}
                  value={m[i][j]}
                  onChange={(v) => onEntry(i, j, v)}
                  digits={3}
                  inputClassName="w-[4.5rem]"
                />
                {sliders && (
                  <input
                    type="range"
                    min={-3}
                    max={3}
                    step={0.1}
                    value={Math.max(-3, Math.min(3, m[i][j]))}
                    onChange={(e) => onEntry(i, j, Number(e.target.value))}
                    aria-label={t("w.matrix.entry", { name: ENTRY_NAMES[i][j], matrix: label })}
                    className="mt-1 w-[4.5rem]"
                    style={{ accentColor: j === 0 ? C_E1 : C_E2 }}
                    dir="ltr"
                  />
                )}
              </div>
            )),
          )}
        </div>
      </Brackets>
    </fieldset>
  );
}

/* ---------------------------------------------------------------------------
 * The picture
 * ------------------------------------------------------------------------- */

const poly = (view: PlotView, M: Mat2, pts: Vec2[]) =>
  pts
    .map((p) => apply(M, p))
    .map(([x, y]) => `${view.sx(x).toFixed(2)},${view.sy(y).toFixed(2)}`)
    .join(" ");

function Scene({ view, M, R, eig, ghost, compact }: { view: PlotView; M: Mat2; R: number; eig?: ReturnType<typeof eigen> | null; ghost?: Mat2; compact?: boolean }) {
  const { sx, sy } = view;
  const span: Range = [Math.min(view.x[0], view.y[0]), Math.max(view.x[1], view.y[1])];
  const reach = Math.max(Math.abs(span[0]), Math.abs(span[1]));
  const N = Math.min(40, Math.ceil(reach * 2.5));
  const grid = gridImage(M, N, reach * 40);
  const seg = ([p, q]: [Vec2, Vec2]) => `M${sx(p[0]).toFixed(1)} ${sy(p[1]).toFixed(1)}L${sx(q[0]).toFixed(1)} ${sy(q[1]).toFixed(1)}`;
  const gridD = [...grid.vertical.filter((_, k) => k !== N), ...grid.horizontal.filter((_, k) => k !== N)].map(seg).join("");
  const axesD = seg(grid.vertical[N]) + seg(grid.horizontal[N]);
  const e1 = apply(M, [1, 0]);
  const e2 = apply(M, [0, 1]);
  const arc = orientationArc(M);
  const arcD = arc.map(([x, y], k) => `${k ? "L" : "M"}${sx(x).toFixed(2)} ${sy(y).toFixed(2)}`).join("");
  const last = arc[arc.length - 1];
  const prev = arc[arc.length - 3];
  const arcHead = arrowPath(sx(prev[0]), sy(prev[1]), sx(last[0]), sy(last[1]), 7);
  const arrow = (v: Vec2, color: string, label: string) => {
    const X = sx(v[0]);
    const Y = sy(v[1]);
    const a = arrowPath(sx(0), sy(0), X, Y, 10);
    const len = Math.hypot(X - sx(0), Y - sy(0));
    const ux = len > 0 ? (X - sx(0)) / len : 1;
    const uy = len > 0 ? (Y - sy(0)) / len : 0;
    return (
      <g>
        {a.line && <path d={a.line} stroke={color} strokeWidth={2.75} strokeLinecap="round" fill="none" />}
        {a.head && <path d={a.head} fill={color} />}
        {!compact && (
          <text x={X + ux * 14} y={Y + uy * 14 + 4} textAnchor="middle" fontSize={13} fontStyle="italic" fontWeight={600} fill={color} className="font-serif" stroke="var(--paper)" strokeWidth={3} paintOrder="stroke">
            {label}
          </text>
        )}
      </g>
    );
  };

  return (
    <g>
      {/* image of the grid */}
      <path d={gridD} stroke="var(--sky)" strokeOpacity={0.38} strokeWidth={1} fill="none" />
      <path d={axesD} stroke="var(--sky)" strokeOpacity={0.85} strokeWidth={1.6} fill="none" />
      {/* the original unit square and flag (dashed) */}
      <polygon points={poly(view, IDENTITY, UNIT_SQUARE)} fill="none" stroke="var(--muted)" strokeDasharray="4 4" strokeWidth={1.25} />
      <polygon points={poly(view, IDENTITY, FLAG.pole)} fill="none" stroke="var(--muted)" strokeDasharray="3 3" strokeWidth={1} />
      <polygon points={poly(view, IDENTITY, FLAG.pennant)} fill="none" stroke="var(--muted)" strokeDasharray="3 3" strokeWidth={1} />
      {/* the intermediate step of a composition */}
      {ghost && (
        <g opacity={0.75}>
          <polygon points={poly(view, ghost, UNIT_SQUARE)} fill="none" stroke="var(--gold-ink)" strokeDasharray="6 4" strokeWidth={1.5} />
          <polygon points={poly(view, ghost, FLAG.pole)} fill="none" stroke="var(--human)" strokeDasharray="5 3" strokeWidth={1.25} />
          <polygon points={poly(view, ghost, FLAG.pennant)} fill="none" stroke="var(--human)" strokeDasharray="5 3" strokeWidth={1.25} />
        </g>
      )}
      {/* invariant lines */}
      {eig && (eig.kind === "distinct" || eig.kind === "defective") && (
        <g>
          {(eig.kind === "distinct" ? eig.vectors.map((v, i) => ({ v, l: eig.values[i], i })) : [{ v: eig.vector, l: eig.value, i: -1 }]).map(({ v, l, i }) => {
            const len = Math.hypot(v[0], v[1]) || 1;
            const u: Vec2 = [v[0] / len, v[1] / len];
            const far = reach * 3;
            const lab: Vec2 = [u[0] * R * 0.78, u[1] * R * 0.78];
            const name = i === 0 ? "λ₁" : i === 1 ? "λ₂" : "λ";
            // Keep the label inside the picture: anchor it towards the centre.
            const LX = sx(lab[0]);
            const toLeft = LX > view.W / 2;
            return (
              <g key={i}>
                <line x1={sx(-u[0] * far)} y1={sy(-u[1] * far)} x2={sx(u[0] * far)} y2={sy(u[1] * far)} stroke={C_EIG} strokeWidth={2} strokeDasharray="9 6" />
                <text x={toLeft ? LX - 8 : LX + 8} y={sy(lab[1]) - 8} textAnchor={toLeft ? "end" : "start"} fontSize={13} fontWeight={600} fill={C_EIG} className="font-serif" stroke="var(--paper)" strokeWidth={3.5} paintOrder="stroke">
                  {name} = {fmt(l, 2)}
                </text>
              </g>
            );
          })}
        </g>
      )}
      {/* image of the unit square, the flag and the orientation arc */}
      <polygon points={poly(view, M, UNIT_SQUARE)} fill="var(--gold)" fillOpacity={0.22} stroke="var(--gold)" strokeWidth={2} strokeLinejoin="round" />
      <polygon points={poly(view, M, FLAG.pole)} fill="var(--ink-2)" fillOpacity={0.85} strokeLinejoin="round" />
      <polygon points={poly(view, M, FLAG.pennant)} fill="var(--human)" fillOpacity={0.9} stroke="var(--human)" strokeLinejoin="round" />
      <path d={arcD} stroke="var(--gold-ink)" strokeWidth={1.75} fill="none" />
      {arcHead.head && <path d={arcHead.head} fill="var(--gold-ink)" />}
      {arrow(e1, C_E1, "Ae₁")}
      {arrow(e2, C_E2, "Ae₂")}
      <circle cx={sx(0)} cy={sy(0)} r={3} fill="var(--ink)" />
    </g>
  );
}

function SceneLegend({ showEigen, compose }: { showEigen?: boolean; compose?: boolean }) {
  const { t } = useI18n();
  const item = (sw: ReactNode, text: string) => (
    <li className="flex items-center gap-1.5">
      <svg width="22" height="12" aria-hidden="true" className="shrink-0">
        {sw}
      </svg>
      {text}
    </li>
  );
  return (
    <ul className="mt-2 flex flex-wrap gap-x-4 gap-y-1 text-xs text-ink-2">
      {item(<line x1="1" y1="6" x2="21" y2="6" stroke="var(--sky)" strokeWidth="1.6" />, t("w.matrix.legend.grid"))}
      {item(<rect x="2" y="1" width="18" height="10" fill="var(--gold)" fillOpacity="0.3" stroke="var(--gold)" strokeWidth="1.5" />, t("w.matrix.legend.square"))}
      {item(
        <>
          <rect x="4" y="1" width="2.5" height="10" fill="var(--ink-2)" />
          <path d="M6.5 1 L17 3.5 L6.5 6 Z" fill="var(--human)" />
        </>,
        t("w.matrix.legend.flag"),
      )}
      {item(<rect x="2" y="1" width="18" height="10" fill="none" stroke="var(--muted)" strokeDasharray="3 3" />, t("w.matrix.legend.before"))}
      {compose && item(<rect x="2" y="1" width="18" height="10" fill="none" stroke="var(--human)" strokeDasharray="5 3" />, t("w.matrix.legend.middle"))}
      {showEigen && item(<line x1="1" y1="6" x2="21" y2="6" stroke={C_EIG} strokeWidth="2" strokeDasharray="5 3" />, t("w.matrix.legend.eigen"))}
    </ul>
  );
}
