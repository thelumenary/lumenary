"use client";

import { useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";

type Region = "onlyA" | "both" | "onlyB" | "neither";
const REGIONS: Region[] = ["onlyA", "both", "onlyB", "neither"];

/** Names drawn from many places; membership is what matters mathematically. */
const PEOPLE: { name: string; football: boolean; chess: boolean }[] = [
  { name: "Amara", football: true, chess: false },
  { name: "Kenji", football: true, chess: true },
  { name: "Lucía", football: false, chess: true },
  { name: "Arjun", football: true, chess: true },
  { name: "Fatima", football: false, chess: true },
  { name: "Mateus", football: true, chess: false },
  { name: "Aigerim", football: false, chess: false },
  { name: "Tavita", football: true, chess: false },
  { name: "Olena", football: false, chess: false },
  { name: "Kwame", football: false, chess: true },
];

const regionOf = (p: (typeof PEOPLE)[number]): Region => (p.football && p.chess ? "both" : p.football ? "onlyA" : p.chess ? "onlyB" : "neither");

/** Every one of the 16 combinations of regions has a name. */
const NAMES: Record<string, string> = {
  "": "∅",
  onlyA: "A ∖ B",
  both: "A ∩ B",
  onlyB: "B ∖ A",
  neither: "(A ∪ B)ᶜ",
  "both,onlyA": "A",
  "both,onlyB": "B",
  "onlyA,onlyB": "A △ B",
  "neither,onlyA": "Bᶜ",
  "neither,onlyB": "Aᶜ",
  "both,neither": "(A △ B)ᶜ",
  "both,onlyA,onlyB": "A ∪ B",
  "both,neither,onlyA": "A ∪ Bᶜ",
  "both,neither,onlyB": "Aᶜ ∪ B",
  "neither,onlyA,onlyB": "(A ∩ B)ᶜ",
  "both,neither,onlyA,onlyB": "U",
};

const PRESETS: { label: string; regions: Region[] }[] = [
  { label: "A ∪ B", regions: ["onlyA", "both", "onlyB"] },
  { label: "A ∩ B", regions: ["both"] },
  { label: "A ∖ B", regions: ["onlyA"] },
  { label: "Aᶜ", regions: ["onlyB", "neither"] },
  { label: "A △ B", regions: ["onlyA", "onlyB"] },
];

export function VennExplorer() {
  const { t } = useI18n();
  const [shaded, setShaded] = useState<Set<Region>>(new Set(["both"]));
  const key = [...shaded].sort().join(",");
  const name = NAMES[key];
  const members = useMemo(() => PEOPLE.filter((p) => shaded.has(regionOf(p))).map((p) => p.name), [shaded]);

  const toggle = (r: Region) =>
    setShaded((prev) => {
      const next = new Set(prev);
      if (next.has(r)) next.delete(r);
      else next.add(r);
      return next;
    });

  const fill = (r: Region) => (shaded.has(r) ? "var(--gold)" : "transparent");
  const placed: Record<Region, { x: number; y: number }[]> = {
    onlyA: [
      { x: 118, y: 92 },
      { x: 104, y: 128 },
      { x: 124, y: 164 },
      { x: 108, y: 200 },
    ],
    both: [
      { x: 210, y: 128 },
      { x: 210, y: 168 },
    ],
    onlyB: [
      { x: 300, y: 92 },
      { x: 316, y: 132 },
      { x: 296, y: 170 },
      { x: 314, y: 206 },
    ],
    neither: [
      { x: 44, y: 258 },
      { x: 376, y: 258 },
      { x: 210, y: 270 },
    ],
  };
  const counters: Record<Region, number> = { onlyA: 0, both: 0, onlyB: 0, neither: 0 };

  return (
    <WidgetFrame title={t("w.venn.title")} subtitle={t("w.venn.subtitle")}>
      <div className="grid items-start gap-5 md:grid-cols-[1.2fr_1fr]">
        <div dir="ltr">
          <svg viewBox="0 0 420 290" className="w-full" role="group" aria-label={t("w.venn.diagram")}>
            <defs>
              <clipPath id="vA">
                <circle cx="160" cy="148" r="108" />
              </clipPath>
              <clipPath id="vB">
                <circle cx="260" cy="148" r="108" />
              </clipPath>
              <mask id="notA">
                <rect width="420" height="290" fill="white" />
                <circle cx="160" cy="148" r="108" fill="black" />
              </mask>
              <mask id="notB">
                <rect width="420" height="290" fill="white" />
                <circle cx="260" cy="148" r="108" fill="black" />
              </mask>
              <mask id="notAB">
                <rect width="420" height="290" fill="white" />
                <circle cx="160" cy="148" r="108" fill="black" />
                <circle cx="260" cy="148" r="108" fill="black" />
              </mask>
            </defs>
            <rect x="4" y="4" width="412" height="282" rx="16" fill="var(--paper-2)" stroke="var(--line-2)" />
            <g opacity="0.55" style={{ transition: "fill .2s" }}>
              <rect width="420" height="290" rx="16" fill={fill("neither")} mask="url(#notAB)" />
              <circle cx="160" cy="148" r="108" fill={fill("onlyA")} mask="url(#notB)" />
              <circle cx="260" cy="148" r="108" fill={fill("onlyB")} mask="url(#notA)" />
              <g clipPath="url(#vA)">
                <circle cx="260" cy="148" r="108" fill={fill("both")} />
              </g>
            </g>
            <circle cx="160" cy="148" r="108" fill="none" stroke="var(--human)" strokeWidth="2.5" />
            <circle cx="260" cy="148" r="108" fill="none" stroke="var(--formal)" strokeWidth="2.5" />
            <text x="78" y="44" fill="var(--human)" fontWeight="700" fontSize="15">
              A · {t("w.venn.football")}
            </text>
            <text x="250" y="44" fill="var(--formal)" fontWeight="700" fontSize="15">
              B · {t("w.venn.chess")}
            </text>
            <text x="22" y="28" fill="var(--muted)" fontSize="13" fontWeight="700">
              U
            </text>
            {PEOPLE.map((p) => {
              const r = regionOf(p);
              const pos = placed[r][counters[r]++ % placed[r].length];
              return (
                <text key={p.name} x={pos.x} y={pos.y} textAnchor="middle" fontSize="13" fill="var(--ink)" fontWeight="600">
                  {p.name}
                </text>
              );
            })}
            {/* Invisible hit areas for each region, operable by keyboard via the buttons below. */}
            <g fillOpacity="0" className="cursor-pointer">
              <rect width="420" height="290" mask="url(#notAB)" onClick={() => toggle("neither")} />
              <circle cx="160" cy="148" r="108" mask="url(#notB)" onClick={() => toggle("onlyA")} />
              <circle cx="260" cy="148" r="108" mask="url(#notA)" onClick={() => toggle("onlyB")} />
              <g clipPath="url(#vA)">
                <circle cx="260" cy="148" r="108" onClick={() => toggle("both")} />
              </g>
            </g>
          </svg>
          <div className="mt-2 flex flex-wrap gap-1.5">
            {REGIONS.map((r) => (
              <button key={r} type="button" aria-pressed={shaded.has(r)} onClick={() => toggle(r)} className={`btn btn-sm ${shaded.has(r) ? "btn-gold" : "btn-ghost"}`}>
                {t(`w.venn.region.${r}`)}
              </button>
            ))}
          </div>
        </div>
        <div className="space-y-4">
          <div className="rounded-xl border border-line bg-paper-2/60 p-4" aria-live="polite">
            <p className="text-xs font-semibold uppercase tracking-wide text-muted">{t("w.venn.youMade")}</p>
            <p className="mt-1 font-serif text-3xl text-ink" dir="ltr">
              {name}
            </p>
            <p className="mt-3 font-mono text-sm leading-relaxed text-ink-2" dir="ltr">
              {"{"}
              {members.join(", ")}
              {"}"}
            </p>
            <p className="mt-2 text-xs text-muted">{t("w.venn.count", { n: members.length })}</p>
          </div>
          <div>
            <p className="mb-2 text-xs font-semibold uppercase tracking-wide text-muted">{t("w.venn.tryThese")}</p>
            <div className="flex flex-wrap gap-1.5" dir="ltr">
              {PRESETS.map((p) => (
                <button key={p.label} type="button" className="btn btn-sm btn-ghost font-serif" onClick={() => setShaded(new Set(p.regions))}>
                  {p.label}
                </button>
              ))}
            </div>
          </div>
          <p className="text-sm leading-relaxed text-ink-2">{t("w.venn.challenge")}</p>
        </div>
      </div>
    </WidgetFrame>
  );
}
