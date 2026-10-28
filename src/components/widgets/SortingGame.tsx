"use client";

import { Check, RotateCcw, Sparkles } from "lucide-react";
import { useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";

type Rule = "colour" | "shape";
interface Item {
  id: string;
  emoji: string;
  colour: "yellow" | "red" | "green" | "orange";
  shape: "round" | "long";
}

const ITEMS: Item[] = [
  { id: "banana", emoji: "🍌", colour: "yellow", shape: "long" },
  { id: "lemon", emoji: "🍋", colour: "yellow", shape: "round" },
  { id: "apple", emoji: "🍎", colour: "red", shape: "round" },
  { id: "strawberry", emoji: "🍓", colour: "red", shape: "round" },
  { id: "cucumber", emoji: "🥒", colour: "green", shape: "long" },
  { id: "pear", emoji: "🍐", colour: "green", shape: "round" },
  { id: "orange", emoji: "🍊", colour: "orange", shape: "round" },
  { id: "carrot", emoji: "🥕", colour: "orange", shape: "long" },
];

const BOXES: Record<Rule, string[]> = {
  colour: ["yellow", "red", "green", "orange", "blue"],
  shape: ["round", "long"],
};

const BOX_TINT: Record<string, string> = {
  yellow: "#f4d35e",
  red: "#e76f51",
  green: "#6a994e",
  orange: "#f4a261",
  blue: "#4c86c6",
  round: "var(--sky)",
  long: "var(--formal)",
};

/** K–2 sorting game: put fruit and vegetables into collections by a rule. Click (or tap, or use the keyboard) — no dragging required. */
export function SortingGame() {
  const { t, n } = useI18n();
  const [rule, setRule] = useState<Rule>("colour");
  const [placed, setPlaced] = useState<Record<string, string>>({});
  const [selected, setSelected] = useState<string | null>(null);
  const [checked, setChecked] = useState(false);

  const boxes = BOXES[rule];
  const unplaced = ITEMS.filter((i) => !placed[i.id]);
  const correctBox = (item: Item) => (rule === "colour" ? item.colour : item.shape);
  const wrong = useMemo(() => ITEMS.filter((i) => placed[i.id] && placed[i.id] !== correctBox(i)), [placed, rule]); // eslint-disable-line react-hooks/exhaustive-deps
  const done = unplaced.length === 0;

  const reset = (r: Rule = rule) => {
    setRule(r);
    setPlaced({});
    setSelected(null);
    setChecked(false);
  };

  const drop = (box: string) => {
    if (!selected) return;
    setPlaced((p) => ({ ...p, [selected]: box }));
    setSelected(null);
    setChecked(false);
  };

  return (
    <WidgetFrame title={t("w.sort.title")} subtitle={t("w.sort.subtitle")}>
      <div className="flex flex-wrap items-center gap-2">
        <span className="text-sm font-semibold text-ink-2">{t("w.sort.ruleLabel")}</span>
        {(["colour", "shape"] as Rule[]).map((r) => (
          <button key={r} type="button" onClick={() => reset(r)} aria-pressed={rule === r} className={`btn btn-sm ${rule === r ? "btn-primary" : "btn-ghost"}`}>
            {t(`w.sort.rule.${r}`)}
          </button>
        ))}
        <button type="button" onClick={() => reset()} className="btn btn-sm btn-ghost ms-auto">
          <RotateCcw size={14} aria-hidden="true" /> {t("w.common.reset")}
        </button>
      </div>

      <div className="mt-4 rounded-2xl border border-dashed border-line-2 bg-paper-2/50 p-3">
        <p className="mb-2 text-xs font-semibold uppercase tracking-wide text-muted">{t("w.sort.basket")}</p>
        <div className="flex min-h-16 flex-wrap gap-2">
          {unplaced.length === 0 && <p className="self-center px-2 text-sm text-muted">{t("w.sort.empty")}</p>}
          {unplaced.map((item) => (
            <button
              key={item.id}
              type="button"
              onClick={() => setSelected(selected === item.id ? null : item.id)}
              aria-pressed={selected === item.id}
              aria-label={t(`w.sort.item.${item.id}`)}
              className={`flex h-14 w-14 items-center justify-center rounded-2xl border-2 bg-card text-3xl transition-transform hover:-translate-y-0.5 ${
                selected === item.id ? "scale-110 border-gold shadow-[0_0_0_4px_var(--glow)]" : "border-line"
              }`}
            >
              <span aria-hidden="true">{item.emoji}</span>
            </button>
          ))}
        </div>
        <p className="mt-2 text-xs text-muted" aria-live="polite">
          {selected ? t("w.sort.nowPick", { item: t(`w.sort.item.${selected}`) }) : unplaced.length ? t("w.sort.pickItem") : ""}
        </p>
      </div>

      <div className={`mt-4 grid gap-3 ${rule === "colour" ? "grid-cols-2 sm:grid-cols-5" : "grid-cols-2"}`}>
        {boxes.map((box) => {
          const inBox = ITEMS.filter((i) => placed[i.id] === box);
          return (
            <button
              key={box}
              type="button"
              onClick={() => drop(box)}
              disabled={!selected}
              className={`group flex min-h-32 flex-col rounded-2xl border-2 p-2.5 text-start transition-all ${selected ? "cursor-pointer hover:-translate-y-0.5" : "cursor-default"}`}
              style={{ borderColor: BOX_TINT[box], background: `color-mix(in oklab, ${BOX_TINT[box]} 9%, var(--card))` }}
              aria-label={`${t(`w.sort.box.${box}`)} — ${t("w.sort.contains", { n: inBox.length })}`}
            >
              <span className="flex items-center justify-between text-xs font-bold text-ink">
                {t(`w.sort.box.${box}`)}
                <span className="rounded-full bg-card px-2 py-0.5 font-mono text-ink-2">{n(inBox.length)}</span>
              </span>
              <span className="mt-2 flex flex-wrap gap-1">
                {inBox.map((i) => (
                  <span
                    key={i.id}
                    className={`relative flex h-10 w-10 items-center justify-center rounded-xl bg-card text-2xl ${checked && wrong.includes(i) ? "ring-2 ring-warn" : ""}`}
                    role="img"
                    aria-label={t(`w.sort.item.${i.id}`)}
                  >
                    {i.emoji}
                  </span>
                ))}
                {inBox.length === 0 && box === "blue" && done && <span className="text-xs italic text-muted">{t("w.sort.emptyBox")}</span>}
              </span>
            </button>
          );
        })}
      </div>

      <div className="mt-4 flex flex-wrap items-center gap-3" aria-live="polite">
        <button type="button" className="btn btn-sm btn-gold" disabled={!done} onClick={() => setChecked(true)}>
          <Check size={14} aria-hidden="true" /> {t("w.sort.check")}
        </button>
        {checked && wrong.length > 0 && <p className="text-sm text-warn">{t("w.sort.lookAgain", { item: t(`w.sort.item.${wrong[0].id}`) })}</p>}
        {checked && wrong.length === 0 && (
          <p className="flex items-center gap-2 text-sm font-semibold text-good">
            <Sparkles size={16} aria-hidden="true" />
            {rule === "colour" ? t("w.sort.successColour") : t("w.sort.successShape")}
          </p>
        )}
      </div>
    </WidgetFrame>
  );
}
