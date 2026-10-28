import { MousePointerClick } from "lucide-react";

/** Shared chrome for interactive explorations. */
export function WidgetFrame({ title, subtitle, children, tone = "default" }: { title: string; subtitle?: string; children: React.ReactNode; tone?: "default" | "gold" }) {
  return (
    <div
      className={`not-prose !mt-7 overflow-hidden rounded-2xl border font-sans shadow-[var(--shadow)] ${tone === "gold" ? "border-gold/40 bg-gradient-to-b from-gold-soft/60 to-card" : "border-line bg-card"}`}
    >
      <div className="flex items-start gap-3 border-b border-line/80 px-5 py-3.5">
        <MousePointerClick size={18} className={`mt-0.5 shrink-0 ${tone === "gold" ? "text-gold-ink" : "text-sky"}`} aria-hidden="true" />
        <div>
          <p className="text-[0.95rem] font-bold text-ink">{title}</p>
          {subtitle && <p className="mt-0.5 text-sm leading-snug text-muted">{subtitle}</p>}
        </div>
      </div>
      <div className="px-5 py-5">{children}</div>
    </div>
  );
}
