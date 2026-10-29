/**
 * The hero illustration: the curriculum as a rising constellation, one landmark per stage from
 * counting to research, with side stars branching off it.
 */
export function HeroConstellation({ path: labels, branches }: { path: string[]; branches: string[] }) {
  const path = [
    { x: 40, y: 392 },
    { x: 100, y: 344 },
    { x: 160, y: 300 },
    { x: 224, y: 252 },
    { x: 286, y: 204 },
    { x: 346, y: 156 },
    { x: 408, y: 106 },
    { x: 470, y: 52 },
  ];
  // Side stars, each linked to the landmark it grows from; labels sit away from the path.
  const far: { x: number; y: number; from: number; anchor: "start" | "end"; dx: number }[] = [
    { x: 268, y: 330, from: 2, anchor: "start", dx: 12 },
    { x: 384, y: 250, from: 4, anchor: "start", dx: 12 },
    { x: 230, y: 130, from: 5, anchor: "end", dx: -12 },
    { x: 500, y: 190, from: 6, anchor: "end", dx: -12 },
  ];
  const stars = [
    [30, 40], [90, 120], [160, 60], [250, 70], [340, 40], [470, 300], [420, 380], [300, 380], [200, 400], [110, 220], [60, 280], [520, 260], [150, 180], [520, 120],
  ];
  return (
    <svg viewBox="0 0 540 420" className="h-auto w-full" role="img" aria-label={labels.join(" → ")}>
      <defs>
        <radialGradient id="hc-glow">
          <stop offset="0%" stopColor="var(--gold)" stopOpacity="0.55" />
          <stop offset="100%" stopColor="var(--gold)" stopOpacity="0" />
        </radialGradient>
        <linearGradient id="hc-line" x1="0" y1="1" x2="1" y2="0">
          <stop offset="0%" stopColor="var(--gold)" stopOpacity="0.95" />
          <stop offset="100%" stopColor="var(--gold)" stopOpacity="0.6" />
        </linearGradient>
      </defs>
      {stars.map(([x, y], i) => (
        <circle key={i} cx={x} cy={y} r={i % 3 === 0 ? 1.8 : 1.2} fill="var(--ink-2)" opacity="0.5" className="animate-twinkle" style={{ animationDelay: `${(i * 0.37) % 3.6}s` }} />
      ))}
      {far.map((f, i) => (
        <line key={`fl${i}`} x1={path[f.from].x} y1={path[f.from].y} x2={f.x} y2={f.y} stroke="var(--gold)" strokeOpacity="0.45" strokeWidth="1.5" />
      ))}
      <path
        d={`M${path.map((p) => `${p.x} ${p.y}`).join(" L")}`}
        fill="none"
        stroke="url(#hc-line)"
        strokeWidth="2.5"
        strokeLinecap="round"
        className="animate-draw"
      />
      {far.map((f, i) => (
        <g key={`f${i}`}>
          <circle cx={f.x} cy={f.y} r="5.5" fill="var(--gold-soft)" stroke="var(--gold)" strokeWidth="1.5" />
          {branches[i] && (
            <text x={f.x + f.dx} y={f.y + 4} textAnchor={f.anchor} fontSize="12.5" fill="var(--muted)" fontStyle="italic">
              {branches[i]}
            </text>
          )}
        </g>
      ))}
      {path.map((p, i) => {
        const last = i === path.length - 1;
        return (
          <g key={i} className="animate-float-up" style={{ animationDelay: `${0.25 + i * 0.14}s` }}>
            <circle cx={p.x} cy={p.y} r={last ? 30 : 22} fill="url(#hc-glow)" />
            <circle cx={p.x} cy={p.y} r={last ? 10 : 8} fill="var(--gold)" stroke="var(--paper)" strokeWidth="3" />
            <text x={last ? p.x - 16 : p.x + 14} y={last ? p.y + 4 : p.y + 22} textAnchor={last ? "end" : "start"} fontSize="13.5" fontWeight="600" fill="var(--ink)">
              {labels[i]}
            </text>
          </g>
        );
      })}
    </svg>
  );
}
