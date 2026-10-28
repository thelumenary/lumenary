/**
 * The hero illustration: the first learning path as a rising constellation,
 * fading into the parts of mathematics still to come.
 */
export function HeroConstellation({ lessons, future }: { lessons: string[]; future: string[] }) {
  const path = [
    { x: 52, y: 368 },
    { x: 146, y: 306 },
    { x: 226, y: 252 },
    { x: 312, y: 196 },
    { x: 392, y: 140 },
  ];
  // Planned destinations, each linked to the lesson (or destination) it grows from.
  const far: { x: number; y: number; from: { x: number; y: number }; anchor: "start" | "end"; dx: number }[] = [
    { x: 456, y: 74, from: path[4], anchor: "end", dx: -13 },
    { x: 334, y: 300, from: path[2], anchor: "start", dx: 13 },
    { x: 430, y: 232, from: path[3], anchor: "start", dx: 13 },
    { x: 516, y: 24, from: { x: 456, y: 74 }, anchor: "end", dx: -13 },
  ];
  const stars = [
    [30, 40], [90, 120], [160, 60], [250, 110], [340, 40], [470, 300], [420, 380], [300, 340], [200, 380], [110, 220], [60, 280], [500, 250], [360, 260], [260, 30],
  ];
  return (
    <svg viewBox="0 0 540 420" className="h-auto w-full" role="img" aria-label={lessons.join(" → ")}>
      <defs>
        <radialGradient id="hc-glow">
          <stop offset="0%" stopColor="var(--gold)" stopOpacity="0.55" />
          <stop offset="100%" stopColor="var(--gold)" stopOpacity="0" />
        </radialGradient>
        <linearGradient id="hc-line" x1="0" y1="1" x2="1" y2="0">
          <stop offset="0%" stopColor="var(--gold)" stopOpacity="0.9" />
          <stop offset="100%" stopColor="var(--gold)" stopOpacity="0.5" />
        </linearGradient>
      </defs>
      {stars.map(([x, y], i) => (
        <circle key={i} cx={x} cy={y} r={i % 3 === 0 ? 1.8 : 1.2} fill="var(--ink-2)" opacity="0.5" className="animate-twinkle" style={{ animationDelay: `${(i * 0.37) % 3.6}s` }} />
      ))}
      {far.map((f, i) => (
        <line key={`fl${i}`} x1={f.from.x} y1={f.from.y} x2={f.x} y2={f.y} stroke="var(--line-2)" strokeWidth="1.5" strokeDasharray="4 6" />
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
          <circle cx={f.x} cy={f.y} r="7" fill="var(--card)" stroke="var(--line-2)" strokeWidth="1.5" strokeDasharray="2 2.5" />
          {future[i] && (
            <text x={f.x + f.dx} y={f.y + 4} textAnchor={f.anchor} fontSize="12.5" fill="var(--muted)" fontStyle="italic">
              {future[i]}
            </text>
          )}
        </g>
      ))}
      {path.map((p, i) => (
        <g key={i} className="animate-float-up" style={{ animationDelay: `${0.25 + i * 0.18}s` }}>
          <circle cx={p.x} cy={p.y} r="26" fill="url(#hc-glow)" />
          <circle cx={p.x} cy={p.y} r="10" fill="var(--gold)" stroke="var(--paper)" strokeWidth="3" />
          <text x={p.x + 16} y={p.y + 26} fontSize="13.5" fontWeight="600" fill="var(--ink)">
            {i + 1}. {lessons[i]}
          </text>
        </g>
      ))}
    </svg>
  );
}
