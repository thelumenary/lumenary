/**
 * The three optional feline narrators. Drawn as simple vector portraits so
 * they stay crisp, light-weight and themeable.
 */
export type NarratorId = "chloe" | "margaret" | "gideon";

const HEAD = "M14 27 11.5 9.5 25 18.2Q32 15.8 39 18.2L52.5 9.5 50 27Q54 34.5 52 42.5 47.5 54.5 32 55.5 16.5 54.5 12 42.5 10 34.5 14 27Z";

function Face({ eye, pupil = "#1d1d1f" }: { eye: string; pupil?: string }) {
  return (
    <g>
      <ellipse cx="24.5" cy="34" rx="4" ry="4.6" fill={eye} />
      <ellipse cx="39.5" cy="34" rx="4" ry="4.6" fill={eye} />
      <ellipse cx="25" cy="34.4" rx="1.6" ry="3.3" fill={pupil} />
      <ellipse cx="40" cy="34.4" rx="1.6" ry="3.3" fill={pupil} />
      <circle cx="26" cy="32.2" r="0.9" fill="#fff" />
      <circle cx="41" cy="32.2" r="0.9" fill="#fff" />
      <path d="M30.2 40.4h3.6L32 42.6Z" fill="#d9777f" />
      <path d="M32 42.6v1.6M32 44.2c-1 1.4-2.8 1.6-4 .6M32 44.2c1 1.4 2.8 1.6 4 .6" stroke="#3a2a2a" strokeWidth="0.9" fill="none" strokeLinecap="round" />
      <g stroke="currentColor" strokeWidth="0.7" opacity="0.45" strokeLinecap="round">
        <path d="M22 42.5 11 41M22 44.5 11.5 46.5M42 42.5 53 41M42 44.5 52.5 46.5" />
      </g>
    </g>
  );
}

export function NarratorAvatar({ who, size = 48, className = "" }: { who: NarratorId; size?: number; className?: string }) {
  const bg = { chloe: "var(--human-soft)", margaret: "var(--compute-soft)", gideon: "var(--formal-soft)" }[who];
  const ring = { chloe: "var(--human)", margaret: "var(--compute)", gideon: "var(--formal)" }[who];
  return (
    <svg width={size} height={size} viewBox="0 0 64 64" className={className} role="img" aria-label={who}>
      <circle cx="32" cy="32" r="31" fill={bg} stroke={ring} strokeWidth="1.5" opacity="0.98" />
      <g transform="translate(0 2)">
        {who === "chloe" && (
          <g>
            <path d={HEAD} fill="#e9a35e" />
            <path d="M15.2 22.5 13.8 12.8 21.5 17.8Z M48.8 22.5 50.2 12.8 42.5 17.8Z" fill="#f6c9a5" />
            <path d="M28 20.5 29 25M32 19.5v5M36 20.5 35 25" stroke="#c4773a" strokeWidth="1.6" strokeLinecap="round" />
            <path d="M20 38q12 13 24 0 3 9-12 11.5Q17 47 20 38Z" fill="#fbe8d0" />
            <Face eye="#7fb069" />
            <path d="M43.5 18.5l2.2-1.8.4 2.8-2.6.4" fill="var(--gold)" />
          </g>
        )}
        {who === "margaret" && (
          <g>
            <path d={HEAD} fill="#9ea4ad" />
            <path d="M15.2 22.5 13.8 12.8 21.5 17.8Z M48.8 22.5 50.2 12.8 42.5 17.8Z" fill="#d8c6c8" />
            <path d="M27 21q5-3 10 0M26 24.5q6-3 12 0" stroke="#6f7680" strokeWidth="1.5" fill="none" strokeLinecap="round" />
            <path d="M13.5 30.5l5 1.2M13.2 34.5l5 .2M50.5 30.5l-5 1.2M50.8 34.5l-5 .2" stroke="#6f7680" strokeWidth="1.4" strokeLinecap="round" />
            <path d="M20 38q12 13 24 0 3 9-12 11.5Q17 47 20 38Z" fill="#eceef0" />
            <Face eye="#e0a23b" />
            <g fill="none" stroke="#2b3440" strokeWidth="1.5">
              <circle cx="24.5" cy="34" r="6.2" />
              <circle cx="39.5" cy="34" r="6.2" />
              <path d="M30.7 33.4q1.3-1 2.6 0M18.3 33 14.5 31.5M45.7 33l3.8-1.5" />
            </g>
          </g>
        )}
        {who === "gideon" && (
          <g>
            <path d={HEAD} fill="#2a2b35" />
            <path d="M15.2 22.5 13.8 12.8 21.5 17.8Z M48.8 22.5 50.2 12.8 42.5 17.8Z" fill="#4a4558" />
            <path d="M24 38.5q8 9 16 0 2 7-8 9-10-2-8-9Z" fill="#3a3b47" />
            <Face eye="#f2c14e" pupil="#14141a" />
            <g transform="translate(32 55)">
              <path d="M0 0-8.5-4.5v9Z M0 0 8.5-4.5v9Z" fill="var(--formal)" />
              <circle r="2.1" fill="var(--formal)" stroke="#2a2b35" strokeWidth="0.8" />
            </g>
          </g>
        )}
      </g>
    </svg>
  );
}
