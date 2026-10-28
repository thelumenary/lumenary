/** The Lumenary mark: a four-pointed star of light inside a ring — a lamp, a compass, a point of wonder. */
export function LogoMark({ size = 32, className = "" }: { size?: number; className?: string }) {
  return (
    <svg width={size} height={size} viewBox="0 0 32 32" className={className} aria-hidden="true">
      <circle cx="16" cy="16" r="14.6" fill="none" stroke="currentColor" strokeWidth="1.4" opacity="0.28" />
      <circle cx="16" cy="16" r="10.2" fill="none" stroke="var(--gold)" strokeWidth="0.9" opacity="0.55" strokeDasharray="1.2 2.4" />
      <path d="M16 3.2c.9 7.4 3.4 11.2 12.8 12.8C19.4 17.6 16.9 20.6 16 28.8 15.1 20.6 12.6 17.6 3.2 16 12.6 14.4 15.1 10.6 16 3.2Z" fill="var(--gold)" />
      <circle cx="16" cy="16" r="2" fill="var(--paper)" />
    </svg>
  );
}

export function Wordmark({ className = "" }: { className?: string }) {
  return (
    <span className={`font-display text-[1.2rem] leading-none tracking-tight ${className}`}>
      <span className="font-normal text-ink-2">The </span>
      <span className="font-semibold text-ink">Lumenary</span>
    </span>
  );
}
