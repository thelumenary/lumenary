export function PageHeader({ eyebrow, title, lead, children }: { eyebrow?: string; title: string; lead?: string; children?: React.ReactNode }) {
  return (
    <div className="relative overflow-hidden border-b border-line">
      <div className="bg-grid pointer-events-none absolute inset-0 opacity-50 [mask-image:radial-gradient(ellipse_at_top,black,transparent_70%)]" aria-hidden="true" />
      <div className="container-page relative py-12 sm:py-16">
        {eyebrow && <p className="eyebrow">{eyebrow}</p>}
        <h1 className="mt-2 max-w-3xl text-4xl font-semibold leading-[1.1] text-ink sm:text-5xl">{title}</h1>
        {lead && <p className="mt-5 max-w-2xl text-lg leading-relaxed text-ink-2">{lead}</p>}
        {children}
      </div>
    </div>
  );
}
