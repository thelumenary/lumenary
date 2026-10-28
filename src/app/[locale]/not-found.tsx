import Link from "next/link";

export default function NotFound() {
  return (
    <div className="container-page flex min-h-[50vh] flex-col items-center justify-center py-20 text-center">
      <p className="font-display text-7xl font-semibold text-gold">∅</p>
      <h1 className="mt-4 text-3xl font-semibold text-ink">This page is the empty set.</h1>
      <p className="mt-3 text-ink-2">It has no elements — and, sadly, no content.</p>
      <Link href="/" className="btn btn-primary mt-8">
        The Lumenary
      </Link>
    </div>
  );
}
