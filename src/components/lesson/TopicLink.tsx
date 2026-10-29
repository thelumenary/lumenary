import Link from "next/link";
import type { Locale } from "@/i18n/config";
import { getTopic } from "@/lib/content";
import { href } from "@/lib/href";

/** Inline link to another topic: its lesson when one exists, otherwise its topic page. */
export function TopicLink({ locale, id, children }: { locale: Locale; id: string; children?: React.ReactNode }) {
  const topic = getTopic(id);
  if (!topic) throw new Error(`<TopicLink id="${id}">: no such topic in the knowledge graph`);
  const to = topic.lesson ? href(locale, `math/lessons/${topic.lesson}`) : href(locale, `math/topics/${topic.id}`);
  return (
    <Link prefetch={false} href={to} className="underline decoration-gold/60 underline-offset-2 hover:decoration-gold">
      {children ?? topic.title}
    </Link>
  );
}
