import type { Metadata } from "next";
import { getT, resolveLocale } from "@/i18n/server";
import { getPage } from "@/lib/content";
import { ProsePage } from "@/components/site/ProsePage";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  return { title: getPage("about", await resolveLocale(params)).frontmatter.title };
}

export default async function AboutPage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  return <ProsePage slug="about" locale={locale} t={await getT(locale)} eyebrow={(await getT(locale))("meta.siteName")} />;
}
