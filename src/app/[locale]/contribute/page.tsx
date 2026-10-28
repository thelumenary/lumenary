import type { Metadata } from "next";
import { getT, resolveLocale } from "@/i18n/server";
import { getPage } from "@/lib/content";
import { ProsePage } from "@/components/site/ProsePage";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  return { title: getPage("contribute", await resolveLocale(params)).frontmatter.title };
}

export default async function ContributePage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  return <ProsePage slug="contribute" locale={locale} t={await getT(locale)} eyebrow={(await getT(locale))("meta.siteName")} />;
}
