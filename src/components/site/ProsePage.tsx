import { LOCALE_META, type Locale } from "@/i18n/config";
import type { TFunction } from "@/i18n/dictionary";
import { getPage } from "@/lib/content";
import { renderMdx, type MdxComponents } from "@/lib/mdx";
import { makeBlocks } from "@/components/lesson/blocks";
import { PageHeader } from "@/components/ui/PageHeader";
import { TranslationNotice } from "@/components/lesson/TranslationNotice";

/** Renders an MDX prose page from content/pages/<slug>/<locale>.mdx with English fallback. */
export async function ProsePage({ slug, locale, t, eyebrow, children, components = {} }: { slug: string; locale: Locale; t: TFunction; eyebrow?: string; children?: React.ReactNode; components?: MdxComponents }) {
  const page = getPage(slug, locale);
  const body = await renderMdx(page.body, { ...makeBlocks(t), ...components });
  const lang = { lang: page.locale, dir: LOCALE_META[page.locale].dir };
  return (
    <>
      <PageHeader eyebrow={eyebrow} title={page.frontmatter.title} lead={page.frontmatter.lead} />
      <div className="container-page py-12">
        <div className="mx-auto max-w-3xl">
          <TranslationNotice t={t} requested={locale} rendered={page.locale} fallback={page.fallback} stale={page.stale} status={page.frontmatter.translation.status} />
          <div className="prose-ui mt-2" {...lang}>
            {body}
          </div>
        </div>
        {children}
      </div>
    </>
  );
}
