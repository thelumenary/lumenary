import "../globals.css";
import type { Metadata } from "next";
import { Fraunces, Inter, JetBrains_Mono, Noto_Sans_Arabic, Noto_Sans_Devanagari, Source_Serif_4 } from "next/font/google";
import { LOCALES, LOCALE_META } from "@/i18n/config";
import { CORE_NAMESPACES, getMessages, makeT, pickMessages } from "@/i18n/dictionary";
import { I18nProvider } from "@/i18n/client";
import { resolveLocale } from "@/i18n/server";
import { SiteHeader } from "@/components/site/SiteHeader";
import { SiteFooter } from "@/components/site/SiteFooter";
import { themeInitScript } from "@/components/site/ThemeToggle";

const fraunces = Fraunces({ subsets: ["latin", "latin-ext"], variable: "--font-fraunces", axes: ["opsz", "SOFT"], display: "swap" });
const inter = Inter({ subsets: ["latin", "latin-ext"], variable: "--font-inter", display: "swap" });
const sourceSerif = Source_Serif_4({ subsets: ["latin", "latin-ext"], variable: "--font-source-serif", display: "swap", style: ["normal", "italic"] });
const jetbrains = JetBrains_Mono({ subsets: ["latin"], variable: "--font-jetbrains", display: "swap" });
const notoArabic = Noto_Sans_Arabic({ subsets: ["arabic"], variable: "--font-noto-arabic", display: "swap", preload: false });
const notoDeva = Noto_Sans_Devanagari({ subsets: ["devanagari"], variable: "--font-noto-deva", display: "swap", preload: false });

export const dynamicParams = false;

export function generateStaticParams() {
  return LOCALES.map((locale) => ({ locale }));
}

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  const locale = await resolveLocale(params);
  const t = makeT(await getMessages(locale));
  return {
    title: { default: `${t("meta.siteName")} — ${t("meta.tagline")}`, template: `%s · ${t("meta.siteName")}` },
    description: t("meta.description"),
    alternates: { languages: Object.fromEntries(LOCALES.map((l) => [l, `/${l}/`])) },
    icons: { icon: "/favicon.svg" },
  };
}

export default async function LocaleLayout({ children, params }: { children: React.ReactNode; params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const messages = await getMessages(locale);
  const t = makeT(messages);
  const fonts = [fraunces, inter, sourceSerif, jetbrains, notoArabic, notoDeva].map((f) => f.variable).join(" ");
  return (
    <html lang={locale} dir={LOCALE_META[locale].dir} className={fonts} suppressHydrationWarning>
      <head>
        <script dangerouslySetInnerHTML={{ __html: themeInitScript }} />
      </head>
      <body className="min-h-screen">
        <I18nProvider locale={locale} messages={pickMessages(messages, CORE_NAMESPACES)}>
          <a href="#main" className="sr-only z-50 rounded-full bg-ink px-4 py-2 text-paper focus:not-sr-only focus:fixed focus:start-4 focus:top-3">
            {t("nav.skip")}
          </a>
          <SiteHeader />
          <main id="main" tabIndex={-1} className="outline-none">
            {children}
          </main>
          <SiteFooter locale={locale} t={t} />
        </I18nProvider>
      </body>
    </html>
  );
}
