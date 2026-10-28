import type { Locale } from "./config";
import { getMessages, pickMessages } from "./dictionary";
import { I18nProvider } from "./client";

/** Server component: make extra message namespaces available to the client components inside it. */
export async function Messages({ locale, ns, children }: { locale: Locale; ns: string[]; children: React.ReactNode }) {
  const messages = await getMessages(locale);
  return (
    <I18nProvider locale={locale} messages={pickMessages(messages, ns)}>
      {children}
    </I18nProvider>
  );
}
