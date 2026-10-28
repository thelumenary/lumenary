/** Locale-prefixed, trailing-slash href (the site is exported with trailingSlash: true). */
export function href(locale: string, path = ""): string {
  const [pathPart, hash] = path.replace(/^\/+/, "").split("#");
  const withSlash = pathPart && !pathPart.endsWith("/") ? `${pathPart}/` : pathPart;
  return `/${locale}/${withSlash}${hash ? `#${hash}` : ""}`;
}
