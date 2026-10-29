import type { MetadataRoute } from "next";
import { LOCALES } from "@/i18n/config";
import { getComputeReport, getGraph, getLeanReport, lessonSlugs, trailSlugs } from "@/lib/content";
import { href } from "@/lib/href";

export const dynamic = "force-static";

const SITE_URL = "https://lumenary.academy";

/** Every public page in every demo locale (static export writes this to /sitemap.xml). */
export default function sitemap(): MetadataRoute.Sitemap {
  const paths = [
    "",
    "math/",
    "math/graph/",
    "math/trails/",
    "lab/",
    "formal/",
    "practice/",
    "educators/",
    "about/",
    "contribute/",
    "languages/",
    "verification/",
    ...lessonSlugs().flatMap((s) => [`math/lessons/${s}/`, `practice/${s}/`]),
    ...trailSlugs().map((s) => `math/trails/${s}/`),
    ...getGraph().topics.map((t) => `math/topics/${t.id}/`),
    ...(getComputeReport()?.experiments ?? []).map((e) => `lab/${e.id}/`),
    ...[...new Set((getLeanReport()?.declarations ?? []).map((d) => d.file.replace(/^(formal\/)?Lumenary\//, "").replace(/\.lean$/, "")))].map((m) => `formal/${m}/`),
  ];
  // href() maps pages that exist only in English to their English URL; list each page once.
  const urls = new Set(LOCALES.flatMap((locale) => paths.map((p) => `${SITE_URL}${href(locale, p)}`)));
  return [...urls].map((url) => ({ url }));
}
