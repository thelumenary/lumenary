"use client";

import { Cat } from "lucide-react";
import { useEffect, useState } from "react";
import { useI18n } from "@/i18n/client";
import { CATS_KEY as KEY } from "./init-scripts";

/**
 * Shows or hides the three cat guides (their portraits and names) everywhere on the site. They are
 * shown by default; anything marked `data-cat` is hidden by CSS while `<html data-cats="hidden">`.
 * The icon sits in the site header; the text variant sits next to a lesson's guides.
 */
export function CatToggle({ variant = "icon" }: { variant?: "icon" | "text" }) {
  const { t } = useI18n();
  const [hidden, setHidden] = useState(false);

  useEffect(() => {
    setHidden(document.documentElement.getAttribute("data-cats") === "hidden");
  }, []);

  const toggle = () => {
    const value = !hidden;
    setHidden(value);
    if (value) document.documentElement.setAttribute("data-cats", "hidden");
    else document.documentElement.removeAttribute("data-cats");
    try {
      if (value) localStorage.setItem(KEY, "hidden");
      else localStorage.removeItem(KEY);
    } catch {}
  };

  const action = hidden ? t("cats.show") : t("cats.hide");
  if (variant === "text")
    return (
      <button type="button" onClick={toggle} className="text-sm text-muted underline decoration-line-2 underline-offset-4 hover:text-ink">
        {action}
      </button>
    );
  return (
    <button
      type="button"
      onClick={toggle}
      aria-pressed={!hidden}
      className="relative inline-flex h-9 w-9 items-center justify-center rounded-full text-ink-2 hover:bg-paper-2 hover:text-ink"
      aria-label={t("cats.label")}
      title={action}
    >
      <Cat size={18} aria-hidden="true" className={hidden ? "opacity-45" : ""} />
      {hidden && <span className="absolute h-[22px] w-[2px] rotate-45 rounded-full bg-current" aria-hidden="true" />}
    </button>
  );
}
