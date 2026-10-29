"use client";

import { Monitor, Moon, Sun } from "lucide-react";
import { useEffect, useState } from "react";
import { useI18n } from "@/i18n/client";
import { THEME_KEY as KEY } from "./init-scripts";

type Theme = "system" | "light" | "dark";

function apply(theme: Theme) {
  const root = document.documentElement;
  if (theme === "system") root.removeAttribute("data-theme");
  else root.setAttribute("data-theme", theme);
}

export function ThemeToggle() {
  const { t } = useI18n();
  const [theme, setTheme] = useState<Theme>("system");

  useEffect(() => {
    try {
      const saved = localStorage.getItem(KEY);
      if (saved === "light" || saved === "dark") setTheme(saved);
    } catch {}
  }, []);

  const next = () => {
    const order: Theme[] = ["system", "light", "dark"];
    const value = order[(order.indexOf(theme) + 1) % order.length];
    setTheme(value);
    apply(value);
    try {
      if (value === "system") localStorage.removeItem(KEY);
      else localStorage.setItem(KEY, value);
    } catch {}
  };

  const Icon = theme === "light" ? Sun : theme === "dark" ? Moon : Monitor;
  return (
    <button
      type="button"
      onClick={next}
      className="inline-flex h-9 w-9 items-center justify-center rounded-full text-ink-2 hover:bg-paper-2 hover:text-ink"
      aria-label={`${t("theme.label")}: ${t(`theme.${theme}`)}`}
      title={`${t("theme.label")}: ${t(`theme.${theme}`)}`}
    >
      <Icon size={18} aria-hidden="true" />
    </button>
  );
}
