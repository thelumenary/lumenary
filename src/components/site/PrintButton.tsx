"use client";

import { Printer } from "lucide-react";
import { useI18n } from "@/i18n/client";

export function PrintButton() {
  const { t } = useI18n();
  return (
    <button type="button" className="btn btn-primary no-print" onClick={() => window.print()}>
      <Printer size={16} aria-hidden="true" /> {t("educators.print")}
    </button>
  );
}
