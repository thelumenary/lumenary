"use client";

import { useEffect, useRef } from "react";

/** A small, accessible code editor: a monospace textarea with sensible Tab handling and auto-height. */
export function CodeEditor({ value, onChange, label, minRows = 6 }: { value: string; onChange: (v: string) => void; label: string; minRows?: number }) {
  const ref = useRef<HTMLTextAreaElement>(null);
  useEffect(() => {
    const el = ref.current;
    if (!el) return;
    el.style.height = "auto";
    el.style.height = `${el.scrollHeight + 2}px`;
  }, [value]);
  return (
    <textarea
      ref={ref}
      aria-label={label}
      spellCheck={false}
      autoCapitalize="off"
      autoCorrect="off"
      dir="ltr"
      rows={minRows}
      value={value}
      onChange={(e) => onChange(e.target.value)}
      onKeyDown={(e) => {
        if (e.key === "Tab" && !e.shiftKey && !e.altKey && !e.metaKey && !e.ctrlKey) {
          // Escape releases focus for keyboard users (Tab inserts spaces only while editing).
          e.preventDefault();
          const el = e.currentTarget;
          const { selectionStart: s, selectionEnd: end } = el;
          const next = value.slice(0, s) + "    " + value.slice(end);
          onChange(next);
          requestAnimationFrame(() => el.setSelectionRange(s + 4, s + 4));
        } else if (e.key === "Escape") {
          e.currentTarget.blur();
        }
      }}
      className="block w-full resize-none bg-transparent px-4 py-3.5 font-mono text-[0.84rem] leading-[1.65] text-ink outline-none"
    />
  );
}
