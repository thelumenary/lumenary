"use client";

import { useEffect, useState } from "react";

/**
 * Optional, privacy-preserving progress tracking. Off by default; when on,
 * everything stays in this browser's localStorage. No accounts, no network,
 * no streaks, no rankings.
 */
const KEY = "lumenary:progress:v1";
const ENABLED = "lumenary:progress:enabled";
const EVENT = "lumenary:progress";

export interface ProgressStore {
  version: 1;
  lessons: Record<string, { visitedAt: string }>;
  exercises: Record<string, { solved: boolean; attempts: number; updatedAt: string }>;
  trails: Record<string, { visitedAt: string }>;
}

const empty = (): ProgressStore => ({ version: 1, lessons: {}, exercises: {}, trails: {} });

function safeGet(key: string): string | null {
  try {
    return localStorage.getItem(key);
  } catch {
    return null;
  }
}
function safeSet(key: string, value: string | null) {
  try {
    if (value === null) localStorage.removeItem(key);
    else localStorage.setItem(key, value);
  } catch {}
}

export function isEnabled(): boolean {
  return safeGet(ENABLED) === "1";
}

export function setEnabled(on: boolean) {
  safeSet(ENABLED, on ? "1" : null);
  if (!on) safeSet(KEY, null);
  window.dispatchEvent(new Event(EVENT));
}

export function load(): ProgressStore {
  const raw = safeGet(KEY);
  if (!raw) return empty();
  try {
    const parsed = JSON.parse(raw) as ProgressStore;
    return parsed.version === 1 ? { ...empty(), ...parsed } : empty();
  } catch {
    return empty();
  }
}

function save(store: ProgressStore) {
  if (!isEnabled()) return;
  safeSet(KEY, JSON.stringify(store));
  window.dispatchEvent(new Event(EVENT));
}

export function recordLesson(slug: string) {
  if (!isEnabled()) return;
  const s = load();
  s.lessons[slug] = { visitedAt: new Date().toISOString() };
  save(s);
}

export function recordTrail(slug: string) {
  if (!isEnabled()) return;
  const s = load();
  s.trails[slug] = { visitedAt: new Date().toISOString() };
  save(s);
}

export function recordAttempt(id: string, solved: boolean) {
  if (!isEnabled()) return;
  const s = load();
  const prev = s.exercises[id] ?? { solved: false, attempts: 0, updatedAt: "" };
  s.exercises[id] = { solved: prev.solved || solved, attempts: prev.attempts + 1, updatedAt: new Date().toISOString() };
  save(s);
}

export function replaceAll(store: ProgressStore) {
  save({ ...empty(), ...store, version: 1 });
}

export function clearAll() {
  safeSet(KEY, null);
  window.dispatchEvent(new Event(EVENT));
}

export function useProgress() {
  const [state, setState] = useState<{ enabled: boolean; store: ProgressStore }>({ enabled: false, store: empty() });
  useEffect(() => {
    const sync = () => setState({ enabled: isEnabled(), store: load() });
    sync();
    window.addEventListener(EVENT, sync);
    window.addEventListener("storage", sync);
    return () => {
      window.removeEventListener(EVENT, sync);
      window.removeEventListener("storage", sync);
    };
  }, []);
  return state;
}
