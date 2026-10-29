"use client";

import { useEffect, useRef, useSyncExternalStore } from "react";

/** Convert a pointer position to the SVG's user (viewBox) coordinates. */
export function svgPoint(svg: SVGSVGElement | null, clientX: number, clientY: number): [number, number] | null {
  if (!svg) return null;
  const ctm = svg.getScreenCTM();
  if (ctm) {
    const inv = ctm.inverse();
    return [inv.a * clientX + inv.c * clientY + inv.e, inv.b * clientX + inv.d * clientY + inv.f];
  }
  const rect = svg.getBoundingClientRect();
  const vb = svg.viewBox.baseVal;
  if (!rect.width || !rect.height || !vb) return null;
  return [vb.x + ((clientX - rect.left) / rect.width) * vb.width, vb.y + ((clientY - rect.top) / rect.height) * vb.height];
}

const QUERY = "(prefers-reduced-motion: reduce)";
function subscribe(cb: () => void) {
  if (typeof window === "undefined" || !window.matchMedia) return () => {};
  const mq = window.matchMedia(QUERY);
  mq.addEventListener("change", cb);
  return () => mq.removeEventListener("change", cb);
}

/** True when the reader asked for reduced motion (always false during server rendering). */
export function useReducedMotion(): boolean {
  return useSyncExternalStore(
    subscribe,
    () => (typeof window !== "undefined" && window.matchMedia ? window.matchMedia(QUERY).matches : false),
    () => false,
  );
}

/**
 * Run `tick(dtSeconds)` on every animation frame while `running` is true.
 * The callback may change between renders; the loop always calls the latest one.
 */
export function useAnimationLoop(running: boolean, tick: (dt: number) => void) {
  const ref = useRef(tick);
  useEffect(() => {
    ref.current = tick;
  });
  useEffect(() => {
    if (!running || typeof window === "undefined") return;
    let raf = 0;
    let last = performance.now();
    const loop = (now: number) => {
      const dt = Math.min(0.1, (now - last) / 1000);
      last = now;
      ref.current(dt);
      raf = requestAnimationFrame(loop);
    };
    raf = requestAnimationFrame(loop);
    return () => cancelAnimationFrame(raf);
  }, [running]);
}
