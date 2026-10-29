/** Ids of the interactive experiments that Wonder Trails can embed (see components/lesson/mdx-components.tsx). */
export const EXPERIMENT_IDS = ["inverse-finder", "clock-lab", "remainder-colors", "boxes-nesting", "arrow-composer", "product-maps", "diagonal-builder", "euler-counter", "sphere-triangles", "torus-world", "knot-colours", "winding-loops", "halving-series", "prime-sieve", "random-walk", "square-symmetries", "osculating-circles", "kepler-orbits"] as const;
export type ExperimentId = (typeof EXPERIMENT_IDS)[number];
