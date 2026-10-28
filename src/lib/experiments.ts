/** Ids of the interactive experiments that Wonder Trails can embed (see components/lesson/mdx-components.tsx). */
export const EXPERIMENT_IDS = ["inverse-finder", "clock-lab", "remainder-colors", "boxes-nesting", "arrow-composer", "product-maps", "diagonal-builder"] as const;
export type ExperimentId = (typeof EXPERIMENT_IDS)[number];
