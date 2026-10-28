import { describe, expect, it } from "vitest";
import { ancestors, findCycle, layoutGraph } from "@/lib/graph-layout";
import { GraphFile } from "@/lib/schema";
import { json } from "./helpers";

describe("graph utilities", () => {
  it("finds cycles and accepts DAGs", () => {
    expect(findCycle([{ id: "a", prerequisites: ["b"] }, { id: "b", prerequisites: [] }])).toBeNull();
    expect(findCycle([{ id: "a", prerequisites: ["b"] }, { id: "b", prerequisites: ["a"] }])).not.toBeNull();
  });
  it("computes transitive prerequisites", () => {
    const m = new Map([
      ["c", ["b"]],
      ["b", ["a"]],
      ["a", []],
    ]);
    expect([...ancestors("c", m)].sort()).toEqual(["a", "b"]);
  });
  it("lays out every topic without overlaps", () => {
    const graph = GraphFile.parse(json("content/math/graph/graph.json"));
    const layout = layoutGraph(graph.topics);
    const nodes = Object.values(layout.nodes);
    expect(nodes).toHaveLength(graph.topics.length);
    for (let i = 0; i < nodes.length; i++)
      for (let j = i + 1; j < nodes.length; j++) {
        const a = nodes[i];
        const b = nodes[j];
        const overlap = Math.abs(a.x - b.x) < layout.nodeWidth && Math.abs(a.y - b.y) < layout.nodeHeight;
        expect(overlap, `${a.id} overlaps ${b.id}`).toBe(false);
      }
  });
});
