import { describe, expect, it } from "vitest";
import { normalizeDigits, parseInteger, parseSet, setsEqual } from "@/components/exercises/parse";

describe("integer answers", () => {
  it("accepts ASCII and Unicode minus signs", () => {
    expect(parseInteger("-4")).toBe(-4);
    expect(parseInteger("−4")).toBe(-4);
    expect(parseInteger(" +12 ")).toBe(12);
  });
  it("accepts regional numerals", () => {
    expect(normalizeDigits("٣٤")).toBe("34");
    expect(parseInteger("−١٢")).toBe(-12);
    expect(parseInteger("२५")).toBe(25);
    expect(parseInteger("۷")).toBe(7);
  });
  it("rejects non-integers", () => {
    expect(parseInteger("3.5")).toBeNull();
    expect(parseInteger("three")).toBeNull();
    expect(parseInteger("")).toBeNull();
  });
});

describe("set answers", () => {
  it("ignores order, repetition, case and quotes", () => {
    expect(setsEqual(parseSet("{3, 1, 2, 1}")!, new Set(["1", "2", "3"]))).toBe(true);
    expect(setsEqual(parseSet("{'Apple', strawberry}")!, new Set(["apple", "strawberry"]))).toBe(true);
    expect(setsEqual(parseSet("1,2")!, new Set(["1", "2"]))).toBe(true);
  });
  it("reads the empty set", () => {
    expect(parseSet("{}")!.size).toBe(0);
    expect(parseSet("∅")!.size).toBe(0);
  });
  it("accepts Arabic and CJK separators", () => {
    expect(setsEqual(parseSet("{١، ٢}")!, new Set(["1", "2"]))).toBe(true);
    expect(setsEqual(parseSet("｛1，2｝")!, new Set(["1", "2"]))).toBe(true);
  });
  it("rejects unbalanced or nested braces", () => {
    expect(parseSet("{1, 2")).toBeNull();
    expect(parseSet("{{1}, 2}")).toBeNull();
  });
});
