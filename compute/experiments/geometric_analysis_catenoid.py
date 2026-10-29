"""Soap films between two rings: minimal is not the same as minimising.

Two coaxial circles of radius R sit at x = -h and x = h. A catenoid
y = a cosh(x / a) spans them when R = a cosh(h / a). Writing s = h / a, this is
R / h = cosh(s) / s, which has two solutions when h / R is below a critical
value, one when it equals it, and none above it. Both solutions are minimal
surfaces (mean curvature zero), but:

* the thin catenoid always has more area than the fat one (it is unstable);
* for h / R above about 0.528 even the fat catenoid has more area than the
  two flat discs (the Goldschmidt solution), so it is only a local minimum.

Everything is computed from closed-form areas; the critical values are found
by bisection, so they are numerical approximations with stated tolerance.
"""

import math

EXPERIMENT = {
    "id": "geometric_analysis_catenoid",
    "title": "Catenoids between two rings: minimal versus minimising",
    "evidence": ["numerical"],
    "lessons": ["geometric-analysis"],
    "summary": (
        "Solves R = a cosh(h/a) for the catenoids spanning two coaxial rings, "
        "finds by bisection the critical ratio h/R = 0.6627... beyond which no "
        "catenoid exists and the ratio 0.5277... beyond which two flat discs have "
        "less area, and compares the areas of the thin catenoid, the fat catenoid "
        "and the discs: a minimal surface need not minimise area. Numerical, "
        "with closed-form areas and bisection to 1e-12."
    ),
    "packages": [],
}


def bisect(f, lo, hi, tol=1e-12):
    """A root of f in [lo, hi], assuming f(lo) and f(hi) have opposite signs."""
    flo = f(lo)
    for _ in range(200):
        mid = (lo + hi) / 2
        fm = f(mid)
        if (fm > 0) == (flo > 0):
            lo, flo = mid, fm
        else:
            hi = mid
        if hi - lo < tol:
            break
    return (lo + hi) / 2


#: s* with s tanh s = 1: where cosh(s)/s is smallest.
S_STAR = bisect(lambda s: s * math.tanh(s) - 1, 0.5, 2.0)
#: The largest h/R for which a catenoid spans the rings.
CRITICAL_RATIO = S_STAR / math.cosh(S_STAR)


def catenoid_parameters(h, R):
    """The parameters a of the catenoids through (+-h, R): (fat, thin)."""
    g = lambda s: math.cosh(s) / s - R / h
    if h / R > CRITICAL_RATIO:
        return ()
    s_fat = bisect(g, 1e-9, S_STAR)
    s_thin = bisect(g, S_STAR, 50.0)
    return (h / s_fat, h / s_thin)


def catenoid_area(a, h):
    """Area of y = a cosh(x/a), |x| <= h, rotated about the x-axis."""
    return 2 * math.pi * a * h + math.pi * a * a * math.sinh(2 * h / a)


def euler_lagrange_residual(a, x):
    """y y'' - (1 + y'^2) for y = a cosh(x/a); zero for a minimal profile."""
    y, yp, ypp = a * math.cosh(x / a), math.sinh(x / a), math.cosh(x / a) / a
    return y * ypp - (1 + yp * yp)


def goldschmidt_ratio():
    """h/R (R = 1) at which the fat catenoid and the two discs have equal area."""
    def diff(h):
        fat = catenoid_parameters(h, 1.0)[0]
        return catenoid_area(fat, h) - 2 * math.pi
    return bisect(diff, 0.3, CRITICAL_RATIO - 1e-9)


def main():
    print(f"s tanh s = 1 at s* = {S_STAR:.10f}")
    print(f"Critical ratio h/R = s*/cosh(s*) = {CRITICAL_RATIO:.10f}")
    print(f"Discs beat the fat catenoid for h/R > {goldschmidt_ratio():.10f}")
    print()
    print("Rings of radius R = 1 at x = -h, h. Areas (two discs: 2 pi = 6.2832)")
    print("   h    a(fat)   a(thin)  A(fat)   A(thin)  least area")
    for h in (0.2, 0.4, 0.5, 0.55, 0.6, 0.65, 0.67):
        params = catenoid_parameters(h, 1.0)
        if not params:
            print(f"{h:5.2f}   no catenoid spans the rings: the film breaks")
            continue
        fat, thin = params
        af, at = catenoid_area(fat, h), catenoid_area(thin, h)
        best = "fat catenoid" if af < 2 * math.pi else "two discs"
        print(f"{h:5.2f}  {fat:7.4f}  {thin:7.4f}  {af:7.4f}  {at:7.4f}  {best}")
    res = max(abs(euler_lagrange_residual(a, x)) for a in (0.3, 0.8)
              for x in (-0.5, 0.0, 0.5))
    print(f"Euler-Lagrange residual y y'' - (1 + y'^2): max {res:.1e}")
    print()
    print("Epistemic status: numerical. The areas are closed-form expressions")
    print("evaluated in floating point, and the critical ratios come from")
    print("bisection to about 1e-12. That both catenoids are minimal is the")
    print("exact identity proved in Lean; that the thin one is unstable, and")
    print("which film minimises area among all surfaces, are classical results")
    print("that this program does not check.")


if __name__ == "__main__":
    main()
