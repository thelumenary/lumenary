"""The Hopf fibration numerically: fibres are circles, and any two of them link.

The Hopf map h(z, w) = (2 z conj(w), |z|^2 - |w|^2) sends the unit sphere S^3
in C^2 to the unit sphere S^2. The fibre over a point p is the circle
{(lz, lw) : |l| = 1}. We sample fibres, check that h is constant on them, map
them into R^3 by stereographic projection, and evaluate Gauss's linking
integral for pairs of fibres. The answer is 1 every time: the Hopf invariant of
h, which is why h generates pi_3(S^2) = Z. Numerical evidence only.
"""

import math

import numpy as np

EXPERIMENT = {
    "id": "homotopy_theory_hopf_linking",
    "title": "Hopf fibres are linked circles",
    "evidence": ["numerical"],
    "lessons": ["homotopy-theory"],
    "summary": (
        "Samples fibres of the Hopf map S^3 -> S^2, checks numerically that the map "
        "is constant on each fibre, projects the fibres stereographically to R^3 "
        "and evaluates the Gauss linking integral for several pairs; it is 1 to "
        "about ten digits. Numerical evidence for the linking of Hopf fibres, which "
        "the lesson proves; it is not itself a proof."
    ),
    "packages": ["numpy"],
}


def hopf(z, w):
    """The Hopf map, returning a point (x, y, t) of R^3."""
    v = 2 * z * np.conj(w)
    return np.stack([v.real, v.imag, abs(z) ** 2 - abs(w) ** 2], axis=-1)


def fibre(p, n=400):
    """n points (z, w) on the fibre over the unit vector p = (a, b, c)."""
    a, b, c = p
    if c >= 0:
        z0 = math.sqrt((1 + c) / 2)
        w0 = complex(a, -b) / (2 * z0)
    else:
        w0 = math.sqrt((1 - c) / 2)
        z0 = complex(a, b) / (2 * w0)
    lam = np.exp(2j * np.pi * np.arange(n) / n)
    return lam * z0, lam * w0


def stereographic(z, w):
    """Project S^3 minus the point (0, i) to R^3."""
    return np.stack([z.real, z.imag, w.real], axis=-1) / (1 - w.imag)[:, None]


def spectral_derivative(c):
    """Derivative d/dtheta of a closed curve sampled at n equally spaced angles."""
    n = len(c)
    k = np.fft.fftfreq(n, d=1.0 / n)
    k[n // 2] = 0 if n % 2 == 0 else k[n // 2]
    return np.real(np.fft.ifft(1j * k[:, None] * np.fft.fft(c, axis=0), axis=0))


def linking_number(c1, c2):
    """Gauss linking integral of two closed curves sampled uniformly in angle.

    Uses the periodic trapezoidal rule with spectrally exact tangent vectors,
    which converges faster than any power of 1/n for smooth curves.
    """
    t1, t2 = spectral_derivative(c1), spectral_derivative(c2)
    r = c1[:, None, :] - c2[None, :, :]
    cross = np.cross(t1[:, None, :], t2[None, :, :])
    integrand = np.einsum("ijk,ijk->ij", r, cross)
    integrand /= np.linalg.norm(r, axis=-1) ** 3
    h = 2 * math.pi / len(c1) * 2 * math.pi / len(c2)
    return integrand.sum() * h / (4 * math.pi)


def round_circle(center, n=400, vertical=False):
    """A unit circle around center, horizontal or in a vertical (x, z) plane."""
    t = 2 * np.pi * np.arange(n) / n
    if vertical:
        pts = np.stack([np.cos(t), np.zeros(n), np.sin(t)], axis=-1)
    else:
        pts = np.stack([np.cos(t), np.sin(t), np.zeros(n)], axis=-1)
    return pts + np.asarray(center, dtype=float)


def unit(v):
    """Normalise a vector to a point of S^2."""
    v = np.asarray(v, dtype=float)
    return v / np.linalg.norm(v)


POINTS = {
    "north pole": unit([0, 0, 1]),
    "equator, x": unit([1, 0, 0]),
    "equator, y": unit([0, 1, 0]),
    "(1, 1, 1)": unit([1, 1, 1]),
    "(-2, 1, -1)": unit([-2, 1, -1]),
}


def main():
    print("Hopf map h : S^3 -> S^2, h(z, w) = (2 z conj(w), |z|^2 - |w|^2)")
    print()
    curves = {}
    worst = 0.0
    for name, p in POINTS.items():
        z, w = fibre(p)
        worst = max(worst, float(np.abs(hopf(z, w) - p).max()))
        curves[name] = stereographic(z, w)
    print(f"max |h(x) - p| over 400 points on each of 5 fibres: {worst:.1e}")
    print()
    print("Gauss linking numbers of the projected fibres (400 points each):")
    names = list(POINTS)
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            lk = linking_number(curves[names[i]], curves[names[j]])
            print(f"  {names[i]:<12} with {names[j]:<12} Lk = {lk:.10f}")
    flat = round_circle([0, 0, 0])
    apart = linking_number(flat, round_circle([3, 0, 0], vertical=True))
    print(f"  control: two unlinked round circles      Lk = {abs(apart):.10f}")
    print()
    print("Every pair of fibres links once. The linking number of two fibres")
    print("is the Hopf invariant H(h) = 1; a map S^3 -> S^2 homotopic to a")
    print("constant would have H = 0, so h is not null-homotopic.")
    print()
    print("Epistemic status: numerical evidence. The trapezoidal rule for")
    print("smooth closed curves converges very fast and the values agree with")
    print("the integer 1 to many digits, but floating-point quadrature proves")
    print("nothing; the lesson proves that h generates pi_3(S^2) = Z.")


if __name__ == "__main__":
    main()
