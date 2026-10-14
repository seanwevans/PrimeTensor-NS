# Uniform positive tube for all twelve sharp triad sectors

Checkpoint: `9df43a84`.

## What is new

The six positive and six Hermitian-reflected sharp center pairs form a **finite compact** subset `lowNormalQuarterCoherentCenterSet` of the momentum-plane parameter space `(Fin 3 → ℝ) × (Fin 3 → ℝ)`.

At each center the genuine Schwartz-field signed kernel is `9/64`. By continuity and compactness of the entire orbit, there exists **one** `δ > 0` for which its value is **strictly greater than `9/128`** throughout the closed δ-thickening of the twelve-point set. This is a uniform local result, not twelve unrelated radii.

The closed δ-thickening is compact, hence the signed kernel is integrable there. Since it contains an open ball centered at a resonant point, that set has positive volume. Its signed integral is therefore strictly positive.

## What remains open

The currently constructed six-packet Schwartz field has frequency-cutoff outer radius `min(1, |t|)/4 = 1/16` at `t=1/4`. Nothing yet establishes that the **whole support of the trilinear signed kernel** lies within the positive tube supplied by continuity. Without that support inclusion, a strictly positive integral over the tube does not imply a positive full-space integral.

A conditional theorem names precisely the required inclusion and assumes full integrability. The next step is to construct adjustable narrower Schwartz frequency packets, show their nonzero triad kernel only sees coherent triples, and choose packet width below the uniform radius (accounting for all three momentum-conserving frequency errors). Only then may global noncancellation be deduced.

No singularity or continuation theorem follows from these local-sign calculations alone.
