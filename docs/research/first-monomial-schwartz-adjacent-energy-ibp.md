# Real Schwartz adjacent-energy integration by parts

Base checkpoint: `f23c46ce`.

This file prepares to discharge the explicit adjacent energy inequalities in
`FirstMonomialTriadLowQuarterPoint3CriticalHalfLogConvexBridge.lean`. The
Mathlib real line-derivative integration-by-parts theorem is specialized to
arbitrary real Schwartz functions; every product is integrable because each
factor belongs to L2. The resulting identities apply to all nine physical
first-order and all 27 ordered second-order energy slots.

These are actual Euclidean Schwartz integrals rather than Fourier scalar
surrogates, and they require no solenoidality, PDE trajectory, or boundedness
hypotheses. They do not themselves establish the adjacent inequalities:
Cauchy--Schwarz on the full indexed sums and mixed-derivative rearrangement
remain necessary. We deliberately do not assert those results yet.
