# Full second-jet L6 to E3 bridge

**Base:** `8dee5190` (aggregate quantitative L6 Sobolev over all 27 second jets).

The previously established 27-slot homogeneous Sobolev sum uses squared
`eLpNorm` seminorms in `ℝ≥0∞`, while the full 81-slot `E3` comparison is
in `ℝ`. The missing representation step is now explicit:

`(eLpNorm F 2 volume)^2 = ENNReal.ofReal (∫ x, ‖F x‖^2)`

for every actual L2 physical Fréchet field. A Schwartz pullback provides
`MemLp` without a new hypothesis. Finite nonnegative sums preserve `ofReal`.
The resulting bound is

`sum_27 (eLpNorm secondJet 6)^2 ≤ S^2 * ofReal(card(Axis.three) * E3(f))`.

The dimension factor is the cardinality of the intrinsic Depth.three axes,
not an unproved isometry between physical sup norm and Hilbert norm. This
is a classical Schwartz-space estimate; no Navier--Stokes conclusion is claimed.

No axioms or `sorry` introduced; local Lean compilation required.
