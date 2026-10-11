# Scalar relative-energy continuity instead of strong old–selected continuity

Base checkpoint: `ff5c6f8b` — derive canonical initial overlap from relative energy Gronwall.

The original initial relative-energy theorem assumes continuity of the **entire**
physical Hilbert-valued difference `D : ℝ → H3PhysicalRealFinVectorL2Hilbert`
on `[0,b]`. The cumulative integral argument only differentiates the scalar
`e(t) = ‖D(t)‖²`. The new independent scalar Grönwall theorem requires
`ContinuousOn e (Icc 0 b)` and `e ≥ 0`, not strong continuity of `D`.

The new `H3AuditInitialCanonicalScalarRelativeEnergyData` also preserves the
independent integral PDE estimate `e(t) ≤ K ∫₀ᵗ e(s) ds`; `K` need not be assumed
nonnegative because the energy inequality and nonnegativity of the cumulative
integral already supply the sign needed by Grönwall. A theorem transfers the
previous, stronger continuity contract to the new one.

From the scalar contract the proof obtains pointwise physical L² uniqueness,
compact weak-test equality, canonical weighted H³ overlap, physical initial L²
and H³-energy continuity, and the conditional full-time transverse intrinsic
H^(3/2) conclusion.

**Remaining obligations:** The actual Navier–Stokes relative-energy inequality,
scalar relative-energy continuity at physical time zero, the initial H³ datum,
and the independent terminal physical strong-H³ vorticity endpoint are not
proved from the open-time admissibility class in this patch.

This source is not certified by the project Lean/mathlib build until checked on
the target Rocky Linux machine. No `sorry`, `admit`, or extra axioms added.
