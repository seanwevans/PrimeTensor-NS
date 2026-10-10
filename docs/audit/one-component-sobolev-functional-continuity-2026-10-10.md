# Homogeneous three-halves Fourier mass: continuity and time measurability boundary

**Baseline:** `6153f0c6` (`prove physical homogeneous H3/2 Fourier density dominated by H3 endpoint`).

## Proved in `H3/Audit/OneComponentSobolevFunctionalContinuity.lean`

With the actual native Fourier gradient square `q(ξ)=(2π)²‖ξ‖²` and
`W₃(ξ)²=1+q+q²+q³`, define the real Fourier coefficient

    m(ξ) = sqrt(sqrt(q(ξ)^3)) / W₃(ξ).

The preceding checkpoint proved `sqrt(q³) <= W₃²`; thus `0 <= m <= 1`.
Multiplication by this coefficient is a contraction on the complete scalar
weighted Fourier `L²` state. The module constructs the multiplier as a complex
continuous linear map, verifies the exact square-mass identity

    ∫ sqrt(q³) |W₃⁻¹ G|² = ‖m G‖²,

and concludes that the actual homogeneous `Ḣ^(3/2)` Fourier square mass is
continuous in the native H³ spectral state `G`.

For a preterminal velocity component, the previous code defined its actual
homogeneous time density by spatial Fourier integration. This new continuity
statement makes that time density Borel measurable **if the canonical
spectral-state time map is measurable**. It then imports the existing terminal
integrability proof for both transverse velocity components on the same late
interval. The scalar density's measurability is no longer assumed separately.

## What remains genuinely unproved

1. Show measurability (preferably strong local continuity) of the *actual*
   canonical spectral velocity path from `LoggedPreterminalH3PathAdmissible`.
   The strong endpoint modulus at `T` is not, alone, a proof of measurability
   at all strict earlier times. Relevant existing work includes the canonical
   selected/old spectral path and local Fourier-jet continuity interfaces.
2. Check exact compatibility with the published one-component theorem's
   function spaces and strong-solution class, and formalize its continuation
   conclusion. No published theorem is imported as an axiom here.
3. Recover the criterion on a complete compact-preterminal-to-terminal window
   if the chosen external formulation is not tail-local; this can be based on
   scalar H³-energy continuity plus the new Fourier norm comparison.

## Scope

These are conditional bounds for an endpoint hypothesis. They do not assert
unconditional regularity, nonextension, or Clay Form A. The new component
contains no `sorry`, `admit`, or new axiom declarations. A local Lean and Lake
build is needed for kernel verification.

## Lean elaboration corrections (fix 1)

The Sobolev multiplier continuity proof now composes the existing exact inverse H³-frequency-weight continuity lemma rather than relying on `fun_prop` to discover it. The Fourier `Lp` add/smul representative identities are exposed before applying a.e. multiplier equalities. The quarter-root square is rewritten through an explicit intermediate equality. The `Lp` state carries its canonical Borel measurable-space structure locally (not a new PDE assumption), and the multiplier maps zero to zero through the actual continuous linear operator.
