import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.Projected

/-!
# Intrinsic q-weighted selected forcing derivatives

The arbitrary-radial forcing derivative has now been closed at every natural
order.  The two terminal Hilbert frontiers that remain use the intrinsic
Fourier square-gradient factor

    q(ξ) = (2π)^2 |ξ|^2.

Hence their forcing paths are fixed scalar multiples of the already-closed
radial orders:

    q F_j   = (2π)^2 |ξ|^2 F_j,
    q^2 F_j = (2π)^4 |ξ|^4 F_j.

This file packages those two selected paths and transfers the strong radial
derivative theorem through the fixed real scalar factors.  No new estimate is
introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/-! ## q F -/

/--
Selected `q F_j` path on a positive compact restart slab, extended to all real
elapsed times.
-/
noncomputable def h3PreterminalSelectedForcingSecondQFourierL2OnSlabExtension
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : ℝ) :
    H3FourierComplexL2 :=
  ((2 * Real.pi) ^ 2 : ℝ) •
    h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
      2 hNS ht₀ hE hTail hQ hQR i s

/--
Canonical derivative candidate for the selected `q F_j` path.
-/
noncomputable def h3PreterminalSelectedForcingSecondQTimeDerivativeFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    H3FourierComplexL2 :=
  ((2 * Real.pi) ^ 2 : ℝ) •
    h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
      2 hNS ht₀ hE hTail hQ hQR i s

/--
The selected intrinsic `q F_j` path has a genuine strong Fourier `L²`
derivative at every strict interior slab time.
-/
theorem h3PreterminalSelectedForcingSecondQFourierL2OnSlabExtension_hasDerivAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    HasDerivAt
      (
        h3PreterminalSelectedForcingSecondQFourierL2OnSlabExtension
          hNS ht₀ hE hTail hQ hQR i
      )
      (
        h3PreterminalSelectedForcingSecondQTimeDerivativeFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR i
          ⟨x, hx.1.le, hx.2.le⟩
      )
      x := by

  have hBase :=
    h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension_hasDerivAt
      2 hNS ht₀ hE hTail hQ hQR i hx

  have hScaled :
      HasDerivAt
        (
          fun s : ℝ =>
            ((2 * Real.pi) ^ 2 : ℝ) •
              h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
                2 hNS ht₀ hE hTail hQ hQR i s
        )
        (
          ((2 * Real.pi) ^ 2 : ℝ) •
            h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
              2 hNS ht₀ hE hTail hQ hQR i
              ⟨x, hx.1.le, hx.2.le⟩
        )
        x :=
    HasDerivAt.fun_const_smul
      ((2 * Real.pi) ^ 2 : ℝ)
      hBase

  change
    HasDerivAt
      (
        fun s : ℝ =>
          ((2 * Real.pi) ^ 2 : ℝ) •
            h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
              2 hNS ht₀ hE hTail hQ hQR i s
      )
      (
        ((2 * Real.pi) ^ 2 : ℝ) •
          h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
            2 hNS ht₀ hE hTail hQ hQR i
            ⟨x, hx.1.le, hx.2.le⟩
      )
      x

  exact hScaled

/-! ## q² F -/

/--
Selected `q² F_j` path on a positive compact restart slab, extended to all real
elapsed times.
-/
noncomputable def h3PreterminalSelectedForcingFourthQFourierL2OnSlabExtension
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : ℝ) :
    H3FourierComplexL2 :=
  ((2 * Real.pi) ^ 4 : ℝ) •
    h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
      4 hNS ht₀ hE hTail hQ hQR i s

/--
Canonical derivative candidate for the selected `q² F_j` path.
-/
noncomputable def h3PreterminalSelectedForcingFourthQTimeDerivativeFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    H3FourierComplexL2 :=
  ((2 * Real.pi) ^ 4 : ℝ) •
    h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
      4 hNS ht₀ hE hTail hQ hQR i s

/--
The selected intrinsic `q² F_j` path has a genuine strong Fourier `L²`
derivative at every strict interior slab time.
-/
theorem h3PreterminalSelectedForcingFourthQFourierL2OnSlabExtension_hasDerivAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    HasDerivAt
      (
        h3PreterminalSelectedForcingFourthQFourierL2OnSlabExtension
          hNS ht₀ hE hTail hQ hQR i
      )
      (
        h3PreterminalSelectedForcingFourthQTimeDerivativeFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR i
          ⟨x, hx.1.le, hx.2.le⟩
      )
      x := by

  have hBase :=
    h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension_hasDerivAt
      4 hNS ht₀ hE hTail hQ hQR i hx

  have hScaled :
      HasDerivAt
        (
          fun s : ℝ =>
            ((2 * Real.pi) ^ 4 : ℝ) •
              h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
                4 hNS ht₀ hE hTail hQ hQR i s
        )
        (
          ((2 * Real.pi) ^ 4 : ℝ) •
            h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
              4 hNS ht₀ hE hTail hQ hQR i
              ⟨x, hx.1.le, hx.2.le⟩
        )
        x :=
    HasDerivAt.fun_const_smul
      ((2 * Real.pi) ^ 4 : ℝ)
      hBase

  change
    HasDerivAt
      (
        fun s : ℝ =>
          ((2 * Real.pi) ^ 4 : ℝ) •
            h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
              4 hNS ht₀ hE hTail hQ hQR i s
      )
      (
        ((2 * Real.pi) ^ 4 : ℝ) •
          h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
            4 hNS ht₀ hE hTail hQ hQR i
            ⟨x, hx.1.le, hx.2.le⟩
      )
      x

  exact hScaled

end

end Euclidean
end Bridge
end PrimeTensor
