import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure

/-!
# Differentiate the arbitrary-radial selected projected RHS

On every positive selected compact slab,

    R_m(t)
      =
    -((2π)^2) • V_{m+2}(t) - F_m(t).

The first term already has derivative

    -((2π)^2) • R_{m+2}(t),

because the arbitrary-radial selected velocity derivative is closed at every
order at least two.  The preceding quotient checkpoint now supplies the genuine
derivative of `F_m`.

This file combines those two facts and closes the next selected PDE rung:

    d/dt R_m
      =
    -((2π)^2) • R_{m+2} - F'_m.

No new nonlinear estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedProjectedRHSTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2200000

/-! ## Extended projected-RHS path -/

/--
Order-`m` selected projected-RHS radial `L²` path, extended from the positive
compact slab to all real elapsed times by `Set.IccExtend`.
-/
noncomputable def h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlabExtension
    (m : ℕ)
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
  Set.IccExtend
    (by linarith : Q / 2 ≤ Q)
    (
      h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
        m hNS ht₀ hE hTail hQ hQR i
    )
    s

/-!
The derivative candidate is the differentiated PDE decomposition.
-/

/--
Canonical order-`m` radial time derivative candidate for the selected
projected RHS.
-/
noncomputable def h3PreterminalSelectedProjectedRHSTimeDerivativeNatRadialFourierL2OnSlab
    (m : ℕ)
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
  (-((2 * Real.pi) ^ 2 : ℝ)) •
      h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
        (m + 2) hNS ht₀ hE hTail hQ hQR i s
    -
  h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
    m hNS ht₀ hE hTail hQ hQR i s

/-! ## Local PDE identity -/

/--
Near any strict interior slab point, the extended projected-RHS path is exactly
the differentiated-PDE source path

    `-((2π)^2) • V_{m+2} - F_m`.
-/
theorem h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlabExtension_eventuallyEq_pde
    (m : ℕ)
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
    let V : ℝ → H3FourierComplexL2 :=
      Set.IccExtend
        (by linarith : Q / 2 ≤ Q)
        (
          fun s : Set.Icc (Q / 2) Q =>
            h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
              (m + 2) (by omega)
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState
                hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              (by positivity : 0 < Q / 2)
              hQR s i
        )
    let F : ℝ → H3FourierComplexL2 :=
      h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
        m hNS ht₀ hE hTail hQ hQR i
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlabExtension
        m hNS ht₀ hE hTail hQ hQR i
      =ᶠ[𝓝 x]
    (fun r : ℝ =>
      (-((2 * Real.pi) ^ 2 : ℝ)) • V r - F r) := by

  dsimp only

  let hHalfLe : Q / 2 ≤ Q := by
    linarith

  let Vclosed :
      Set.Icc (Q / 2) Q → H3FourierComplexL2 :=
    fun s =>
      h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
        (m + 2) (by omega)
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        (by positivity : 0 < Q / 2)
        hQR s i

  let Fclosed :
      Set.Icc (Q / 2) Q → H3FourierComplexL2 :=
    fun s =>
      h3SelectedRestartForcingRadialFourierL2OnSlab
        m
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        hQ hQR.le i s

  let Rclosed :
      Set.Icc (Q / 2) Q → H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      m hNS ht₀ hE hTail hQ hQR i

  let V : ℝ → H3FourierComplexL2 :=
    Set.IccExtend hHalfLe Vclosed

  let F : ℝ → H3FourierComplexL2 :=
    Set.IccExtend hHalfLe Fclosed

  let R : ℝ → H3FourierComplexL2 :=
    Set.IccExtend hHalfLe Rclosed

  have hInterior :
      Set.Icc (Q / 2) Q ∈ 𝓝 x :=
    Icc_mem_nhds hx.1 hx.2

  have hEq :
      R =ᶠ[𝓝 x]
      (fun r : ℝ =>
        (-((2 * Real.pi) ^ 2 : ℝ)) • V r - F r) := by

    filter_upwards [hInterior] with r hr

    dsimp only [R, V, F]

    rw [
      Set.IccExtend_of_mem hHalfLe Rclosed hr,
      Set.IccExtend_of_mem hHalfLe Vclosed hr,
      Set.IccExtend_of_mem hHalfLe Fclosed hr
    ]

    dsimp only [
      Rclosed,
      Vclosed,
      Fclosed,
      h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
    ]

  change
    R =ᶠ[𝓝 x]
      (fun r : ℝ =>
        (-((2 * Real.pi) ^ 2 : ℝ)) • V r - F r)

  exact hEq

/-! ## Genuine projected-RHS derivative -/

/--
At every strict interior positive slab point, the arbitrary-radial selected
projected RHS has a genuine strong Fourier `L²` derivative equal to the
differentiated PDE candidate.
-/
theorem h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlabExtension_hasDerivAt
    (m : ℕ)
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
        h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlabExtension
          m hNS ht₀ hE hTail hQ hQR i
      )
      (
        h3PreterminalSelectedProjectedRHSTimeDerivativeNatRadialFourierL2OnSlab
          m hNS ht₀ hE hTail hQ hQR i
          ⟨x, hx.1.le, hx.2.le⟩
      )
      x := by

  let c : ℝ :=
    -((2 * Real.pi) ^ 2 : ℝ)

  let V : ℝ → H3FourierComplexL2 :=
    Set.IccExtend
      (by linarith : Q / 2 ≤ Q)
      (
        fun s : Set.Icc (Q / 2) Q =>
          h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
            (m + 2) (by omega)
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalSelectedDecoderAnchorState
              hNS ht₀ hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le
              hNS ht₀ hE hTail)
            (by positivity : 0 < Q / 2)
            hQR s i
      )

  let F : ℝ → H3FourierComplexL2 :=
    h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
      m hNS ht₀ hE hTail hQ hQR i

  let RV : H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      (m + 2) hNS ht₀ hE hTail hQ hQR i
      ⟨x, hx.1.le, hx.2.le⟩

  let DF : H3FourierComplexL2 :=
    h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
      m hNS ht₀ hE hTail hQ hQR i
      ⟨x, hx.1.le, hx.2.le⟩

  have hV :
      HasDerivAt V RV x := by
    dsimp only [V, RV]
    exact
      h3PreterminalSelectedVelocityNatRadialFourierL2OnSlab_hasDerivAt
        (m + 2) (by omega)
        hNS ht₀ hE hTail hQ hQR i hx

  have hF :
      HasDerivAt F DF x := by
    dsimp only [F, DF]
    exact
      h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension_hasDerivAt
        m hNS ht₀ hE hTail hQ hQR i hx

  have hScaled :
      HasDerivAt
        (fun r : ℝ => c • V r)
        (c • RV)
        x := by
    exact
      HasDerivAt.fun_const_smul c hV

  have hPDE :
      HasDerivAt
        (fun r : ℝ => c • V r - F r)
        (c • RV - DF)
        x :=
    hScaled.sub hF

  have hEq :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlabExtension_eventuallyEq_pde
      m hNS ht₀ hE hTail hQ hQR i hx

  have hTransport :
      HasDerivAt
        (
          h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlabExtension
            m hNS ht₀ hE hTail hQ hQR i
        )
        (c • RV - DF)
        x :=
    hPDE.congr_of_eventuallyEq hEq.symm

  dsimp only [
    c,
    RV,
    DF,
    h3PreterminalSelectedProjectedRHSTimeDerivativeNatRadialFourierL2OnSlab
  ] at hTransport ⊢

  exact hTransport

end

end Euclidean
end Bridge
end PrimeTensor
