import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Raw.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Integral.Bridge

/-!
# Spectral selected slope error and exact raw-Fourier bridge

The preceding radial checkpoint gives strong convergence of every natural
radial velocity slope error, while the nonlinear forcing map consumes genuine
weighted H³ spectral states.

This file installs the exact representation bridge.  The selected raw Fourier
coordinate derivative is taken from the already-proved scalar theorem rather
than re-projecting the vector derivative through an ambiguous real module
instance.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedSpectralSlopeError
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-! ## Real scalar linearity of exact deweighting -/

/--
Exact scalar deweighting commutes with real scalar multiplication.
-/
@[simp]
theorem h3SpectralScalarRawFourierL2_smul_real
    (c : ℝ)
    (G : H3SpectralScalarState) :
    h3SpectralScalarRawFourierL2 (c • G)
      =
    c • h3SpectralScalarRawFourierL2 G := by

  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3SpectralScalarRawFourierL2_ae (c • G),
    h3SpectralScalarRawFourierL2_ae G,
    MeasureTheory.Lp.coeFn_smul c G,
    MeasureTheory.Lp.coeFn_smul c
      (h3SpectralScalarRawFourierL2 G)
  ] with ξ hLeft hG hIn hOut

  rw [hLeft, hOut]

  change
    h3SpectralScalarRawFourier (c • G) ξ
      =
    c •
      (h3SpectralScalarRawFourierL2 G :
        H3FourierPoint3 → ℂ) ξ

  rw [hG]

  unfold h3SpectralScalarRawFourier

  rw [hIn]

  simp only [
    Pi.smul_apply,
    Complex.real_smul
  ]

  ring

/-! ## Raw slope error -/

/--
Coordinatewise raw Fourier slope error of the selected velocity.
-/
noncomputable def h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab
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
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ) :
    H3FourierComplexL2 :=
  h⁻¹ •
      (
        h3SelectedRestartVelocityRawFourierVector
            hNS ht₀ hE hTail
            (x + h) i
          -
        h3SelectedRestartVelocityRawFourierVector
            hNS ht₀ hE hTail
            x i
      )
    -
  h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
    hNS ht₀ hE hTail
    (
      h3SelectedProjectedRHSSlabRadius
        hE hQ hQR
        ⟨x, hx.1.le, hx.2.le⟩
    )
    i

/--
The raw selected slope error converges strongly to zero in Fourier `L²`.
-/
theorem tendsto_h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab_zero
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
    Tendsto
      (fun h : ℝ =>
        h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR i hx h)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (0 : H3FourierComplexL2)) := by

  have hx0 :
      0 < x := by
    have hHalf :
        0 < Q / 2 := by
      positivity
    exact
      lt_of_lt_of_le
        hHalf
        hx.1.le

  have hxQ :
      x < Q :=
    hx.2

  have hCoord :=
    h3SelectedRestartVelocityRawFourierL2_hasDerivAt_unit
      hNS ht₀ hQ hE hTail hQR.le
      ⟨hx0, hxQ⟩ i

  let xSlab :
      Set.Icc (Q / 2) Q :=
    ⟨x, hx.1.le, hx.2.le⟩

  let xRadius :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    h3PreterminalElapsedToSelectedUnitRadius
      hQR.le
      ⟨x, hx0.le, hxQ.le⟩

  have hRadius :
      xRadius
        =
      h3SelectedProjectedRHSSlabRadius
        hE hQ hQR xSlab := by
    apply Subtype.ext
    rfl

  have hSlope :=
    hCoord.tendsto_slope_zero

  have hSlope' :
      Tendsto
        (fun h : ℝ =>
          h⁻¹ •
            (
              h3SelectedRestartVelocityRawFourierVector
                  hNS ht₀ hE hTail
                  (x + h) i
                -
              h3SelectedRestartVelocityRawFourierVector
                  hNS ht₀ hE hTail
                  x i
            ))
        (𝓝[≠] (0 : ℝ))
        (
          𝓝
            (
              h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
                hNS ht₀ hE hTail
                (
                  h3SelectedProjectedRHSSlabRadius
                    hE hQ hQR xSlab
                )
                i
            )
        ) := by

    rw [← hRadius]

    simpa only [
      xRadius,
      h3SelectedRestartVelocityRawFourierVector
    ] using hSlope

  have hErr :=
    hSlope'.sub
      (
        tendsto_const_nhds :
        Tendsto
          (fun _h : ℝ =>
            h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
              hNS ht₀ hE hTail
              (
                h3SelectedProjectedRHSSlabRadius
                  hE hQ hQR xSlab
              )
              i)
          (𝓝[≠] (0 : ℝ))
          (
            𝓝
              (
                h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
                  hNS ht₀ hE hTail
                  (
                    h3SelectedProjectedRHSSlabRadius
                      hE hQ hQR xSlab
                  )
                  i
              )
          )
      )

  simpa only [
    h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab,
    xSlab,
    sub_self
  ] using hErr

/--
The raw slope-error norm also tends to zero.
-/
theorem tendsto_norm_h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab_zero
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
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR i hx h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  have hBase :=
    tendsto_h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab_zero
      hNS ht₀ hE hTail hQ hQR i hx

  have hNorm :=
    (continuous_norm.tendsto
      (0 : H3FourierComplexL2)).comp
      hBase

  change
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR i hx h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ‖(0 : H3FourierComplexL2)‖)
    at hNorm

  simpa only [norm_zero] using hNorm

/-! ## Genuine weighted spectral slope error -/

/--
Genuine weighted H³ spectral slope error of the complete selected velocity
vector.
-/
noncomputable def h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ) :
    H3SpectralFinVectorState :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
  let R : H3SpectralFinVectorState :=
    h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
      hNS ht₀ hE hTail hQ hQR
      ⟨x, hx.1.le, hx.2.le⟩
  h⁻¹ • (W (x + h) - W x) - R

/--
Coordinate application of the genuine spectral slope error.
-/
@[simp]
theorem h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply
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
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ) :
    h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
        hNS ht₀ hE hTail hQ hQR hx h i
      =
    (h⁻¹ : ℝ) •
        (
          (
            h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState
                hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              (x + h)
          ) i
            -
          (
            h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState
                hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              x
          ) i
        )
      -
    h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
      hNS ht₀ hE hTail hQ hQR
      ⟨x, hx.1.le, hx.2.le⟩ i := by
  rfl

/--
Exact coordinatewise deweighting of the genuine spectral slope error recovers
the raw Fourier slope-error package.
-/
theorem h3SpectralScalarRawFourierL2_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_eq
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
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ) :
    h3SpectralScalarRawFourierL2
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
          hNS ht₀ hE hTail hQ hQR hx h i
      )
      =
    h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR i hx h := by

  rw [
    h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply
      hNS ht₀ hE hTail hQ hQR i hx h
  ]

  simp only [
    h3SpectralScalarRawFourierL2_sub,
    h3SpectralScalarRawFourierL2_smul_real
  ]

  rw [
    h3SpectralScalarRawFourierL2_h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab_apply_eq
      hNS ht₀ hE hTail hQ hQR
      ⟨x, hx.1.le, hx.2.le⟩ i
  ]

  unfold
    h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab
    h3SelectedRestartVelocityRawFourierVector

  rfl

/--
The raw Fourier realization of every coordinate of the genuine spectral slope
error therefore converges strongly to zero.
-/
theorem tendsto_h3SpectralScalarRawFourierL2_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
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
    Tendsto
      (fun h : ℝ =>
        h3SpectralScalarRawFourierL2
          (
            h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
              hNS ht₀ hE hTail hQ hQR hx h i
          ))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (0 : H3FourierComplexL2)) := by

  have hRaw :=
    tendsto_h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab_zero
      hNS ht₀ hE hTail hQ hQR i hx

  apply hRaw.congr'

  filter_upwards with h

  exact
    (
      h3SpectralScalarRawFourierL2_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_eq
        hNS ht₀ hE hTail hQ hQR i hx h
    ).symm

end

end Euclidean
end Bridge
end PrimeTensor
