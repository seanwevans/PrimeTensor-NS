import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Raw.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.Derivative.Bilinear

/-!
# Selected raw-Fourier vector derivative

The remaining terminal derivative branches have been reduced to first-time
differentiability of weighted nonlinear forcing paths.

The raw selected velocity derivative theorem already proves the relevant
three-component Banach-space statement internally before projecting to one
coordinate.  The important representation distinction is:

* the selected mild path `W(t)` is a weighted H³ spectral state;
* its physical Fourier realization is the raw vector
  `i ↦ h3SpectralScalarRawFourierL2 (W(t) i)`.

The physical `L²` evolution theorem differentiates the second object, not the
weighted H³ state itself.  This file exposes exactly that vector theorem:

    d/dt [i ↦ rawFourierL2 (W(t)_i)]
      =
    selected projected Fourier RHS.

No stronger weighted-spectral differentiability statement is asserted here.
That distinction is essential before applying the nonlinear bilinear forcing
map at the next checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalSelectedRawFourierVectorDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/--
Raw Fourier realization of the complete selected finite spectral velocity path.
-/
noncomputable def h3SelectedRestartVelocityRawFourierVector
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (r : ℝ) :
    H3SpectralFinVectorState :=
  fun i : Fin 3 =>
    h3SpectralScalarRawFourierL2
      (
        (
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalSelectedDecoderAnchorState
              hNS ht₀ hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le
              hNS ht₀ hE hTail)
            r
        ) i
      )

/--
At every strict interior elapsed time, the complete raw Fourier realization of
the selected velocity has a genuine three-component `L²` derivative equal to
the exact selected projected Fourier Navier--Stokes RHS.
-/
theorem h3SelectedRestartVelocityRawFourierVector_hasDerivAt_unit
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
    HasDerivAt
      (h3SelectedRestartVelocityRawFourierVector
        hNS ht₀ hE hTail)
      (
        h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
          hNS ht₀ hE hTail
          (
            h3PreterminalElapsedToSelectedUnitRadius
              htauR
              ⟨q, hq.1.le, hq.2.le⟩
          )
      )
      q := by

  let S : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      (one_pos : (0 : ℝ) < 1)
      hNS ht₀ hE hTail

  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
      hNS ht₀ hE hTail htauR

  let P :
      H3PhysicalRealFinVectorL2Hilbert →L[ℝ]
        H3SpectralFinVectorState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap

  have hPhysical :
      HasDerivAt S (G q) q := by
    dsimp only [S, G]
    exact
      h3PreterminalSelectedVelocityPhysicalL2HilbertAt_hasDerivAt_unit
        hNS ht₀ htau hE hTail htauR hq

  have hFourierVector :
      HasDerivAt
        (fun r : ℝ => P (S r))
        (P (G q))
        q := by
    have h :=
      P.hasFDerivAt.comp_hasDerivAt
        q
        hPhysical
    simpa only [Function.comp_def] using h

  have hIccNeighborhood :
      Set.Icc (0 : ℝ) tau ∈ 𝓝 q :=
    Icc_mem_nhds hq.1 hq.2

  have hPathEventually :
      (fun r : ℝ => P (S r))
        =ᶠ[𝓝 q]
      h3SelectedRestartVelocityRawFourierVector
        hNS ht₀ hE hTail := by

    filter_upwards [hIccNeighborhood] with r hr

    let rClosed : Set.Icc (0 : ℝ) tau :=
      ⟨r, hr⟩

    let rRadius :
        Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      h3PreterminalElapsedToSelectedUnitRadius
        htauR rClosed

    have hVec :=
      h3PhysicalRealFinVectorL2HilbertRawFourier_selectedUnitVelocityOnRadius_eq
        hNS ht₀ hE hTail rRadius

    have hrRadius :
        (rRadius : ℝ) = r := by
      dsimp only [rRadius, rClosed]
      exact
        h3PreterminalElapsedToSelectedUnitRadius_coe
          htauR
          ⟨r, hr⟩

    unfold
      h3PreterminalSelectedUnitRawFourierVectorOnRadius
      h3PreterminalSelectedUnitSpectralStateOnRadius
      at hVec

    rw [hrRadius] at hVec

    dsimp only [P, S]

    rw [
      h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap_apply
    ]

    change
      h3PhysicalRealFinVectorL2HilbertRawFourier
          (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht₀ hE hTail r)
        =
      (fun i : Fin 3 =>
        h3SpectralScalarRawFourierL2
          (
            (
              h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalSelectedDecoderAnchorState
                  hNS ht₀ hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalSelectedDecoderAnchorState_le
                  hNS ht₀ hE hTail)
                r
            ) i
          ))

    simpa using hVec

  have hRawVectorDerivative :
      HasDerivAt
        (h3SelectedRestartVelocityRawFourierVector
          hNS ht₀ hE hTail)
        (P (G q))
        q :=
    hFourierVector.congr_of_eventuallyEq
      hPathEventually.symm

  have hqClosed :
      q ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hq.1.le, hq.2.le⟩

  let qClosed : Set.Icc (0 : ℝ) tau :=
    ⟨q, hqClosed⟩

  let qRadius :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    h3PreterminalElapsedToSelectedUnitRadius
      htauR qClosed

  have hRHSPhysical :
      G q
        =
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht₀ hE hTail qRadius := by
    dsimp only [G, qRadius, qClosed]
    exact
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed_apply_of_mem
        hNS ht₀ hE hTail htauR hqClosed

  have hRHSFourier :
      P
          (
            h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
              hNS ht₀ hE hTail qRadius
          )
        =
      h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
        hNS ht₀ hE hTail qRadius := by
    dsimp only [P]
    rw [
      h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap_apply
    ]
    exact
      h3PhysicalRealFinVectorL2HilbertRawFourier_selectedUnitProjectedRHSPhysicalL2HilbertOnRadius_eq
        hNS ht₀ hE hTail qRadius

  have hDerivativeValue :
      P (G q)
        =
      h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
        hNS ht₀ hE hTail qRadius := by
    rw [hRHSPhysical, hRHSFourier]

  rw [hDerivativeValue] at hRawVectorDerivative

  simpa only [
    qRadius,
    qClosed
  ] using hRawVectorDerivative

/--
The selected raw Fourier vector path is therefore differentiable at every
strict interior restart time.
-/
theorem h3SelectedRestartVelocityRawFourierVector_differentiableAt_unit
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
    DifferentiableAt ℝ
      (h3SelectedRestartVelocityRawFourierVector
        hNS ht₀ hE hTail)
      q :=
  (
    h3SelectedRestartVelocityRawFourierVector_hasDerivAt_unit
      hNS ht₀ htau hE hTail htauR hq
  ).differentiableAt

/-!
The exact diagonal forcing subtraction identity needed by the next quotient
argument is already available upstream as

`h3RawFinLerayOuterProductDivergence_diagonal_sub`.

We intentionally do not redeclare it here.
-/

end

end Euclidean
end Bridge
end PrimeTensor
