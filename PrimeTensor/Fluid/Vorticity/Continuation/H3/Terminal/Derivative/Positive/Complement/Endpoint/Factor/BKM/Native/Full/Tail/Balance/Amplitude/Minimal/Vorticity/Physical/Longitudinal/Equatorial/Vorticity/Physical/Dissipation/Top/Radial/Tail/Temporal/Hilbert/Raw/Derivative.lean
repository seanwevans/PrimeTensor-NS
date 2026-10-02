import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.State
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Physical.L2.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.RHS.Leray.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Reduction

/-!
# Strong raw-Fourier derivative of the selected restart

Before applying the unbounded top-tail multiplier `q(ξ)^2`, isolate the
unweighted temporal theorem in the exact Fourier Hilbert space used by the
rest of the sharp-tail argument.

The selected branch already has the genuine physical Hilbert derivative

    d/dt U_phys(t) = RHS_phys(t)

at every strict elapsed interior point.

Two bounded linear maps transport that derivative without any new analysis:

1. the already-defined contractive real Plancherel map from the physical
   three-component Hilbert space to the finite raw-Fourier vector;
2. coordinate projection onto one `Fin 3` Fourier component.

On the closed selected restart radius the Plancherel image of the physical
velocity is exactly the deweighted selected spectral state, and the Plancherel
image of the physical projected RHS is exactly the quotient-safe spectral
projected RHS.

Thus every selected raw Fourier velocity coordinate has a genuine strong
`L²` derivative equal to the exact unweighted spectral PDE RHS.

This checkpoint is intentionally prior to the `q²` multiplier.  The next step
can truncate that multiplier, transport this derivative through each bounded
truncation, and then remove the truncation using the already-closed weighted
state and weighted-RHS `L²` control.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailRawDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Bounded coordinate projection over the real scalar field -/

/--
Coordinate projection from the finite Fourier vector, viewed as a real
continuous-linear map so it composes directly with real-time derivatives.
-/
noncomputable def h3TopTailSpectralFinCoordinateRealCLM
    (i : Fin 3) :
    H3SpectralFinVectorState →L[ℝ] H3FourierComplexL2 :=
  (
    (h3EndpointSpectralFinCoordinateCLM i).restrictScalars ℝ
  )

@[simp]
theorem h3TopTailSpectralFinCoordinateRealCLM_apply
    (i : Fin 3)
    (U : H3SpectralFinVectorState) :
    h3TopTailSpectralFinCoordinateRealCLM i U = U i := by
  rfl

/-! ## Strong selected raw-Fourier derivative -/

/--
At every strict interior elapsed time, one selected raw Fourier velocity
coordinate has the genuine strong `L²` derivative given by the exact selected
unit-viscosity spectral projected RHS.
-/
theorem h3SelectedRestartVelocityRawFourierL2_hasDerivAt_unit
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
    (hq : q ∈ Set.Ioo (0 : ℝ) tau)
    (i : Fin 3) :
    HasDerivAt
      (fun r : ℝ =>
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
      (
        h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
          hNS ht₀ hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius
            htauR
            ⟨q, hq.1.le, hq.2.le⟩)
          i
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

  let C :
      H3SpectralFinVectorState →L[ℝ]
        H3FourierComplexL2 :=
    h3TopTailSpectralFinCoordinateRealCLM i

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

  have hCoordinate :
      HasDerivAt
        (fun r : ℝ => C (P (S r)))
        (C (P (G q)))
        q := by
    have h :=
      C.hasFDerivAt.comp_hasDerivAt
        q
        hFourierVector
    simpa only [Function.comp_def] using h

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)

  let rawPath : ℝ → H3FourierComplexL2 :=
    fun r =>
      h3SpectralScalarRawFourierL2
        (W r i)

  have hIccNeighborhood :
      Set.Icc (0 : ℝ) tau ∈ 𝓝 q :=
    Icc_mem_nhds hq.1 hq.2

  have hPathEventually :
      (fun r : ℝ => C (P (S r)))
        =ᶠ[𝓝 q]
      rawPath := by

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

    have hCoord :=
      congrFun hVec i

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
      at hCoord

    rw [hrRadius] at hCoord

    dsimp only [C, P, S, rawPath, W]

    rw [
      h3TopTailSpectralFinCoordinateRealCLM_apply,
      h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap_apply
    ]

    simpa using hCoord

  have hRawDerivative :
      HasDerivAt
        rawPath
        (C (P (G q)))
        q :=
    hCoordinate.congr_of_eventuallyEq
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
      C (P (G q))
        =
      h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
          hNS ht₀ hE hTail qRadius i := by

    rw [hRHSPhysical, hRHSFourier]

    dsimp only [C]

    exact
      h3TopTailSpectralFinCoordinateRealCLM_apply
        i
        (
          h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
            hNS ht₀ hE hTail qRadius
        )

  dsimp only [rawPath, W] at hRawDerivative ⊢

  rw [hDerivativeValue] at hRawDerivative

  simpa only [
    qRadius,
    qClosed
  ] using hRawDerivative

end

end Euclidean
end Bridge
end PrimeTensor
