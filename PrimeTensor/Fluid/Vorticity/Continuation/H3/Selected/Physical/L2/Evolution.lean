import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Velocity.Lipschitz
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Leray.Weak.Determining
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.RHS.Leray.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Fourier.L2.Diffusion.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Fourier.L2.Forcing.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Reduction

/-!
# Selected restart: strong physical L² evolution

The selected branch already has an exact weak FTC against every compact smooth
solenoidal test.  This file upgrades that identity to a genuine Hilbert-valued
Bochner evolution.

The missing functional-analytic ingredients are all already present in the
repository:

* the selected weighted H³ path is strongly continuous;
* the raw Fourier Laplacian and Leray forcing are strongly continuous in their
  weighted H³ inputs;
* inverse Fourier transport, real projection, and the finite `PiLp 2` wrapper
  are continuous;
* every selected projected RHS state is Leray-fixed;
* divergence-free weak tests determine all Leray-fixed physical L² states.

Consequently the selected projected RHS is a strongly continuous physical
Hilbert path, hence Bochner interval-integrable.  The weak FTC pairings commute
with that Bochner integral, and Leray-fixed density upgrades equality of all
weak pairings to equality of the actual Hilbert vectors.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedPhysicalL2Evolution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected unit-viscosity projected physical RHS is strongly continuous
on the complete closed restart radius in the native three-component Hilbert
space. -/
theorem continuous_h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    Continuous
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail) := by
  let W :
      Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail

  have hW : Continuous W := by
    dsimp only [W]
    unfold h3PreterminalSelectedUnitSpectralStateOnRadius
    exact
      (continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht hE hTail)).comp
        continuous_subtype_val

  have hLap
      (i : Fin 3) :
      Continuous
        (fun q :
            Set.Icc
              (0 : ℝ)
              (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
            hNS ht hE hTail q i) := by
    have hCoord :
        Continuous
          (fun q :
              Set.Icc
                (0 : ℝ)
                (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
            W q i) :=
      (continuous_apply i).comp hW

    have hFourier :
        Continuous
          (fun q :
              Set.Icc
                (0 : ℝ)
                (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
            h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
              hNS ht hE hTail q i) := by
      unfold h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
      exact
        continuous_h3SpectralScalarLaplacianRawFourierL2.comp
          hCoord

    unfold h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius

    exact
      continuous_h3FromFourierRealL2.comp
        (continuous_h3RealPartFourierL2.comp
          ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ).symm.continuous.comp
              hFourier))

  have hForce
      (i : Fin 3) :
      Continuous
        (fun q :
            Set.Icc
              (0 : ℝ)
              (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius
            hNS ht hE hTail q i) := by
    let D :
        Set.Icc
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
          H3SpectralFinVectorState × H3SpectralFinVectorState :=
      fun q => (W q, W q)

    have hD : Continuous D := by
      dsimp only [D]
      exact Continuous.prodMk hW hW

    have hFourier :
        Continuous
          (fun q :
              Set.Icc
                (0 : ℝ)
                (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
            h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
              hNS ht hE hTail q i) := by
      have hComp :=
        (continuous_h3RawFinLerayOuterProductDivergenceFourierL2 i).comp hD

      have hEq :
          (fun q :
              Set.Icc
                (0 : ℝ)
                (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
            h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
              hNS ht hE hTail q i)
            =
          (fun q =>
            h3RawFinLerayOuterProductDivergenceFourierL2
              (W q) (W q) i) := by
        funext q
        rfl

      rw [hEq]
      change
        Continuous
          (fun q =>
            h3RawFinLerayOuterProductDivergenceFourierL2
              (W q) (W q) i) at hComp
      exact hComp

    unfold h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius

    exact
      continuous_h3FromFourierRealL2.comp
        (continuous_h3RealPartFourierL2.comp
          ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ).symm.continuous.comp
              hFourier))

  have hPi :
      Continuous
        (fun q :
            Set.Icc
              (0 : ℝ)
              (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          fun i : Fin 3 =>
            h3PreterminalSelectedUnitProjectedRHSPhysicalL2OnRadius
              hNS ht hE hTail q i) := by
    apply continuous_pi
    intro i
    unfold h3PreterminalSelectedUnitProjectedRHSPhysicalL2OnRadius
    exact (hLap i).sub (hForce i)

  have hToHilbert :
      Continuous
        (WithLp.toLp (2 : ℝ≥0∞) :
          (Fin 3 → H3ScalarL2) →
            H3PhysicalRealFinVectorL2Hilbert) := by
    exact
      PiLp.continuous_toLp
        (2 : ℝ≥0∞)
        (fun _ : Fin 3 => H3ScalarL2)

  change
    Continuous
      (fun q :
          Set.Icc
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        (WithLp.toLp
          (2 : ℝ≥0∞)
          (fun i : Fin 3 =>
            h3PreterminalSelectedUnitProjectedRHSPhysicalL2OnRadius
              hNS ht hE hTail q i) :
          H3PhysicalRealFinVectorL2Hilbert))

  exact hToHilbert.comp hPi

/-- The zero-extended selected projected RHS is strongly continuous on the
closed elapsed interval on which it is used. -/
theorem continuousOn_h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E) :
    ContinuousOn
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
        hNS ht hE hTail htauR)
      (Set.Icc (0 : ℝ) tau) := by
  rw [continuousOn_iff_continuous_domRestrict]

  let f :
      Set.Icc (0 : ℝ) tau →
        H3PhysicalRealFinVectorL2Hilbert :=
    fun q =>
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)

  have hClosed : Continuous f := by
    let R : ℝ :=
      h3FinHeatLerayRestartRadius (1 : ℝ) E

    have hBase :=
      continuous_h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail

    have hEmbed :
        Continuous
          (fun q : Set.Icc (0 : ℝ) tau =>
            (⟨(q : ℝ),
              ⟨q.property.1, q.property.2.trans htauR⟩⟩ :
              Set.Icc (0 : ℝ) R)) := by
      exact continuous_subtype_val.subtype_mk _

    dsimp only [f, R]
    exact hBase.comp hEmbed

  have hEq :
      (Set.Icc (0 : ℝ) tau).domRestrict
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR)
        =
      f := by
    funext q
    dsimp only [f]
    exact
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed_apply_of_mem
        hNS ht hE hTail htauR q.property

  rw [hEq]
  exact hClosed

/-- The selected projected RHS is genuinely Bochner interval-integrable to any
closed elapsed target. -/
theorem intervalIntegrable_h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    IntervalIntegrable
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
        hNS ht hE hTail htauR)
      volume
      (0 : ℝ)
      (q : ℝ) := by
  have hCont :=
    continuousOn_h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
      hNS ht htau hE hTail htauR

  have hSub :
      Set.Icc (0 : ℝ) (q : ℝ) ⊆ Set.Icc (0 : ℝ) tau := by
    intro s hs
    exact ⟨hs.1, hs.2.trans q.property.2⟩

  exact
    (hCont.mono hSub).intervalIntegrable_of_Icc
      q.property.1

/-- Genuine physical Hilbert Bochner integral of the selected projected RHS to
one elapsed target. -/
noncomputable def h3PreterminalSelectedUnitProjectedRHSPhysicalL2BochnerIntegralTo
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2Hilbert :=
  ∫ s in (0 : ℝ)..(q : ℝ),
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
      hNS ht hE hTail htauR s

/-- Every ambient elapsed selected projected RHS state is Leray-fixed. -/
theorem h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
        hNS ht hE hTail htauR s) := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) tau

  · rw [
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed_apply_of_mem
        hNS ht hE hTail htauR hs
    ]

    exact
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius_lerayFixed
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR ⟨s, hs⟩)

  · rw [← mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff]
    unfold
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
    rw [dif_neg hs]
    exact Submodule.zero_mem _

/-- The physical Hilbert Bochner integral of the selected projected RHS remains
Leray-fixed. -/
theorem h3PreterminalSelectedUnitProjectedRHSPhysicalL2BochnerIntegralTo_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2BochnerIntegralTo
        hNS ht hE hTail htauR q) := by
  rw [← mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff]

  unfold h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule
  change
    h3PhysicalRealFinVectorL2HilbertLerayDefectContinuousLinearMap
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2BochnerIntegralTo
          hNS ht hE hTail htauR q)
      =
    0

  have hInt :=
    intervalIntegrable_h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
      hNS ht htau hE hTail htauR q

  have hComm :
      h3PhysicalRealFinVectorL2HilbertLerayDefectContinuousLinearMap
          (∫ s in (0 : ℝ)..(q : ℝ),
            h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
              hNS ht hE hTail htauR s)
        =
      ∫ s in (0 : ℝ)..(q : ℝ),
        h3PhysicalRealFinVectorL2HilbertLerayDefectContinuousLinearMap
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR s) := by
    symm
    exact
      h3PhysicalRealFinVectorL2HilbertLerayDefectContinuousLinearMap.intervalIntegral_comp_comm
        hInt

  rw [h3PreterminalSelectedUnitProjectedRHSPhysicalL2BochnerIntegralTo]
  rw [hComm]

  have hPointwise :
      (fun s : ℝ =>
        h3PhysicalRealFinVectorL2HilbertLerayDefectContinuousLinearMap
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR s))
        =
      (fun _s : ℝ => (0 : H3SpectralFinVectorState)) := by
    funext s
    have hFixed :
        H3PhysicalRealFinVectorL2HilbertLerayFixed
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR s) :=
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed_lerayFixed
        (s := s) hNS ht hE hTail htauR

    have hMem :=
      (mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
          hNS ht hE hTail htauR s)).2 hFixed

    change
      h3PhysicalRealFinVectorL2HilbertLerayDefectContinuousLinearMap
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR s)
        =
      0
      at hMem

    exact hMem

  rw [hPointwise]
  simp

/-- Pairing a fixed physical Hilbert state commutes with the selected projected
RHS Bochner integral. -/
theorem inner_h3PreterminalSelectedUnitProjectedRHSPhysicalL2BochnerIntegralTo_eq_intervalIntegral
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau)
    (Phi : H3PhysicalRealFinVectorL2Hilbert) :
    inner ℝ
        Phi
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2BochnerIntegralTo
          hNS ht hE hTail htauR q)
      =
    ∫ s in (0 : ℝ)..(q : ℝ),
      inner ℝ
        Phi
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
          hNS ht hE hTail htauR s) := by
  have hInt :=
    intervalIntegrable_h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
      hNS ht htau hE hTail htauR q

  let L : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] ℝ :=
    innerSL ℝ Phi

  have hComm :
      (∫ s in (0 : ℝ)..(q : ℝ),
        L
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR s))
        =
      L
        (∫ s in (0 : ℝ)..(q : ℝ),
          h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR s) :=
    L.intervalIntegral_comp_comm hInt

  simpa only [
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2BochnerIntegralTo,
    L,
    innerSL_apply_apply
  ] using hComm.symm

/-- The selected weak FTC upgrades to a genuine physical Hilbert-valued
Bochner evolution identity. -/
theorem h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed_eq_BochnerProjectedRHSTo
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed
        hNS ht htau hE hTail q
      =
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2BochnerIntegralTo
      hNS ht hE hTail htauR q := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed
      hNS ht htau hE hTail q

  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2BochnerIntegralTo
      hNS ht hE hTail htauR q

  have hVFixed :
      H3PhysicalRealFinVectorL2HilbertLerayFixed V := by
    let q0 : Set.Icc (0 : ℝ) tau :=
      ⟨0, le_rfl, htau.le⟩

    have hQ :=
      h3PreterminalSelectedUnitVelocityPhysicalL2HilbertOnRadius_lerayFixed
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)

    have h0 :=
      h3PreterminalSelectedUnitVelocityPhysicalL2HilbertOnRadius_lerayFixed
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q0)

    dsimp only [V]
    unfold h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed

    apply H3PhysicalRealFinVectorL2HilbertLerayFixed.sub

    · simpa only [h3PreterminalElapsedToSelectedUnitRadius_coe] using hQ

    · simpa only [
        h3PreterminalElapsedToSelectedUnitRadius_coe,
        q0
      ] using h0

  have hRFixed :
      H3PhysicalRealFinVectorL2HilbertLerayFixed R := by
    dsimp only [R]
    exact
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2BochnerIntegralTo_lerayFixed
        hNS ht htau hE hTail htauR q

  apply
    h3PhysicalRealFinVectorL2Hilbert_eq_of_lerayFixed_of_divergenceFreeWeakTest_pairings_eq
      V R hVFixed hRFixed

  intro phi hphi

  have hWeak :=
    h3PreterminalSelectedUnitWeakProjectedRHSFTCOnElapsed
      hNS ht htau hE hTail htauR phi hphi q

  have hBochner :=
    inner_h3PreterminalSelectedUnitProjectedRHSPhysicalL2BochnerIntegralTo_eq_intervalIntegral
      hNS ht htau hE hTail htauR q
      (h3WeakTestVectorPhysicalL2Hilbert phi)

  dsimp only [V, R]
  exact hWeak.trans hBochner.symm

end

end Euclidean
end Bridge
end PrimeTensor
