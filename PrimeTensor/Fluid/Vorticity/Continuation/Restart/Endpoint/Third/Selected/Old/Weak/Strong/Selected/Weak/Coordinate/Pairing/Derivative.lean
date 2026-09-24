import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Weak.Temporal.Local.Domination
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Pointwise.FTC
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiate one selected weak velocity coordinate pairing

Joint spacetime continuity has already closed the selected local-domination
frontier.  This file performs the corresponding parametric-integral step.

For one compact test coordinate `φ` and one velocity coordinate `i`, define

    P_i(r) = ∫ φ(x) S_i(r,x) dx.

At every strict elapsed time `s ∈ (0,tau)` we prove

    P_i'(s)
      =
    ∫ φ(x) ∂ₜS_i(s,x) dx.

The proof follows Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` interface exactly:

* the selected local-domination theorem supplies the integrable majorant;
* each spatial velocity slice is continuous, hence measurable and locally
  integrable;
* the temporal-derivative slice is continuous by the joint-continuity theorem;
* pointwise `HasDerivAt` is extracted from the already-proved strict-positive
  selected temporal regularity.

No old-path temporal input and no Banach-valued velocity derivative is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongGenericWeakForcingAdvection

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakCoordinatePairingDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Match the norm topology used by `H3WeakTestFunction`. -/
local instance point3NormTopologicalSpaceH3SelectedOldWeakStrongSelectedWeakCoordinatePairingDerivative :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- One ambient-real selected weak velocity coordinate pairing. -/
noncomputable def h3PreterminalSelectedUnitWeakVelocityCoordinatePairingReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestFunction)
    (i : Fin 3)
    (r : ℝ) :
    ℝ :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
  ∫ x : Point3,
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ x)
      (h3SpectralScalarRealC1RepresentativeOnPoint3
        (W r i) x)
    ∂volume

/-- The matching selected temporal-derivative coordinate pairing. -/
noncomputable def h3PreterminalSelectedUnitWeakTemporalCoordinatePairingReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestFunction)
    (i : Fin 3)
    (r : ℝ) :
    ℝ :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
  ∫ x : Point3,
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ x)
      (temporal.d
        (fun q : ℝ =>
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (W q i) x)
        r)
    ∂volume

/-- At every strict elapsed time, one selected weak velocity coordinate pairing
has derivative equal to the compact-test pairing with the actual selected
pointwise temporal derivative. -/
theorem h3PreterminalSelectedUnitWeakVelocityCoordinatePairingReal_hasDerivAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestVector)
    (i : Fin 3) :
    HasDerivAt
      (h3PreterminalSelectedUnitWeakVelocityCoordinatePairingReal
        hNS ht hE hTail (φ i) i)
      (h3PreterminalSelectedUnitWeakTemporalCoordinatePairingReal
        hNS ht hE hTail (φ i) i s)
      s := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let F : ℝ → Point3 → ℝ :=
    fun r x =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W r i) x)

  let F' : ℝ → Point3 → ℝ :=
    fun r x =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (temporal.d
          (fun q : ℝ =>
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (W q i) x)
          r)

  have hDom :=
    H3PreterminalSelectedUnitWeakTemporalLocalDominationAt_of_jointContinuity
      hNS ht htau hE hTail htauR hs φ

  dsimp only [H3PreterminalSelectedUnitWeakTemporalLocalDominationAt] at hDom

  rcases hDom i with
    ⟨S, hS, hSsub, bound, hBoundInt, hBound⟩

  have hF_meas :
      ∀ᶠ r : ℝ in 𝓝 s,
        AEStronglyMeasurable
          (F r)
          (volume : Measure Point3) := by
    filter_upwards with r

    have hRep :
        Continuous
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W r i)) :=
      (h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
        (W r i)).continuous

    have hCont :
        Continuous (F r) := by
      dsimp only [F]
      change
        Continuous
          (fun x : Point3 =>
            (φ i x) *
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W r i) x)
      exact
        (φ i).continuous.mul hRep

    exact hCont.aestronglyMeasurable

  have hF_int :
      Integrable
        (F s)
        (volume : Measure Point3) := by
    have hRep :
        Continuous
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s i)) :=
      (h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
        (W s i)).continuous

    have hRepLocal :
        LocallyIntegrable
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s i))
          (volume : Measure Point3) :=
      hRep.locallyIntegrable

    dsimp only [F]

    exact
      (φ i).integrable_bilin
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (hRepLocal.locallyIntegrableOn Set.univ)

  have hJoint :=
    h3PreterminalSelectedUnitRealVelocity_temporalDerivative_jointContinuousOnElapsed
      hNS ht hE hTail htauR i

  dsimp only at hJoint

  have hTemporalSlice :
      Continuous
        (fun x : Point3 =>
          temporal.d
            (fun q : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W q i) x)
            s) := by
    rw [← continuousOn_univ]

    have hEmbed :
        Continuous
          (fun x : Point3 => (s, x)) :=
      continuous_const.prodMk continuous_id

    have hMaps :
        MapsTo
          (fun x : Point3 => (s, x))
          Set.univ
          (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
      intro x hx
      exact ⟨hs, Set.mem_univ x⟩

    have hComp :=
      hJoint.comp
        hEmbed.continuousOn
        hMaps

    apply hComp.congr
    intro x hx
    rfl

  have hF'_meas :
      AEStronglyMeasurable
        (F' s)
        (volume : Measure Point3) := by
    have hCont :
        Continuous (F' s) := by
      dsimp only [F']
      change
        Continuous
          (fun x : Point3 =>
            (φ i x) *
              temporal.d
                (fun q : ℝ =>
                  h3SpectralScalarRealC1RepresentativeOnPoint3
                    (W q i) x)
                s)
      exact
        (φ i).continuous.mul hTemporalSlice

    exact hCont.aestronglyMeasurable

  have hBound' :
      ∀ᵐ x : Point3 ∂volume,
        ∀ r : ℝ,
          r ∈ S →
          ‖F' r x‖ ≤ bound x := by
    simpa only [F', W] using hBound

  have hDiff :
      ∀ᵐ x : Point3 ∂volume,
        ∀ r : ℝ,
          r ∈ S →
          HasDerivAt
            (fun q : ℝ => F q x)
            (F' r x)
            r := by
    filter_upwards with x

    intro r hr

    have hrIoo :
        r ∈ Set.Ioo (0 : ℝ) tau :=
      hSsub hr

    have hrR :
        r <
          h3FinHeatLerayRestartRadius (1 : ℝ) E :=
      lt_of_lt_of_le hrIoo.2 htauR

    let f : ℝ → ℝ :=
      fun q : ℝ =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (W q i) x

    have hRegularity0 :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_temporalDerivativeRegularity
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        x
        (h3AxisOfFin3 i)

    have hRegularity :
        DifferentiableOn ℝ f
          (Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E)) := by
      have hAll :
          DifferentiableOn ℝ f
              (Set.Ioo
                (0 : ℝ)
                (h3FinHeatLerayRestartRadius (1 : ℝ) E))
            ∧
          ContinuousOn
            (deriv f)
            (Set.Ioo
              (0 : ℝ)
              (h3FinHeatLerayRestartRadius (1 : ℝ) E)) := by
        simpa only [
          f,
          W,
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
          h3PreterminalTailCanonicalSelectedRestart,
          h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
          h3SpectralVelocityRealC1RepresentativeOnPoint3
        ] using hRegularity0

      exact hAll.1

    have hrOpen :
        r ∈
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨hrIoo.1, hrR⟩

    have hDiffWithin :
        DifferentiableWithinAt
          ℝ f
          (Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E))
          r :=
      hRegularity r hrOpen

    have hDiffAt :
        DifferentiableAt ℝ f r :=
      hDiffWithin.differentiableAt
        (isOpen_Ioo.mem_nhds hrOpen)

    have hBase :
        HasDerivAt
          f
          (temporal.d f r)
          r := by
      change HasDerivAt f (deriv f r) r
      exact hDiffAt.hasDerivAt

    have hMul :=
      hBase.const_mul (φ i x)

    dsimp only [F, F', f]

    exact hMul

  have hParam :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F)
      (x₀ := s)
      (s := S)
      (bound := bound)
      hS
      hF_meas
      hF_int
      (F' := F')
      hF'_meas
      hBound'
      hBoundInt
      hDiff

  dsimp only [
    h3PreterminalSelectedUnitWeakVelocityCoordinatePairingReal,
    h3PreterminalSelectedUnitWeakTemporalCoordinatePairingReal,
    W
  ]

  exact hParam.2

end

end Euclidean
end Bridge
end PrimeTensor
