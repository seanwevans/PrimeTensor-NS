import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Pointwise.FTC
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Advection.Representatives

/-!
# Weak-pairing bridges for the canonical selected restart

The strict-positive selected pointwise FTC is now available.  Before integrating
that identity against compact divergence-free tests, two quotient seams must be
made explicit in the native physical `L²` Hilbert language.

First, the selected physical decoder used by the weak--strong comparison has
the selected classical restart velocity as its almost-everywhere
representative.  Consequently

    ⟪Φ, S(q)⟫
      =
    Σᵢ ∫ φᵢ(x) Sᵢ(q,x) dx.

Second, the generic pressure-free Leray/advection theorem already proves that
a divergence-free compact test cannot distinguish the Leray-projected
nonlinearity from ordinary physical advection.  Specializing that theorem to
the canonical selected slice gives

    ⟪Φ, N_sel(q)⟫
      =
    Σᵢ ∫ φᵢ(x) (S·∇S)ᵢ(q,x) dx.

These are exactly the velocity and nonlinear representation bridges needed by
the selected weak FTC.  No old-path temporal regularity, endpoint continuity,
or selected--old agreement is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongGenericWeakForcingAdvection

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakPairingBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One selected physical `L²` velocity coordinate has the actual selected
classical restart component as an almost-everywhere representative. -/
theorem h3PreterminalSelectedVelocityPhysicalL2HilbertAt_coordinate_ae_selectedWeakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (i : Fin 3) :
    (fun x : Point3 =>
      ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail q) i : H3ScalarL2) x)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht hE hTail)
        q x).component
          (h3AxisOfFin3 i)) := by
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht hE hTail

  have hRep :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_ae_eq_decodeRealL2
      (s := q)
      (one_pos : (0 : ℝ) < 1)
      U₀ hEpos hU₀ i

  have hRep' :
      (fun x : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          U₀ hEpos hU₀ q x).component
            (h3AxisOfFin3 i))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail q) i : H3ScalarL2) x) := by
    simpa only [
      h3PreterminalSelectedVelocityPhysicalL2HilbertAt,
      PiLp.toLp_apply,
      U₀,
      hEpos,
      hU₀,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
    ] using hRep

  simpa only [
    U₀,
    hEpos,
    hU₀
  ] using hRep'.symm

/-- Weak Hilbert pairing with the selected physical velocity is exactly the
literal compact-test pairing with the selected classical restart velocity. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedVelocity_eq_classical
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail q)
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalSelectedDecoderAnchorState hNS ht hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le
              hNS ht hE hTail)
            q x).component
              (h3AxisOfFin3 i))
        ∂volume := by
  unfold h3WeakTestVectorPhysicalL2Hilbert

  rw [PiLp.inner_apply]

  apply Finset.sum_congr rfl
  intro i hi

  rw [h3WeakTestFunctionPhysicalL2_inner_eq_integral]

  apply integral_congr_ae

  filter_upwards [
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt_coordinate_ae_selectedWeakStrong
      (q := q)
      hNS ht hE hTail i
  ] with x hx

  rw [hx]

/-- Against a divergence-free compact weak test, the canonical selected
Leray-forcing Hilbert vector is exactly ordinary selected physical advection. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitLerayForcing_eq_classicalAdvection
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
          hNS ht hE hTail q)
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (realAdvectionComponent
            (h3PreterminalSelectedWeakStrongVelocity
              (one_pos : (0 : ℝ) < 1)
              hNS ht hE hTail)
            (q : ℝ) x
            (h3AxisOfFin3 i))
        ∂volume := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail q

  have hReal :
      H3SpectralVelocityRealizable U := by
    dsimp only [U]
    exact
      h3PreterminalSelectedUnitSpectralStateOnRadius_realizable
        hNS ht hE hTail q

  have hDiv :
      H3SpectralFinRawDivergenceFree U := by
    dsimp only [U]
    exact
      h3PreterminalSelectedUnitSpectralStateOnRadius_rawDivergenceFree
        hNS ht hE hTail q

  calc
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
          hNS ht hE hTail q)
        =
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3WeakStrongLerayForcingPhysicalL2Hilbert U) := by
          rw [
            h3WeakStrongLerayForcingPhysicalL2Hilbert_selectedUnit_eq
              hNS ht hE hTail q
          ]
    _ =
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3WeakStrongAdvectionPhysicalL2Hilbert U) := by
          exact
            inner_h3WeakTestVectorPhysicalL2Hilbert_weakStrongLerayForcing_eq_advection
              U hReal hDiv φ hφ
    _ =
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (realAdvectionComponent
              (h3PreterminalSelectedWeakStrongVelocity
                (one_pos : (0 : ℝ) < 1)
                hNS ht hE hTail)
              (q : ℝ) x
              (h3AxisOfFin3 i))
          ∂volume := by
            unfold
              h3WeakTestVectorPhysicalL2Hilbert
              h3WeakStrongAdvectionPhysicalL2Hilbert

            rw [PiLp.inner_apply]

            apply Finset.sum_congr rfl
            intro i hi

            rw [h3WeakTestFunctionPhysicalL2_inner_eq_integral]

            apply integral_congr_ae

            have hAE :=
              h3WeakStrongAdvectionPhysicalL2_selectedUnit_ae
                hNS ht hE hTail q i

            dsimp only [U]

            filter_upwards [hAE] with x hx

            rw [hx]

end

end Euclidean
end Bridge
end PrimeTensor
