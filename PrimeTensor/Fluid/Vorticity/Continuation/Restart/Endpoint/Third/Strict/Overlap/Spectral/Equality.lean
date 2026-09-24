import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Realizable.Decoder.Injective
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Preterminal.Overlap.Witness
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Leray.Fixed

/-!
# A positive local overlap witness gives exact old/selected spectral equality

`Preterminal.Overlap.Witness` already proves that a positive local overlap
witness identifies the selected endpoint decoder with the old physical velocity.

That conclusion was originally used only at the physical level.  The
realizability and injectivity results now let us lift it all the way back to the
actual weighted H³ spectral state:

1. both the old canonical encoded state and the selected mild state are
   physically realizable;
2. the witness says the selected real decoder, transported back to `Point3`,
   equals the old velocity a.e.;
3. the canonical old decoder satisfies the same a.e. identity;
4. exact carrier round trip identifies the two real Fourier-carrier decoders;
5. injectivity of the real decoder on realizable states identifies the complete
   weighted H³ spectral states.

No endpoint continuity is used in this lifting theorem itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3StrictOverlapSpectralEquality
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3StrictOverlapSpectralEquality :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- At a positive elapsed time, a local old-solution overlap witness identifies
the exact selected weighted H³ endpoint with the canonical encoded old H³
snapshot at the same absolute time. -/
theorem h3PreterminalSpectralOverlapWitnessAt_endpoint_eq_canonicalSpectralState
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hτ : 0 < τ)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hτR : τ ≤ h3FinHeatLerayRestartRadius ν E)
    (hWitness :
      H3PreterminalSpectralOverlapWitnessAt
        ν
        E
        hν
        (h3PreterminalCanonicalAnchorSpectralState
          hNS
          ht
          (canonicalH3TailDataFrom_at_anchor ht hTail).1)
        u
        t
        τ
        hτ.le) :
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν
        (h3PreterminalCanonicalAnchorSpectralState
          hNS
          ht
          (canonicalH3TailDataFrom_at_anchor ht hTail).1)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_velocityH3SpectralStateAt_le_energyCeiling
          (velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
            hNS
            ht
            (canonicalH3TailDataFrom_at_anchor ht hTail).1)
          hE
          (canonicalH3TailDataFrom_at_anchor ht hTail).2)
        τ
      =
    h3PreterminalCanonicalSpectralStateOnElapsed
      hNS
      ht
      hEnd
      (canonicalH3TailDataFrom_integrableOnElapsed hEnd hTail)
      ⟨τ, hτ.le, le_rfl⟩ := by
  let hInt0 : VelocityH3IntegrableAt u t :=
    (canonicalH3TailDataFrom_at_anchor ht hTail).1

  let hMeas0 : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS ht

  let hFourier0 :
      VelocityH3FourierCompatibleAt
        u t hInt0 hMeas0 :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS ht hInt0

  let U₀ : H3SpectralVelocityState :=
    velocityH3SpectralStateAt
      u t hInt0 hMeas0 hFourier0

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  have hU₀ :
      ‖U₀‖ ≤ E := by
    dsimp only [U₀]
    exact
      norm_velocityH3SpectralStateAt_le_energyCeiling
        hFourier0
        hE
        (canonicalH3TailDataFrom_at_anchor ht hTail).2

  let qEnd : Set.Icc (0 : ℝ) τ :=
    ⟨τ, hτ.le, le_rfl⟩

  let qRadius :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν E) :=
    ⟨τ, hτ.le, hτR⟩

  let oldState : H3SpectralVelocityState :=
    h3PreterminalCanonicalSpectralStateOnElapsed
      hNS
      ht
      hEnd
      (canonicalH3TailDataFrom_integrableOnElapsed hEnd hTail)
      qEnd

  let selectedState : H3SpectralVelocityState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hEpos hU₀ τ

  have hWitness' :
      H3PreterminalSpectralOverlapWitnessAt
        ν E hν U₀ u t τ hτ.le := by
    simpa only [
      U₀,
      hInt0,
      hMeas0,
      hFourier0,
      h3PreterminalCanonicalAnchorSpectralState
    ] using hWitness

  rcases
    h3PreterminalSpectralOverlapWitnessAt_endpoint_eq_selected
      hν
      U₀
      hEpos
      hU₀
      u
      hτ
      hτR
      hWitness'
  with
    ⟨P, hPdecode, hEndpoint⟩

  have hSelectedEq :
      P (h3PhysicalTimeMap τ hτ.le h3UnitTimeOne)
        =
      selectedState := by
    simpa only [selectedState] using hEndpoint

  have hOldDecode :
      ∀ j : Fin 3,
        ∀ᵐ x : Point3 ∂volume,
          h3FromFourierRealL2
              (h3SpectralVelocityDecodeRealL2
                oldState
                j)
              x
            =
          (logSpaceTimeVectorField
              u
              (t + τ)
              x).component
            (h3AxisOfFin3 j) := by
    intro j

    simpa only [
      oldState,
      qEnd
    ] using
      h3PreterminalCanonicalSpectralStateOnElapsed_decode_ae
        hNS
        ht
        hEnd
        (canonicalH3TailDataFrom_integrableOnElapsed hEnd hTail)
        qEnd
        j

  have hSelectedDecode :
      ∀ j : Fin 3,
        ∀ᵐ x : Point3 ∂volume,
          h3FromFourierRealL2
              (h3SpectralVelocityDecodeRealL2
                selectedState
                j)
              x
            =
          (logSpaceTimeVectorField
              u
              (t + τ)
              x).component
            (h3AxisOfFin3 j) := by
    intro j

    have hAE := hPdecode j

    rw [hSelectedEq] at hAE

    exact hAE

  have hPhysicalDecodeEq :
      ∀ j : Fin 3,
        h3FromFourierRealL2
            (h3SpectralVelocityDecodeRealL2 selectedState j)
          =
        h3FromFourierRealL2
            (h3SpectralVelocityDecodeRealL2 oldState j) := by
    intro j

    apply MeasureTheory.Lp.ext

    filter_upwards [
      hSelectedDecode j,
      hOldDecode j
    ] with x hSel hOld

    exact hSel.trans hOld.symm

  have hDecodeEq :
      h3SpectralVelocityDecodeRealL2 selectedState
        =
      h3SpectralVelocityDecodeRealL2 oldState := by
    funext j

    have h :=
      congrArg
        h3ToFourierRealL2
        (hPhysicalDecodeEq j)

    simpa only [
      h3ToFourierRealL2_h3FromFourierRealL2
    ] using h

  have hSelectedRealizable :
      H3SpectralVelocityRealizable selectedState := by
    have hSel :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_encoded_realizable
        hν
        hFourier0
        hEpos
        hU₀
        qRadius

    simpa only [
      selectedState,
      qRadius,
      U₀
    ] using hSel

  have hOldRealizable :
      H3SpectralVelocityRealizable oldState := by
    dsimp only [oldState]

    unfold h3PreterminalCanonicalSpectralStateOnElapsed

    exact
      velocityH3SpectralStateAt_realizable
        (velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
          hNS
          (h3PreterminalElapsedTime_mem_Ioo ht hEnd qEnd)
          (canonicalH3TailDataFrom_integrableOnElapsed hEnd hTail qEnd))

  have hStateEq :
      selectedState = oldState :=
    h3SpectralVelocityDecodeRealL2_eq_imp_eq_of_realizable
      hSelectedRealizable
      hOldRealizable
      hDecodeEq

  change selectedState = oldState

  exact hStateEq

/-- Tail-canonical spelling of the same strict positive overlap equality.

This is the form consumed by the pressure-free weak/strong dense-overlap
endpoint theorem. -/
theorem h3PreterminalTailCanonicalSpectralStateOnElapsed_eq_selected_of_overlapWitness
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (hq : 0 < (q : ℝ))
    (hqR :
      (q : ℝ) ≤ h3FinHeatLerayRestartRadius ν E)
    (hWitness :
      H3PreterminalSpectralOverlapWitnessAt
        ν
        E
        hν
        (h3PreterminalCanonicalAnchorSpectralState
          hNS
          ht
          (canonicalH3TailDataFrom_at_anchor ht hTail).1)
        u
        t
        (q : ℝ)
        q.property.1) :
    h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q
      =
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν
      (h3PreterminalCanonicalAnchorSpectralState
        hNS
        ht
        (canonicalH3TailDataFrom_at_anchor ht hTail).1)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_velocityH3SpectralStateAt_le_energyCeiling
        (velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
          hNS
          ht
          (canonicalH3TailDataFrom_at_anchor ht hTail).1)
        hE
        (canonicalH3TailDataFrom_at_anchor ht hTail).2)
      (q : ℝ) := by
  have hqEnd :
      t + (q : ℝ) < T := by
    linarith [hEnd, q.property.2]

  have hLocal :=
    h3PreterminalSpectralOverlapWitnessAt_endpoint_eq_canonicalSpectralState
      hν
      hNS
      ht
      hq
      hqEnd
      hE
      hTail
      hqR
      hWitness

  symm

  simpa only [
    h3PreterminalTailCanonicalSpectralStateOnElapsed,
    h3PreterminalCanonicalSpectralStateOnElapsed
  ] using hLocal

end

end Euclidean
end Bridge
end PrimeTensor
