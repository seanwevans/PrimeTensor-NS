import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyIntegrand
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalVelocityLipschitz
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path

/-!
# Strong continuity of the selected--old weak energy path

The endpoint-independent weak evolution and the ambient quadratic integrand are
already closed.  A partition-based weak energy argument additionally needs the
actual Hilbert path

    D(r) = U_selected(r) - U_old(r)

to be strongly continuous.

This file closes that topology noncircularly.

* The selected restart is globally continuous in weighted spectral `H³`.
  Its canonical real decoder is contractive on differences, inverse Fourier
  transport is continuous, and the finite `PiLp 2` wrapper is continuous.
  Hence the selected physical Hilbert velocity path is strongly continuous.

* The old branch already satisfies an endpoint-independent `L²` Lipschitz
  estimate under the family-level pressure-defect frontier.  Coordinatewise
  Lipschitz continuity therefore gives strong continuity of the bundled
  physical Hilbert velocity path.

Subtracting the two gives strong continuity of the concrete selected--old
difference on `[0,tau]`, hence `ContinuousOn` continuity of the ambient-real
zero extension on that closed interval.  Consequently its squared Hilbert norm
is continuous there.

No old strong time derivative and no old endpoint-continuity hypothesis is
used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyPathContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical real spectral decoder is nonexpansive in the weighted H³
spectral norm. -/
theorem dist_h3SpectralScalarDecodeRealL2_le
    (F G : H3SpectralScalarState) :
    dist
        (h3SpectralScalarDecodeRealL2 F)
        (h3SpectralScalarDecodeRealL2 G)
      ≤
    dist F G := by
  simp only [dist_eq_norm]
  rw [← h3SpectralScalarDecodeRealL2_sub]
  exact norm_h3SpectralScalarDecodeRealL2_le (F - G)

/-- Hence the real spectral decoder is continuous. -/
theorem continuous_h3SpectralScalarDecodeRealL2 :
    Continuous
      (h3SpectralScalarDecodeRealL2 :
        H3SpectralScalarState → H3FourierRealL2) := by
  have hLip :
      LipschitzWith 1
        (h3SpectralScalarDecodeRealL2 :
          H3SpectralScalarState → H3FourierRealL2) := by
    apply LipschitzWith.of_dist_le_mul
    intro F G
    simpa only [NNReal.coe_one, one_mul] using
      dist_h3SpectralScalarDecodeRealL2_le F G

  exact hLip.continuous

/-- Decoding one coordinate of a finite spectral velocity state into the
project physical scalar `L²` carrier is continuous. -/
theorem continuous_h3SelectedPhysicalL2CoordinateDecode
    (j : Fin 3) :
    Continuous
      (fun U : H3SpectralFinVectorState =>
        h3FromFourierRealL2
          (h3SpectralVelocityDecodeRealL2 U j)) := by
  have hCoord :
      Continuous
        (fun U : H3SpectralFinVectorState =>
          h3SpectralScalarDecodeRealL2 (U j)) :=
    continuous_h3SpectralScalarDecodeRealL2.comp
      (continuous_apply j)

  exact
    continuous_h3FromFourierRealL2.comp hCoord

/-- The complete selected physical `PiLp 2` decoder is continuous as a map of
the weighted spectral velocity state. -/
theorem continuous_h3SelectedPhysicalL2HilbertDecode :
    Continuous
      (fun U : H3SpectralFinVectorState =>
        (WithLp.toLp
          (2 : ℝ≥0∞)
          (fun j : Fin 3 =>
            h3FromFourierRealL2
              (h3SpectralVelocityDecodeRealL2 U j)) :
          H3PhysicalRealFinVectorL2Hilbert)) := by
  have hPi :
      Continuous
        (fun U : H3SpectralFinVectorState =>
          fun j : Fin 3 =>
            h3FromFourierRealL2
              (h3SpectralVelocityDecodeRealL2 U j)) := by
    apply continuous_pi
    intro j
    exact continuous_h3SelectedPhysicalL2CoordinateDecode j

  have hToHilbert :
      Continuous
        (WithLp.toLp (2 : ℝ≥0∞) :
          (Fin 3 → H3ScalarL2) →
            H3PhysicalRealFinVectorL2Hilbert) := by
    exact
      PiLp.continuous_toLp
        (2 : ℝ≥0∞)
        (fun _ : Fin 3 => H3ScalarL2)

  exact hToHilbert.comp hPi

/-- The canonical selected restart is strongly continuous in the physical
three-component `L²` Hilbert topology. -/
theorem continuous_h3PreterminalSelectedVelocityPhysicalL2HilbertAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    Continuous
      (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail) := by
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht hTail

  have hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  have hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht hE hTail

  have hW :
      Continuous
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀) :=
    continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  have hDecoded :=
    continuous_h3SelectedPhysicalL2HilbertDecode.comp hW

  apply hDecoded.congr
  intro q
  unfold h3PreterminalSelectedVelocityPhysicalL2HilbertAt
  rfl

/-- Under the endpoint-independent all-tests pressure frontier, the old physical
velocity path is strongly continuous in the native finite Hilbert topology. -/
theorem continuous_h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed_of_allPressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail) :
    Continuous
      (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail) := by
  obtain ⟨K, hK⟩ :=
    h3PreterminalCanonicalL2ZeroLipschitzOnElapsed_of_allDivergenceFreePressureDefect
      hNS ht htau hEnd hE hTail hPressure

  have hPi :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          fun j : Fin 3 =>
            h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q) := by
    apply continuous_pi
    intro j
    exact (hK j).continuous

  have hToHilbert :
      Continuous
        (WithLp.toLp (2 : ℝ≥0∞) :
          (Fin 3 → H3ScalarL2) →
            H3PhysicalRealFinVectorL2Hilbert) := by
    exact
      PiLp.continuous_toLp
        (2 : ℝ≥0∞)
        (fun _ : Fin 3 => H3ScalarL2)

  have h := hToHilbert.comp hPi

  change
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        (WithLp.toLp
          (2 : ℝ≥0∞)
          (fun j : Fin 3 =>
            h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q) :
          H3PhysicalRealFinVectorL2Hilbert))

  apply h.congr
  intro q
  rfl

/-- Under the same pressure frontier, the concrete selected-minus-old physical
difference is a strongly continuous Hilbert path on `[0,tau]`. -/
theorem continuous_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_of_allPressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail) :
    Continuous
      (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail) := by
  have hSelected :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ)) :=
    (continuous_h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      hNS ht hE hTail).comp continuous_subtype_val

  have hOld :
      Continuous
        (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail) :=
    continuous_h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed_of_allPressureDefect
      hNS ht htau hEnd hE hTail hPressure

  change
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ)
          -
        h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)

  exact hSelected.sub hOld

/-- The ambient-real zero extension of the selected-minus-old difference is
continuous on the physical closed elapsed interval. -/
theorem continuousOn_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_of_allPressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail) :
    ContinuousOn
      (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail)
      (Set.Icc (0 : ℝ) tau) := by
  rw [continuousOn_iff_continuous_domRestrict]

  have hEq :
      (Set.Icc (0 : ℝ) tau).domRestrict
          (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail)
        =
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail := by
    funext q

    exact
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
        hNS ht hEnd hE hTail q.property

  rw [hEq]

  exact
    continuous_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_of_allPressureDefect
      hNS ht htau hEnd hE hTail hPressure

/-- The selected-minus-old squared physical `L²` norm is continuous on the
closed elapsed interval. -/
theorem continuousOn_norm_sq_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_of_allPressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail) :
    ContinuousOn
      (fun r : ℝ =>
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail r‖ ^ 2)
      (Set.Icc (0 : ℝ) tau) := by
  have hD :=
    continuousOn_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_of_allPressureDefect
      hNS ht htau hEnd hE hTail hPressure

  exact
    (continuous_norm.comp_continuousOn hD).pow 2

end

end Euclidean
end Bridge
end PrimeTensor
