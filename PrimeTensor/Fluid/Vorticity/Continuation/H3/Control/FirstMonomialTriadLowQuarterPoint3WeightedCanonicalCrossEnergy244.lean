import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3WeightedCanonicalQuarticBound244

/-!
# Exact two-state cross energies for matched weighted H³ Schwartz completions

The canonical scalar completion is already independent of which matched family
approaches a FIXED spectral velocity. To approach continuity at arbitrary
nonzero spectral velocities, one needs to control TWO distinct weighted limits.

The 27 second-derivative and 81 third-derivative Fourier L² jet maps are
continuous. We build their joint squared-distance energies, prove joint
continuity and vanishing on the diagonal, and then show that these precise
spectral masses are the limits of the LITERAL physical Schwartz cross-difference
energies for any two independent matched approximation families.

Crucially, this is a two-state result even when the target velocities differ.
It does not assert full continuity of the completed cubic signed scalar or
identify it with the original physical Navier--Stokes trilinear pairing.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev V3 := H3FourierPoint3
private abbrev J2 := (PrimeTensor.Axis Depth.three) ×
  (PrimeTensor.Axis Depth.three × PrimeTensor.Axis Depth.three)
private abbrev J3 := (PrimeTensor.Axis Depth.three) ×
  (PrimeTensor.Axis Depth.three ×
    (PrimeTensor.Axis Depth.three × PrimeTensor.Axis Depth.three))

noncomputable local instance axisFintypeWeightedCrossEnergy244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact cross difference of all 27 real physical quadratic L² jets. -/
noncomputable def weightedH3CanonicalCrossSecondJetEnergy244
    (U W : H3SpectralVelocityState) : ℝ :=
  ∑ p : J2,
    ‖matchedSpectralSecondFourierJets244 U p -
      matchedSpectralSecondFourierJets244 W p‖ ^ 2

/-- Exact cross difference of all 81 real physical cubic L² jets. -/
noncomputable def weightedH3CanonicalCrossThirdJetEnergy244
    (U W : H3SpectralVelocityState) : ℝ :=
  ∑ p : J3,
    ‖matchedSpectralThirdFourierJets244 U p -
      matchedSpectralThirdFourierJets244 W p‖ ^ 2

/-- The cross-energy of the two derivative orders together, retaining all
108 ordered coordinate slots. -/
noncomputable def weightedH3CanonicalCrossJetEnergy244
    (U W : H3SpectralVelocityState) : ℝ :=
  weightedH3CanonicalCrossSecondJetEnergy244 U W +
    weightedH3CanonicalCrossThirdJetEnergy244 U W

/-- Nonnegativity of the genuine second-order physical cross energy. -/
theorem weightedH3CanonicalCrossSecondJetEnergy_nonneg244
    (U W : H3SpectralVelocityState) :
    0 ≤ weightedH3CanonicalCrossSecondJetEnergy244 U W := by
  unfold weightedH3CanonicalCrossSecondJetEnergy244
  apply Finset.sum_nonneg
  intro p hp
  positivity

/-- Nonnegativity of the genuine third-order physical cross energy. -/
theorem weightedH3CanonicalCrossThirdJetEnergy_nonneg244
    (U W : H3SpectralVelocityState) :
    0 ≤ weightedH3CanonicalCrossThirdJetEnergy244 U W := by
  unfold weightedH3CanonicalCrossThirdJetEnergy244
  apply Finset.sum_nonneg
  intro p hp
  positivity

theorem weightedH3CanonicalCrossJetEnergy_nonneg244
    (U W : H3SpectralVelocityState) :
    0 ≤ weightedH3CanonicalCrossJetEnergy244 U W :=
  add_nonneg
    (weightedH3CanonicalCrossSecondJetEnergy_nonneg244 U W)
    (weightedH3CanonicalCrossThirdJetEnergy_nonneg244 U W)

/-- Cross quadratic energy is jointly continuous on the product of two
weighted H³ spaces; no Schwartz density assumption enters this statement. -/
theorem continuous_weightedH3CanonicalCrossSecondJetEnergy244 :
    Continuous (fun z : H3SpectralVelocityState × H3SpectralVelocityState =>
      weightedH3CanonicalCrossSecondJetEnergy244 z.1 z.2) := by
  unfold weightedH3CanonicalCrossSecondJetEnergy244
  apply continuous_finset_sum
  intro p hp
  have hLeft : Continuous
      (fun z : H3SpectralVelocityState × H3SpectralVelocityState =>
        matchedSpectralSecondFourierJets244 z.1 p) :=
    ((continuous_apply p).comp
      continuous_matchedSpectralSecondFourierJets244).comp continuous_fst
  have hRight : Continuous
      (fun z : H3SpectralVelocityState × H3SpectralVelocityState =>
        matchedSpectralSecondFourierJets244 z.2 p) :=
    ((continuous_apply p).comp
      continuous_matchedSpectralSecondFourierJets244).comp continuous_snd
  exact (hLeft.sub hRight).norm.pow 2

/-- Joint continuity of the full 81-coordinate third-derivative cross mass. -/
theorem continuous_weightedH3CanonicalCrossThirdJetEnergy244 :
    Continuous (fun z : H3SpectralVelocityState × H3SpectralVelocityState =>
      weightedH3CanonicalCrossThirdJetEnergy244 z.1 z.2) := by
  unfold weightedH3CanonicalCrossThirdJetEnergy244
  apply continuous_finset_sum
  intro p hp
  have hLeft : Continuous
      (fun z : H3SpectralVelocityState × H3SpectralVelocityState =>
        matchedSpectralThirdFourierJets244 z.1 p) :=
    ((continuous_apply p).comp
      continuous_matchedSpectralThirdFourierJets244).comp continuous_fst
  have hRight : Continuous
      (fun z : H3SpectralVelocityState × H3SpectralVelocityState =>
        matchedSpectralThirdFourierJets244 z.2 p) :=
    ((continuous_apply p).comp
      continuous_matchedSpectralThirdFourierJets244).comp continuous_snd
  exact (hLeft.sub hRight).norm.pow 2

/-- Joint continuity of both physical jet cross energies in one scalar. -/
theorem continuous_weightedH3CanonicalCrossJetEnergy244 :
    Continuous (fun z : H3SpectralVelocityState × H3SpectralVelocityState =>
      weightedH3CanonicalCrossJetEnergy244 z.1 z.2) := by
  exact continuous_weightedH3CanonicalCrossSecondJetEnergy244.add
    continuous_weightedH3CanonicalCrossThirdJetEnergy244

/-- Both cross energies vanish exactly on the spectral diagonal. -/
theorem weightedH3CanonicalCrossSecondJetEnergy_self244
    (U : H3SpectralVelocityState) :
    weightedH3CanonicalCrossSecondJetEnergy244 U U = 0 := by
  unfold weightedH3CanonicalCrossSecondJetEnergy244
  simp

theorem weightedH3CanonicalCrossThirdJetEnergy_self244
    (U : H3SpectralVelocityState) :
    weightedH3CanonicalCrossThirdJetEnergy244 U U = 0 := by
  unfold weightedH3CanonicalCrossThirdJetEnergy244
  simp

theorem weightedH3CanonicalCrossJetEnergy_self244
    (U : H3SpectralVelocityState) :
    weightedH3CanonicalCrossJetEnergy244 U U = 0 := by
  unfold weightedH3CanonicalCrossJetEnergy244
  rw [weightedH3CanonicalCrossSecondJetEnergy_self244,
    weightedH3CanonicalCrossThirdJetEnergy_self244]
  ring

/-- Different weighted targets U and W yield the *exact* limiting E₂ of
their independently constructed matched real Schwartz approximation families. -/
theorem weightedH3MatchedSchwartzCompletion_crossSecondEnergy_tendsto244
    (U W : H3SpectralVelocityState)
    (F : WeightedH3MatchedSchwartzCompletion244 U)
    (G : WeightedH3MatchedSchwartzCompletion244 W) :
    Tendsto
      (fun n => lowNormalRealSchwartzH3Energy2
        (schwartzVelocityDifference244
          (F.family.approximants n) (G.family.approximants n)))
      atTop (𝓝 (weightedH3CanonicalCrossSecondJetEnergy244 U W)) := by
  have hPair : Tendsto (fun n => (F.spectral n, G.spectral n))
      atTop (𝓝 (U, W)) :=
    Filter.Tendsto.prodMk_nhds F.spectral_tendsto G.spectral_tendsto
  have hLimit : Tendsto (fun n =>
      weightedH3CanonicalCrossSecondJetEnergy244 (F.spectral n) (G.spectral n))
      atTop (𝓝 (weightedH3CanonicalCrossSecondJetEnergy244 U W)) := by
    simpa only [Function.comp_def] using
      (continuous_weightedH3CanonicalCrossSecondJetEnergy244.continuousAt.tendsto.comp hPair)
  have hIdentity (n : ℕ) :
      lowNormalRealSchwartzH3Energy2
        (schwartzVelocityDifference244
          (F.family.approximants n) (G.family.approximants n)) =
      weightedH3CanonicalCrossSecondJetEnergy244 (F.spectral n) (G.spectral n) := by
    simpa only [weightedH3CanonicalCrossSecondJetEnergy244] using
      matchedSpectral_crossEnergy2_eq_squareSum244
        F.family G.family F.spectral G.spectral
        F.second_exact G.second_exact n
  simpa only [hIdentity] using hLimit

/-- The corresponding 81-slot exact limiting E₃ cross energy. -/
theorem weightedH3MatchedSchwartzCompletion_crossThirdEnergy_tendsto244
    (U W : H3SpectralVelocityState)
    (F : WeightedH3MatchedSchwartzCompletion244 U)
    (G : WeightedH3MatchedSchwartzCompletion244 W) :
    Tendsto
      (fun n => lowNormalRealSchwartzH3Energy3
        (schwartzVelocityDifference244
          (F.family.approximants n) (G.family.approximants n)))
      atTop (𝓝 (weightedH3CanonicalCrossThirdJetEnergy244 U W)) := by
  have hPair : Tendsto (fun n => (F.spectral n, G.spectral n))
      atTop (𝓝 (U, W)) :=
    Filter.Tendsto.prodMk_nhds F.spectral_tendsto G.spectral_tendsto
  have hLimit : Tendsto (fun n =>
      weightedH3CanonicalCrossThirdJetEnergy244 (F.spectral n) (G.spectral n))
      atTop (𝓝 (weightedH3CanonicalCrossThirdJetEnergy244 U W)) := by
    simpa only [Function.comp_def] using
      (continuous_weightedH3CanonicalCrossThirdJetEnergy244.continuousAt.tendsto.comp hPair)
  have hIdentity (n : ℕ) :
      lowNormalRealSchwartzH3Energy3
        (schwartzVelocityDifference244
          (F.family.approximants n) (G.family.approximants n)) =
      weightedH3CanonicalCrossThirdJetEnergy244 (F.spectral n) (G.spectral n) := by
    simpa only [weightedH3CanonicalCrossThirdJetEnergy244] using
      matchedSpectral_crossEnergy3_eq_squareSum244
        F.family G.family F.spectral G.spectral
        F.third_exact G.third_exact n
  simpa only [hIdentity] using hLimit

/-- Both genuine Schwartz cross energies converge to the two-state spectral
cross masses, simultaneously, for completely independent matched families. -/
theorem weightedH3MatchedSchwartzCompletion_crossEnergies_tendsto244
    (U W : H3SpectralVelocityState)
    (F : WeightedH3MatchedSchwartzCompletion244 U)
    (G : WeightedH3MatchedSchwartzCompletion244 W) :
    Tendsto (fun n =>
      (lowNormalRealSchwartzH3Energy2
        (schwartzVelocityDifference244
          (F.family.approximants n) (G.family.approximants n)),
       lowNormalRealSchwartzH3Energy3
        (schwartzVelocityDifference244
          (F.family.approximants n) (G.family.approximants n))))
      atTop (𝓝 (weightedH3CanonicalCrossSecondJetEnergy244 U W,
        weightedH3CanonicalCrossThirdJetEnergy244 U W)) :=
  Filter.Tendsto.prodMk_nhds
    (weightedH3MatchedSchwartzCompletion_crossSecondEnergy_tendsto244 U W F G)
    (weightedH3MatchedSchwartzCompletion_crossThirdEnergy_tendsto244 U W F G)

/-- Spectral convergence to one weighted velocity makes the combined 108-jet
cross energy vanish. This is the continuity input for a subsequent
quantitative stability theorem for the completed nonlinear signed functional. -/
theorem weightedH3CanonicalCrossJetEnergy_tendsto_zero_of_tendsto244
    {U : H3SpectralVelocityState}
    {V : ℕ → H3SpectralVelocityState}
    (hV : Tendsto V atTop (𝓝 U)) :
    Tendsto (fun n => weightedH3CanonicalCrossJetEnergy244 (V n) U)
      atTop (𝓝 (0 : ℝ)) := by
  have hPair : Tendsto (fun n => (V n, U))
      atTop (𝓝 (U, U)) :=
    Filter.Tendsto.prodMk_nhds hV tendsto_const_nhds
  have h := continuous_weightedH3CanonicalCrossJetEnergy244.continuousAt.tendsto.comp hPair
  simpa only [Function.comp_def, weightedH3CanonicalCrossJetEnergy_self244] using h

end
end PrimeTensor.FirstMonomialTriad
