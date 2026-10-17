import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzWeightedCanonicalCompletion244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzCriticalHalfFromHolder244

/-!
# A native weighted H³ quartic bound for the canonical signed transport completion

The previous checkpoint constructed a choice-independent real-valued signed
243-slot monomial on arbitrary weighted spectral H³ velocities. It did not
transfer the existing *quantitative* signed Schwarz Holder/Gagliardo-Nirenberg
bound to the completed functional.

Here E₂(U) and E₃(U) are the squared real L² norms of all 27 and 81
*reconstructed physical* derivative coordinates. They depend continuously on
U, including at the zero spectral velocity. Exact Schwartz derivative
matching makes the literal E₂ and E₃ of each Schwartz witness equal to these
spectral energy functionals at its weighted approximation. Passage to the
limit then proves, without fourth-order smoothing assumptions,

  |M(U)|⁴ ≤ K⁴ E₂(U) E₃(U)⁵.

In particular the canonical signed observable vanishes at zero and is
continuous there. No solenoidality or equality to the physical nonlinear
Navier–Stokes transport integral is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev J2 := A3 × (A3 × A3)
private abbrev J3 := A3 × (A3 × (A3 × A3))

noncomputable local instance axisFintypeWeightedCanonicalQuartic244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- All ordered quadratic physical jets contribute, exactly once. -/
noncomputable def weightedH3CanonicalSecondJetEnergy244
    (U : H3SpectralVelocityState) : ℝ :=
  ∑ p : J2, ‖matchedSpectralSecondFourierJets244 U p‖ ^ 2

/-- All ordered cubic physical jets contribute, exactly once. -/
noncomputable def weightedH3CanonicalThirdJetEnergy244
    (U : H3SpectralVelocityState) : ℝ :=
  ∑ p : J3, ‖matchedSpectralThirdFourierJets244 U p‖ ^ 2

/-- Energy continuity is inherited from the actual 27-coordinate L²
reconstruction and the finite sum of real norm squares. -/
theorem continuous_weightedH3CanonicalSecondJetEnergy244 :
    Continuous weightedH3CanonicalSecondJetEnergy244 := by
  unfold weightedH3CanonicalSecondJetEnergy244
  apply continuous_finset_sum
  intro p hp
  exact (((continuous_apply p).comp
    continuous_matchedSpectralSecondFourierJets244).norm.pow 2)

/-- Exactly the same continuity statement for all 81 third jets. -/
theorem continuous_weightedH3CanonicalThirdJetEnergy244 :
    Continuous weightedH3CanonicalThirdJetEnergy244 := by
  unfold weightedH3CanonicalThirdJetEnergy244
  apply continuous_finset_sum
  intro p hp
  exact (((continuous_apply p).comp
    continuous_matchedSpectralThirdFourierJets244).norm.pow 2)

theorem weightedH3CanonicalSecondJetEnergy_nonneg244
    (U : H3SpectralVelocityState) :
    0 ≤ weightedH3CanonicalSecondJetEnergy244 U := by
  unfold weightedH3CanonicalSecondJetEnergy244
  apply Finset.sum_nonneg
  intro p hp
  positivity

theorem weightedH3CanonicalThirdJetEnergy_nonneg244
    (U : H3SpectralVelocityState) :
    0 ≤ weightedH3CanonicalThirdJetEnergy244 U := by
  unfold weightedH3CanonicalThirdJetEnergy244
  apply Finset.sum_nonneg
  intro p hp
  positivity

/-- Exact quadratic energy of one matched Schwartz representative, not an
approximation bound or a surrogate homogeneous seminorm. -/
theorem weightedH3MatchedSchwartzCompletion_secondEnergy_eq244
    (U : H3SpectralVelocityState)
    (F : WeightedH3MatchedSchwartzCompletion244 U) (n : ℕ) :
    lowNormalRealSchwartzH3Energy2 (F.family.approximants n) =
      weightedH3CanonicalSecondJetEnergy244 (F.spectral n) := by
  unfold lowNormalRealSchwartzH3Energy2
    weightedH3CanonicalSecondJetEnergy244
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← h3RealSchwartz_toLp_norm_sq_eq_integral244]
  rw [F.second_exact n j a b]

/-- Exact cubic energy of one matched Schwartz representative. -/
theorem weightedH3MatchedSchwartzCompletion_thirdEnergy_eq244
    (U : H3SpectralVelocityState)
    (F : WeightedH3MatchedSchwartzCompletion244 U) (n : ℕ) :
    lowNormalRealSchwartzH3Energy3 (F.family.approximants n) =
      weightedH3CanonicalThirdJetEnergy244 (F.spectral n) := by
  unfold lowNormalRealSchwartzH3Energy3
    weightedH3CanonicalThirdJetEnergy244
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  rw [← h3RealSchwartz_toLp_norm_sq_eq_integral244]
  rw [F.third_exact n j a b c]

/-- Second-order physical Schwartz energy converges to the genuine spectral
quadratic mass of the weighted H³ target. -/
theorem weightedH3MatchedSchwartzCompletion_secondEnergy_tendsto244
    (U : H3SpectralVelocityState)
    (F : WeightedH3MatchedSchwartzCompletion244 U) :
    Tendsto
      (fun n => lowNormalRealSchwartzH3Energy2 (F.family.approximants n))
      atTop (𝓝 (weightedH3CanonicalSecondJetEnergy244 U)) := by
  have h := continuous_weightedH3CanonicalSecondJetEnergy244.continuousAt.tendsto.comp
    F.spectral_tendsto
  simpa only [Function.comp_def,
    weightedH3MatchedSchwartzCompletion_secondEnergy_eq244 U F] using h

/-- Third-order physical Schwartz energy converges to the full 81-slot
spectral target mass. -/
theorem weightedH3MatchedSchwartzCompletion_thirdEnergy_tendsto244
    (U : H3SpectralVelocityState)
    (F : WeightedH3MatchedSchwartzCompletion244 U) :
    Tendsto
      (fun n => lowNormalRealSchwartzH3Energy3 (F.family.approximants n))
      atTop (𝓝 (weightedH3CanonicalThirdJetEnergy244 U)) := by
  have h := continuous_weightedH3CanonicalThirdJetEnergy244.continuousAt.tendsto.comp
    F.spectral_tendsto
  simpa only [Function.comp_def,
    weightedH3MatchedSchwartzCompletion_thirdEnergy_eq244 U F] using h

/-- The original signed Schwartz 243-slot quartic/GN estimate holds for
the *canonical completed weighted spectral* first monomial. The coefficient
is exactly the previously proved physical coefficient, without a new
untracked constant or an additional density hypothesis. -/
theorem weightedH3CanonicalSignedFirstMonomial_quarticBound244
    (U : H3SpectralVelocityState) :
    |weightedH3CanonicalSignedFirstMonomial244 U| ^ 4 ≤
      lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
        (weightedH3CanonicalSecondJetEnergy244 U *
          (weightedH3CanonicalThirdJetEnergy244 U) ^ 5) := by
  let F : WeightedH3MatchedSchwartzCompletion244 U :=
    weightedH3CanonicalSchwartzWitness244 U
  have hM := weightedH3CanonicalSignedFirstMonomial_tendsto244 U F
  have hE2 := weightedH3MatchedSchwartzCompletion_secondEnergy_tendsto244 U F
  have hE3 := weightedH3MatchedSchwartzCompletion_thirdEnergy_tendsto244 U F
  have hAbs :
      Tendsto (fun n => |lowNormalRealSchwartzPoint3Monomial
        (F.family.approximants n)|) atTop
        (𝓝 |weightedH3CanonicalSignedFirstMonomial244 U|) :=
    (continuous_abs.tendsto _).comp hM
  have hLeft :
      Tendsto (fun n => |lowNormalRealSchwartzPoint3Monomial
        (F.family.approximants n)| ^ 4) atTop
        (𝓝 (|weightedH3CanonicalSignedFirstMonomial244 U| ^ 4)) :=
    hAbs.pow 4
  have hRight :
      Tendsto (fun n =>
        lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
          (lowNormalRealSchwartzH3Energy2 (F.family.approximants n) *
            (lowNormalRealSchwartzH3Energy3 (F.family.approximants n)) ^ 5))
        atTop
        (𝓝 (lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
          (weightedH3CanonicalSecondJetEnergy244 U *
            (weightedH3CanonicalThirdJetEnergy244 U) ^ 5))) :=
    (tendsto_const_nhds.mul (hE2.mul (hE3.pow 5)))
  exact le_of_tendsto_of_tendsto hLeft hRight
    (Filter.Eventually.of_forall (fun n =>
      lowNormalRealSchwartz_firstMonomial_holder244_integerQuartic
        (F.family.approximants n)))

/-- The entire cubic physical-jet reconstruction of the zero weighted H³
state is exactly zero, by the existing quantitative norm estimate. -/
theorem weightedH3CanonicalThirdJetEnergy_zero244 :
    weightedH3CanonicalThirdJetEnergy244
      (0 : H3SpectralVelocityState) = 0 := by
  have hPhysicalZero (a b c : A3) :
      h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c
        (0 : H3SpectralScalarState) = 0 := by
    apply norm_eq_zero.mp
    have h := norm_h3SpectralScalarRawThirdCoordinatePhysicalL2_le244
      a b c (0 : H3SpectralScalarState)
    exact le_antisymm (by simpa using h) (norm_nonneg _)
  have hCarrierZero :
      h3ToFourierRealL2 (0 : H3ScalarL2) = 0 := by
    apply norm_eq_zero.mp
    rw [norm_h3ToFourierRealL2]
    simp
  have hPoint (p : J3) :
      matchedSpectralThirdFourierJets244 (0 : H3SpectralVelocityState) p = 0 := by
    rcases p with ⟨j, a, b, c⟩
    change h3ToFourierRealL2
      (h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c
        ((0 : H3SpectralVelocityState) (h3ClassicalizationFinOfAxis j))) = 0
    rw [Pi.zero_apply, hPhysicalZero, hCarrierZero]
  unfold weightedH3CanonicalThirdJetEnergy244
  simp only [hPoint, norm_zero]
  simp

/-- The nonlinear canonical signed completion vanishes at the zero
weighted spectral velocity, without a divergence-free premise. -/
theorem weightedH3CanonicalSignedFirstMonomial_zero244 :
    weightedH3CanonicalSignedFirstMonomial244
      (0 : H3SpectralVelocityState) = 0 := by
  have h := weightedH3CanonicalSignedFirstMonomial_quarticBound244
    (0 : H3SpectralVelocityState)
  rw [weightedH3CanonicalThirdJetEnergy_zero244] at h
  have hPower :
      |weightedH3CanonicalSignedFirstMonomial244
        (0 : H3SpectralVelocityState)| ^ 4 ≤ 0 := by
    simpa using h
  have hAbs : |weightedH3CanonicalSignedFirstMonomial244
      (0 : H3SpectralVelocityState)| = 0 := by
    by_contra hn
    have hp : 0 < |weightedH3CanonicalSignedFirstMonomial244
        (0 : H3SpectralVelocityState)| := by
      exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm hn)
    exact (not_lt_of_ge hPower) (pow_pos hp 4)
  exact abs_eq_zero.mp hAbs

/-- Continuity of the signed canonical completion at the zero weighted
spectral velocity. This is an analytic consequence of the full 27+81
quadratic/cubic matching and the quartic nonlinear estimate, not a
continuity hypothesis on the classical choice function. -/
theorem weightedH3CanonicalSignedFirstMonomial_continuousAt_zero244 :
    ContinuousAt weightedH3CanonicalSignedFirstMonomial244
      (0 : H3SpectralVelocityState) := by
  have hEnergyZero :
      Tendsto (fun U : H3SpectralVelocityState =>
        lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
          (weightedH3CanonicalSecondJetEnergy244 U *
            (weightedH3CanonicalThirdJetEnergy244 U) ^ 5))
        (𝓝 (0 : H3SpectralVelocityState)) (𝓝 (0 : ℝ)) := by
    have hCont : Continuous
        (fun U : H3SpectralVelocityState =>
          lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
            (weightedH3CanonicalSecondJetEnergy244 U *
              (weightedH3CanonicalThirdJetEnergy244 U) ^ 5)) := by
      exact continuous_const.mul
        (continuous_weightedH3CanonicalSecondJetEnergy244.mul
          (continuous_weightedH3CanonicalThirdJetEnergy244.pow 5))
    have h :
        Tendsto (fun U : H3SpectralVelocityState =>
          lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
            (weightedH3CanonicalSecondJetEnergy244 U *
              (weightedH3CanonicalThirdJetEnergy244 U) ^ 5))
          (𝓝 (0 : H3SpectralVelocityState))
          (𝓝 (lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
            (weightedH3CanonicalSecondJetEnergy244 0 *
              (weightedH3CanonicalThirdJetEnergy244 0) ^ 5))) :=
      hCont.continuousAt.tendsto
    simpa [weightedH3CanonicalThirdJetEnergy_zero244] using h
  have hFourth :
      Tendsto (fun U : H3SpectralVelocityState =>
        |weightedH3CanonicalSignedFirstMonomial244 U| ^ 4)
        (𝓝 (0 : H3SpectralVelocityState)) (𝓝 (0 : ℝ)) := by
    apply squeeze_zero
    · intro U
      exact pow_nonneg (abs_nonneg _) 4
    · intro U
      exact weightedH3CanonicalSignedFirstMonomial_quarticBound244 U
    · exact hEnergyZero
  have hSqrt :
      Tendsto (fun U : H3SpectralVelocityState =>
        Real.sqrt (Real.sqrt
          (|weightedH3CanonicalSignedFirstMonomial244 U| ^ 4)))
        (𝓝 (0 : H3SpectralVelocityState)) (𝓝 (0 : ℝ)) := by
    have h1 :
        Tendsto (fun U : H3SpectralVelocityState =>
          Real.sqrt (|weightedH3CanonicalSignedFirstMonomial244 U| ^ 4))
          (𝓝 (0 : H3SpectralVelocityState)) (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hFourth
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h1
  have hAbs :
      Tendsto (fun U : H3SpectralVelocityState =>
        |weightedH3CanonicalSignedFirstMonomial244 U|)
        (𝓝 (0 : H3SpectralVelocityState)) (𝓝 (0 : ℝ)) := by
    have hPointwise (U : H3SpectralVelocityState) :
        Real.sqrt (Real.sqrt
          (|weightedH3CanonicalSignedFirstMonomial244 U| ^ 4)) =
          |weightedH3CanonicalSignedFirstMonomial244 U| := by
      have hNonneg := abs_nonneg (weightedH3CanonicalSignedFirstMonomial244 U)
      rw [show |weightedH3CanonicalSignedFirstMonomial244 U| ^ 4 =
        (|weightedH3CanonicalSignedFirstMonomial244 U| ^ 2) ^ 2 by ring]
      rw [Real.sqrt_sq_eq_abs,
        abs_of_nonneg (pow_nonneg hNonneg 2),
        Real.sqrt_sq_eq_abs, abs_of_nonneg hNonneg]
    simpa only [hPointwise] using hSqrt
  have hTendsto :
      Tendsto weightedH3CanonicalSignedFirstMonomial244
        (𝓝 (0 : H3SpectralVelocityState)) (𝓝 (0 : ℝ)) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa only [sub_zero, Real.norm_eq_abs] using hAbs
  unfold ContinuousAt
  rw [weightedH3CanonicalSignedFirstMonomial_zero244]
  exact hTendsto

end
end PrimeTensor.FirstMonomialTriad
