import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzMatchedSecondFamily244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzH3CompletionInvariant244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Leray.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.L2.Jet.Continuity

/-!
# Matched real Schwartz H³ energies: from 27+81 L² jets to E₂/E₃ Cauchy

The same real Schwartz approximants from the compact weighted-frequency
construction have literal second and third derivative L² classes exactly
matching the continuous spectral reconstruction. We identify the physical
square integrals with the corresponding Euclidean L² norm squares. A finite
product Cauchy estimate gives the *actual* second- and third-order energy
Cauchy condition, without assuming it as an approximation hypothesis.

The existing Schwartz 243-slot completion theorem then assigns the family a
signed real limit. The result does NOT assert solenoidal Schwartz density or
identify that signed limit with the original Navier–Stokes transport integral.
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

noncomputable local instance axisFintypeMatchedEnergyCauchy244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Schwartz subtraction is exactly subtraction of the associated real L²
classes on the project's Euclidean Fourier carrier. -/
theorem h3RealSchwartz_toLp_sub244
    (f g : SchwartzMap V3 ℝ) :
    (f - g).toLp 2 (volume : Measure V3) =
      f.toLp 2 (volume : Measure V3) -
      g.toLp 2 (volume : Measure V3) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    (f - g).coeFn_toLp 2 (volume : Measure V3),
    f.coeFn_toLp 2 (volume : Measure V3),
    g.coeFn_toLp 2 (volume : Measure V3),
    MeasureTheory.Lp.coeFn_sub
      (f.toLp 2 (volume : Measure V3))
      (g.toLp 2 (volume : Measure V3))
  ] with x hSub hf hg hDiff
  rw [hSub, hDiff]
  simp only [Pi.sub_apply, hf, hg, sub_apply]

/-- Exact Plancherel-ready identification of one *real* Schwartz square
integral with its genuine real L² norm squared. -/
theorem h3RealSchwartz_toLp_norm_sq_eq_integral244
    (f : SchwartzMap V3 ℝ) :
    ‖f.toLp 2 (volume : Measure V3)‖ ^ 2 =
      ∫ x : V3, (f x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 (volume : Measure V3)] with x hx
  rw [hx]
  simp [Real.norm_eq_abs, sq_abs]

/-- The full 27-slot E₂ difference is the sum of actual *real L²* squared
distances of the literal ordered second Schwartz derivatives. -/
theorem h3RealSchwartz_differenceEnergy2_eq_Lp244
    (f g : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy2 (schwartzVelocityDifference244 f g) =
      ∑ j : A3, ∑ a : A3, ∑ b : A3,
        ‖(∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b} (f j))).toLp
               2 (volume : Measure V3) -
          (∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b} (g j))).toLp
               2 (volume : Measure V3)‖ ^ 2 := by
  unfold lowNormalRealSchwartzH3Energy2 schwartzVelocityDifference244
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [schwartzTwoLineDerivs_sub244]
  rw [← h3RealSchwartz_toLp_norm_sq_eq_integral244]
  rw [h3RealSchwartz_toLp_sub244]

/-- The full 81-slot E₃ difference is the sum of genuine L² squared
distances of all ordered third Schwartz derivatives. -/
theorem h3RealSchwartz_differenceEnergy3_eq_Lp244
    (f g : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy3 (schwartzVelocityDifference244 f g) =
      ∑ j : A3, ∑ a : A3, ∑ b : A3, ∑ c : A3,
        ‖(∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b}
              (∂_{h3FourierAxisDirection c} (f j)))).toLp
                2 (volume : Measure V3) -
          (∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b}
              (∂_{h3FourierAxisDirection c} (g j)))).toLp
                2 (volume : Measure V3)‖ ^ 2 := by
  unfold lowNormalRealSchwartzH3Energy3 schwartzVelocityDifference244
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [schwartzThreeLineDerivs_sub244]
  rw [← h3RealSchwartz_toLp_norm_sq_eq_integral244]
  rw [h3RealSchwartz_toLp_sub244]

/-- A Cauchy sequence in a finite sup-norm product has a Cauchy-small
sum of *all* coordinate squared L² differences, with one common tail. -/
theorem finite_pi_L2_squareEnergy_cauchy244
    {J : Type*} [Fintype J] [DecidableEq J]
    (F : ℕ → J → H3FourierRealL2) (hF : CauchySeq F) :
    ∀ η : ℝ, 0 < η →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
        (∑ p : J, ‖F m p - F n p‖ ^ 2) < η := by
  intro η hη
  let K : ℝ := (Fintype.card J : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let δ : ℝ := min 1 (η / K)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (div_pos hη hK)
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hF) δ hδ
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hDist : dist (F m) (F n) < δ := hN m hm n hn
  have hOne : dist (F m) (F n) ≤ 1 :=
    (le_of_lt hDist).trans (min_le_left _ _)
  have hDistNonneg : 0 ≤ dist (F m) (F n) := dist_nonneg
  have hSq : (dist (F m) (F n)) ^ 2 ≤ dist (F m) (F n) := by
    have hProduct : 0 ≤ dist (F m) (F n) *
        (1 - dist (F m) (F n)) :=
      mul_nonneg hDistNonneg (sub_nonneg.mpr hOne)
    nlinarith only [hProduct]
  have hTerm (p : J) :
      ‖F m p - F n p‖ ^ 2 ≤ (dist (F m) (F n)) ^ 2 := by
    have hCoord : ‖F m p - F n p‖ ≤ dist (F m) (F n) := by
      simpa only [dist_eq_norm, Pi.sub_apply] using
        (norm_le_pi_norm (F m - F n) p)
    exact pow_le_pow_left₀ (norm_nonneg _) hCoord 2
  have hSum :
      (∑ p : J, ‖F m p - F n p‖ ^ 2) ≤
        (Fintype.card J : ℝ) * (dist (F m) (F n)) ^ 2 := by
    calc
      _ ≤ ∑ _p : J, (dist (F m) (F n)) ^ 2 := by
        apply Finset.sum_le_sum
        intro p _
        exact hTerm p
      _ = (Fintype.card J : ℝ) * (dist (F m) (F n)) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hBound : (dist (F m) (F n)) ^ 2 ≤ η / K :=
    hSq.trans ((le_of_lt hDist).trans (min_le_right _ _))
  have hCard : 0 ≤ (Fintype.card J : ℝ) := by positivity
  have hStrict : (Fintype.card J : ℝ) * (η / K) < η := by
    have hCancel : (η / K) * K = η := div_mul_cancel₀ η (ne_of_gt hK)
    have hPos : 0 < η / K := div_pos hη hK
    dsimp [K] at hCancel
    nlinarith
  exact lt_of_le_of_lt (hSum.trans (mul_le_mul_of_nonneg_left hBound hCard))
    hStrict

/-- Once every second Schwartz derivative is identified with a coordinate
of a finite real L² product, the full 27-slot E₂ difference energy is exactly
the squared coordinate-distance sum. This lemma does not unfold any spectral
or Fourier decoder. -/
private theorem matched_second_difference_energy_eq_pi244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (F2 : ℕ → J2 → H3FourierRealL2)
    (hExact : ∀ n j a b,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b} (f n j))).toLp
          2 (volume : Measure V3) = F2 n (j, (a, b)))
    (m n : ℕ) :
    lowNormalRealSchwartzH3Energy2
      (schwartzVelocityDifference244 (f m) (f n)) =
        ∑ p : J2, ‖F2 m p - F2 n p‖ ^ 2 := by
  rw [h3RealSchwartz_differenceEnergy2_eq_Lp244]
  simp only [Fintype.sum_prod_type]
  simp_rw [hExact]

/-- Third-order analogue: the 81 genuine Schwartz square integrals equal
one finite-product L² squared difference norm. -/
private theorem matched_third_difference_energy_eq_pi244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (F3 : ℕ → J3 → H3FourierRealL2)
    (hExact : ∀ n j a b c,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c} (f n j)))).toLp
            2 (volume : Measure V3) = F3 n (j, (a, (b, c))))
    (m n : ℕ) :
    lowNormalRealSchwartzH3Energy3
      (schwartzVelocityDifference244 (f m) (f n)) =
        ∑ p : J3, ‖F3 m p - F3 n p‖ ^ 2 := by
  rw [h3RealSchwartz_differenceEnergy3_eq_Lp244]
  simp only [Fintype.sum_prod_type]
  simp_rw [hExact]

/-- One synchronized smooth-compact weighted spectral and real-Schwartz
sequence retains its exact zero-order real decoder alongside its
complete E₂/E₃ difference-energy Cauchy and matched physical jets.
In particular, it can be upgraded to pointwise C¹ realization. -/
theorem exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy_withDecoder244
    (U : H3SpectralVelocityState) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      Tendsto V atTop (𝓝 U) ∧
      (∀ n j, h3SpectralVelocityDecodeRealL2 (V n) j =
        (Ψ n j).toLp 2 (volume : Measure V3)) ∧
      SchwartzH3DifferenceEnergyCauchy244
        (fun n j => Ψ n (h3ClassicalizationFinOfAxis j)) ∧
      (∀ n j a b,
        (∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (Ψ n (h3ClassicalizationFinOfAxis j)))).toLp
              2 (volume : Measure V3) =
          h3ToFourierRealL2
            (h3SpectralVelocitySecondPhysicalJetFamily244 (V n)
              (h3ClassicalizationFinOfAxis j) a b)) ∧
      (∀ n j a b c,
        (∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (∂_{h3FourierAxisDirection c}
              (Ψ n (h3ClassicalizationFinOfAxis j))))).toLp
                2 (volume : Measure V3) =
          h3ToFourierRealL2
            (h3SpectralVelocityThirdPhysicalJetFamily244 (V n)
              (h3ClassicalizationFinOfAxis j) a b c)) := by
  classical
  obtain ⟨V, Ψ, hWeighted, hDecoderExact, hSecondExact, hThirdExact,
    hSecond, hThird⟩ :=
      exists_h3SmoothCompactWeighted_realSchwartzAllSecondThirdSequence244 U
  let f : ℕ → A3 → SchwartzMap V3 ℝ :=
    fun n j => Ψ n (h3ClassicalizationFinOfAxis j)
  let F2 : ℕ → J2 → H3FourierRealL2 := fun n p =>
    h3ToFourierRealL2
      (h3SpectralVelocitySecondPhysicalJetFamily244 (V n)
        (h3ClassicalizationFinOfAxis p.1) p.2.1 p.2.2)
  let F3 : ℕ → J3 → H3FourierRealL2 := fun n p =>
    h3ToFourierRealL2
      (h3SpectralVelocityThirdPhysicalJetFamily244 (V n)
        (h3ClassicalizationFinOfAxis p.1) p.2.1 p.2.2.1 p.2.2.2)
  have hMatch2 (n : ℕ) (j a b : A3) :
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b} (f n j))).toLp
          2 (volume : Measure V3) = F2 n (j, (a, b)) := by
    have h := congrArg h3ToFourierRealL2
      (hSecondExact n (h3ClassicalizationFinOfAxis j) a b)
    simpa only [f, F2, h3ToFourierRealL2_h3FromFourierRealL2] using h.symm
  have hMatch3 (n : ℕ) (j a b c : A3) :
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c} (f n j)))).toLp
            2 (volume : Measure V3) = F3 n (j, (a, (b, c))) := by
    have h := congrArg h3ToFourierRealL2
      (hThirdExact n (h3ClassicalizationFinOfAxis j) a b c)
    simpa only [f, F3, h3ToFourierRealL2_h3FromFourierRealL2] using h.symm
  have hC2 : CauchySeq F2 := by
    have hLimit := h3SpectralVelocitySecondPhysicalJetFamily_tendsto_of_weighted244 hWeighted
    have hT : Tendsto F2 atTop
        (𝓝 (fun p : J2 => h3ToFourierRealL2
          (h3SpectralVelocitySecondPhysicalJetFamily244 U
            (h3ClassicalizationFinOfAxis p.1) p.2.1 p.2.2))) := by
      rw [tendsto_pi_nhds]
      rintro ⟨j, a, b⟩
      have hCoord := (continuous_apply b).continuousAt.tendsto.comp
        ((continuous_apply a).continuousAt.tendsto.comp
          ((continuous_apply (h3ClassicalizationFinOfAxis j)).continuousAt.tendsto.comp
            hLimit))
      exact continuous_h3ToFourierRealL2.continuousAt.tendsto.comp hCoord
    exact hT.cauchySeq
  have hC3 : CauchySeq F3 := by
    have hLimit := h3SpectralVelocityThirdPhysicalJetFamily_tendsto_of_weighted244 hWeighted
    have hT : Tendsto F3 atTop
        (𝓝 (fun p : J3 => h3ToFourierRealL2
          (h3SpectralVelocityThirdPhysicalJetFamily244 U
            (h3ClassicalizationFinOfAxis p.1) p.2.1 p.2.2.1 p.2.2.2))) := by
      rw [tendsto_pi_nhds]
      rintro ⟨j, a, b, c⟩
      have hCoord := (continuous_apply c).continuousAt.tendsto.comp
        ((continuous_apply b).continuousAt.tendsto.comp
          ((continuous_apply a).continuousAt.tendsto.comp
            ((continuous_apply (h3ClassicalizationFinOfAxis j)).continuousAt.tendsto.comp
              hLimit)))
      exact continuous_h3ToFourierRealL2.continuousAt.tendsto.comp hCoord
    exact hT.cauchySeq
  have hE2 (m n : ℕ) :
      lowNormalRealSchwartzH3Energy2
        (schwartzVelocityDifference244 (f m) (f n)) =
          ∑ p : J2, ‖F2 m p - F2 n p‖ ^ 2 :=
    matched_second_difference_energy_eq_pi244 f F2 hMatch2 m n
  have hE3 (m n : ℕ) :
      lowNormalRealSchwartzH3Energy3
        (schwartzVelocityDifference244 (f m) (f n)) =
          ∑ p : J3, ‖F3 m p - F3 n p‖ ^ 2 :=
    matched_third_difference_energy_eq_pi244 f F3 hMatch3 m n
  have hEnergy : SchwartzH3DifferenceEnergyCauchy244 f := by
    intro η hη
    obtain ⟨N2, hN2⟩ := finite_pi_L2_squareEnergy_cauchy244 F2 hC2
      (η / 2) (by positivity)
    obtain ⟨N3, hN3⟩ := finite_pi_L2_squareEnergy_cauchy244 F3 hC3
      (η / 2) (by positivity)
    refine ⟨max N2 N3, ?_⟩
    intro m hm n hn
    have hm2 := le_trans (le_max_left N2 N3) hm
    have hn2 := le_trans (le_max_left N2 N3) hn
    have hm3 := le_trans (le_max_right N2 N3) hm
    have hn3 := le_trans (le_max_right N2 N3) hn
    constructor
    · rw [hE2 m n]
      exact (hN2 m hm2 n hn2).trans (by linarith)
    · rw [hE3 m n]
      exact (hN3 m hm3 n hn3).trans (by linarith)
  refine ⟨V, Ψ, hWeighted, hDecoderExact, hEnergy, ?_, ?_⟩
  · intro n j a b
    simpa only [f, F2] using hMatch2 n j a b
  · intro n j a b c
    simpa only [f, F3] using hMatch3 n j a b c

/-- Backwards-compatible projection of the strengthened construction. -/
theorem exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy_matched244
    (U : H3SpectralVelocityState) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      Tendsto V atTop (𝓝 U) ∧
      SchwartzH3DifferenceEnergyCauchy244
        (fun n j => Ψ n (h3ClassicalizationFinOfAxis j)) ∧
      (∀ n j a b,
        (∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (Ψ n (h3ClassicalizationFinOfAxis j)))).toLp
              2 (volume : Measure V3) =
          h3ToFourierRealL2
            (h3SpectralVelocitySecondPhysicalJetFamily244 (V n)
              (h3ClassicalizationFinOfAxis j) a b)) ∧
      (∀ n j a b c,
        (∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (∂_{h3FourierAxisDirection c}
              (Ψ n (h3ClassicalizationFinOfAxis j))))).toLp
                2 (volume : Measure V3) =
          h3ToFourierRealL2
            (h3SpectralVelocityThirdPhysicalJetFamily244 (V n)
              (h3ClassicalizationFinOfAxis j) a b c)) := by
  obtain ⟨V, Ψ, hWeighted, _hDecoder, hEnergy, hSecond, hThird⟩ :=
    exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy_withDecoder244 U
  exact ⟨V, Ψ, hWeighted, hEnergy, hSecond, hThird⟩

/-- Retain the existing public existence API unchanged, forgetting only the
newly exported exact quadratic and cubic Schwartz/Fourier jet witnesses. -/
theorem exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy244
    (U : H3SpectralVelocityState) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      Tendsto V atTop (𝓝 U) ∧
      SchwartzH3DifferenceEnergyCauchy244
        (fun n j => Ψ n (h3ClassicalizationFinOfAxis j)) := by
  obtain ⟨V, Ψ, hWeighted, hEnergy, _, _⟩ :=
    exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy_matched244 U
  exact ⟨V, Ψ, hWeighted, hEnergy⟩

/-- Every weighted H³ spectral velocity admits a genuinely real Schwartz
H³-energy Cauchy family, hence a well-defined completed signed 243-slot
Schwartz transport scalar, without asserting an identification with the
physical nonlinear transport of an arbitrary non-Schwartz slice. -/
theorem exists_h3WeightedPhysicalSchwartz_completedSignedFirstMonomial244
    (U : H3SpectralVelocityState) :
    ∃ F : SchwartzH3CauchyFamily244,
      Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial (F.approximants n))
        atTop (𝓝 (completedSchwartzH3FirstMonomial244 F)) := by
  obtain ⟨_, Ψ, _, hEnergy⟩ :=
    exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy244 U
  let F : SchwartzH3CauchyFamily244 :=
    ⟨(fun n j => Ψ n (h3ClassicalizationFinOfAxis j)), hEnergy⟩
  exact ⟨F, completedSchwartzH3FirstMonomial_tendsto244 F⟩

end
end PrimeTensor.FirstMonomialTriad
