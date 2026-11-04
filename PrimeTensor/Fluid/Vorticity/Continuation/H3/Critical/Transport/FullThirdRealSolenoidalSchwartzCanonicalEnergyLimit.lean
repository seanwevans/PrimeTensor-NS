import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdRealSolenoidalSchwartzMatchedH3Jets
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3WeightedCanonicalQuarticBound244
import Mathlib.Tactic

/-!
# Canonical physical E₂/E₃ and signed H³ transport along real solenoidal Schwartz density

The previous result constructs one actual real, physically divergence-free
Schwartz sequence with exactly matched second (27 slots) and third (81 slots)
derivatives in the weighted H³ spectral reconstruction.

Here these exact derivatives give the *original real spatial* quadratic
energies E₂ and E₃, not only equivalent norms. Their common H³ limit gives
an E₂/E₃-Cauchy Schwartz family. This supplies a valid matched witness for
the choice-independent canonical signed 243-slot completion and therefore
identifies the signed Schwartz limit of this same solenoidal family.

No assertion is made that the signed limit equals an arbitrary Navier--Stokes
solution's nonlinear transport at a nonsmooth time slice; that identification
is a separate PDE/physical-trace theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Filter Topology PrimeTensor.Bridge.Euclidean FourierTransform
open scoped BigOperators ENNReal SchwartzMap LineDeriv FourierTransform

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev J2 := A3 × (A3 × A3)
private abbrev J3 := A3 × (A3 × (A3 × A3))

noncomputable local instance axisFintypeSolenoidalCanonicalEnergy244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact 27/81 derivative matching from one Schwartz sequence is
sufficient for common-tail physical E₂/E₃ Cauchy control. No solenoidality
hypothesis is required by this (purely quadratic) step. -/
theorem thirdFullMatchedSchwartz_energyCauchy_of_weighted244
    (target : H3SpectralVelocityState)
    (V : ℕ → H3SpectralVelocityState)
    (Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ)
    (hV : Tendsto V atTop (𝓝 target))
    (hSecond : ∀ n j a b,
      h3SpectralVelocitySecondPhysicalJetFamily244 (V n) j a b =
        h3FromFourierRealL2
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b} (Ψ n j))).toLp
              2 (volume : Measure V3)))
    (hThird : ∀ n j a b c,
      h3SpectralVelocityThirdPhysicalJetFamily244 (V n) j a b c =
        h3FromFourierRealL2
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b}
              (∂_{h3FourierAxisDirection c} (Ψ n j)))).toLp
                2 (volume : Measure V3))) :
    SchwartzH3DifferenceEnergyCauchy244
      (fun n j => Ψ n (h3ClassicalizationFinOfAxis j)) := by
  classical
  let f : ℕ → A3 → SchwartzMap V3 ℝ :=
    fun n j => Ψ n (h3ClassicalizationFinOfAxis j)
  let F2 : ℕ → J2 → H3FourierRealL2 :=
    fun n => matchedSpectralSecondFourierJets244 (V n)
  let F3 : ℕ → J3 → H3FourierRealL2 :=
    fun n => matchedSpectralThirdFourierJets244 (V n)
  have hMatch2 (n : ℕ) (j a b : A3) :
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b} (f n j))).toLp
          2 (volume : Measure V3) = F2 n (j, (a, b)) := by
    have h := congrArg h3ToFourierRealL2
      (hSecond n (h3ClassicalizationFinOfAxis j) a b)
    simpa only [f, F2, matchedSpectralSecondFourierJets244,
      h3ToFourierRealL2_h3FromFourierRealL2] using h.symm
  have hMatch3 (n : ℕ) (j a b c : A3) :
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c} (f n j)))).toLp
            2 (volume : Measure V3) = F3 n (j, (a, (b, c))) := by
    have h := congrArg h3ToFourierRealL2
      (hThird n (h3ClassicalizationFinOfAxis j) a b c)
    simpa only [f, F3, matchedSpectralThirdFourierJets244,
      h3ToFourierRealL2_h3FromFourierRealL2] using h.symm
  have hF2 : CauchySeq F2 := by
    have hLimit : Tendsto F2 atTop
        (𝓝 (matchedSpectralSecondFourierJets244 target)) :=
      continuous_matchedSpectralSecondFourierJets244.continuousAt.tendsto.comp hV
    exact hLimit.cauchySeq
  have hF3 : CauchySeq F3 := by
    have hLimit : Tendsto F3 atTop
        (𝓝 (matchedSpectralThirdFourierJets244 target)) :=
      continuous_matchedSpectralThirdFourierJets244.continuousAt.tendsto.comp hV
    exact hLimit.cauchySeq
  have hE2 (m n : ℕ) :
      lowNormalRealSchwartzH3Energy2
        (schwartzVelocityDifference244 (f m) (f n)) =
          ∑ p : J2, ‖F2 m p - F2 n p‖ ^ 2 := by
    rw [h3RealSchwartz_differenceEnergy2_eq_Lp244]
    simp only [Fintype.sum_prod_type]
    simp_rw [hMatch2]
  have hE3 (m n : ℕ) :
      lowNormalRealSchwartzH3Energy3
        (schwartzVelocityDifference244 (f m) (f n)) =
          ∑ p : J3, ‖F3 m p - F3 n p‖ ^ 2 := by
    rw [h3RealSchwartz_differenceEnergy3_eq_Lp244]
    simp only [Fintype.sum_prod_type]
    simp_rw [hMatch3]
  change SchwartzH3DifferenceEnergyCauchy244 f
  intro η hη
  obtain ⟨N2, hN2⟩ :=
    finite_pi_L2_squareEnergy_cauchy244 F2 hF2 (η / 2) (by positivity)
  obtain ⟨N3, hN3⟩ :=
    finite_pi_L2_squareEnergy_cauchy244 F3 hF3 (η / 2) (by positivity)
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

/-- An actual solenoidal sequence with exact 27+81 matching defines a valid
choice-independent weighted H³ signed-completion witness. -/
noncomputable def thirdFullSolenoidalMatchedCompletion244
    (target : H3SpectralVelocityState)
    (V : ℕ → H3SpectralVelocityState)
    (Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ)
    (hV : Tendsto V atTop (𝓝 target))
    (hSecond : ∀ n j a b,
      h3SpectralVelocitySecondPhysicalJetFamily244 (V n) j a b =
        h3FromFourierRealL2
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b} (Ψ n j))).toLp
              2 (volume : Measure V3)))
    (hThird : ∀ n j a b c,
      h3SpectralVelocityThirdPhysicalJetFamily244 (V n) j a b c =
        h3FromFourierRealL2
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b}
              (∂_{h3FourierAxisDirection c} (Ψ n j)))).toLp
                2 (volume : Measure V3))) :
    WeightedH3MatchedSchwartzCompletion244 target := by
  let f : ℕ → A3 → SchwartzMap V3 ℝ :=
    fun n j => Ψ n (h3ClassicalizationFinOfAxis j)
  have hEnergy : SchwartzH3DifferenceEnergyCauchy244 f :=
    thirdFullMatchedSchwartz_energyCauchy_of_weighted244
      target V Ψ hV hSecond hThird
  refine {
    spectral := V
    family := ⟨f, hEnergy⟩
    spectral_tendsto := hV
    second_exact := ?_
    third_exact := ?_
  }
  · intro n j a b
    have h := congrArg h3ToFourierRealL2
      (hSecond n (h3ClassicalizationFinOfAxis j) a b)
    simpa only [f, matchedSpectralSecondFourierJets244,
      h3ToFourierRealL2_h3FromFourierRealL2] using h.symm
  · intro n j a b c
    have h := congrArg h3ToFourierRealL2
      (hThird n (h3ClassicalizationFinOfAxis j) a b c)
    simpa only [f, matchedSpectralThirdFourierJets244,
      h3ToFourierRealL2_h3FromFourierRealL2] using h.symm

/-- The constructed REAL SOLENOIDAL Schwartz sequence has exactly the
canonical 27-slot and 81-slot physical energies at each index, and its
signed 243-slot Schwartz transport converges to the same choice-independent
canonical signed H³ functional used elsewhere in the development. -/
theorem exists_thirdFullRealSolenoidalSchwartz_canonicalEnergySignedLimit244
    (target : H3SpectralVelocityState)
    (hDiv : H3SpectralFinDivergenceFree target)
    (hReal : H3SpectralVelocityRawHermitian target) :
    ∃ (V : ℕ → H3SpectralVelocityState)
      (Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ),
      Tendsto V atTop (𝓝 target) ∧
      (∀ (n : ℕ) (x : V3), ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) x
            (h3FourierAxisDirection j) = 0) ∧
      (∀ n j,
        (V n j : V3 → ℂ) =ᵐ[volume]
          (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
            𝓕 (h3SchwartzComplexify (Ψ n j)) ξ)) ∧
      (∀ n,
        lowNormalRealSchwartzH3Energy2
          (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)) =
        weightedH3CanonicalSecondJetEnergy244 (V n)) ∧
      (∀ n,
        lowNormalRealSchwartzH3Energy3
          (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)) =
        weightedH3CanonicalThirdJetEnergy244 (V n)) ∧
      Tendsto (fun n => lowNormalRealSchwartzH3Energy2
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (weightedH3CanonicalSecondJetEnergy244 target)) ∧
      Tendsto (fun n => lowNormalRealSchwartzH3Energy3
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (weightedH3CanonicalThirdJetEnergy244 target)) ∧
      SchwartzH3DifferenceEnergyCauchy244
        (fun n j => Ψ n (h3ClassicalizationFinOfAxis j)) ∧
      Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (weightedH3CanonicalSignedFirstMonomial244 target)) := by
  obtain ⟨V, Ψ, hV, hDivExact, hAE, _hDecoder, hSecond, hThird,
    _hDecodeLimit, _hSecondLimit, _hThirdLimit, _hVCauchy⟩ :=
    exists_thirdFullRealSolenoidalSchwartzMatchedH3Jets244
      target hDiv hReal
  let F : WeightedH3MatchedSchwartzCompletion244 target :=
    thirdFullSolenoidalMatchedCompletion244 target V Ψ hV hSecond hThird
  have hE2 (n : ℕ) :
      lowNormalRealSchwartzH3Energy2
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)) =
          weightedH3CanonicalSecondJetEnergy244 (V n) :=
    weightedH3MatchedSchwartzCompletion_secondEnergy_eq244 target F n
  have hE3 (n : ℕ) :
      lowNormalRealSchwartzH3Energy3
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)) =
          weightedH3CanonicalThirdJetEnergy244 (V n) :=
    weightedH3MatchedSchwartzCompletion_thirdEnergy_eq244 target F n
  have hE2Limit : Tendsto
      (fun n => lowNormalRealSchwartzH3Energy2
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
      atTop (𝓝 (weightedH3CanonicalSecondJetEnergy244 target)) :=
    weightedH3MatchedSchwartzCompletion_secondEnergy_tendsto244 target F
  have hE3Limit : Tendsto
      (fun n => lowNormalRealSchwartzH3Energy3
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
      atTop (𝓝 (weightedH3CanonicalThirdJetEnergy244 target)) :=
    weightedH3MatchedSchwartzCompletion_thirdEnergy_tendsto244 target F
  have hEnergy : SchwartzH3DifferenceEnergyCauchy244
      (fun n j => Ψ n (h3ClassicalizationFinOfAxis j)) :=
    thirdFullMatchedSchwartz_energyCauchy_of_weighted244
      target V Ψ hV hSecond hThird
  have hSigned : Tendsto
      (fun n => lowNormalRealSchwartzPoint3Monomial
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
      atTop (𝓝 (weightedH3CanonicalSignedFirstMonomial244 target)) :=
    weightedH3CanonicalSignedFirstMonomial_tendsto244 target F
  exact ⟨V, Ψ, hV, hDivExact, hAE, hE2, hE3,
    hE2Limit, hE3Limit, hEnergy, hSigned⟩

end
end PrimeTensor.FirstMonomialTriad
