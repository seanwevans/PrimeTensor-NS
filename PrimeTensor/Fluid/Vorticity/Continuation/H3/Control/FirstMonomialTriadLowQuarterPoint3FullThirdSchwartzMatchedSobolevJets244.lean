import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzDecoderRealization244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzWeightedCanonicalCompletion244
import Mathlib.Tactic

/-!
# Synchronize decoder, Sobolev L²/L⁴ jets and the signed cubic on ONE sequence

The prior matched weighted-H³ construction established exact second and third
Schwartz/physical jets and Cauchy control of their full E₂/E₃ energies, but
its public theorem discarded the zero-order decoder equality. Meanwhile the
full-third C¹ bridge used a separately chosen Schwartz sequence. A new
backwards-compatible stronger matched-energy theorem retains the zero decoder.

The identical real Schwartz approximants therefore enjoy:
* true pointwise zero-jet reconstruction from their own weighted state;
* the actual first derivative convergence by spectral H³ continuity;
* full 81-slot third-order L² and 27-slot second-order L⁴ Cauchy control
  using the ALREADY PROVED quartic Gagliardo--Nirenberg estimate;
* convergence of the 243-slot signed first monomial to the established
  choice-independent weighted-H³ canonical functional.

This theorem does not identify the latter scalar with the physical third-order
Navier--Stokes commutator of an arbitrary nonsmooth snapshot. Neither full
fourth-order dissipation approximation nor the signed continuation criterion
is smuggled into this proof.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeMatchedSobolev244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The stronger matched construction supplies an actual pointwise realization
for the SAME approximants whose E₂/E₃ differences vanish in the mixed graph. -/
theorem exists_thirdFullSchwartz_matchedDecoderAndMixedGraph244
    (U : H3SpectralVelocityState) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      Tendsto V atTop (𝓝 U) ∧
      (∀ n : ℕ, ∀ j : Fin 3,
        h3SchwartzPoint3Scalar (Ψ n j) =
          h3SpectralScalarRealC1RepresentativeOnPoint3 (V n j)) ∧
      SchwartzH3DifferenceEnergyCauchy244
        (fun n j => Ψ n (h3ClassicalizationFinOfAxis j)) ∧
      SchwartzMixedJetGraphCauchy244
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
  obtain ⟨V, Ψ, hWeighted, hDecoder, hEnergy, hSecond, hThird⟩ :=
    exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy_withDecoder244 U
  refine ⟨V, Ψ, hWeighted, ?_, hEnergy, hEnergy.toMixedGraph, hSecond, hThird⟩
  intro n j
  have hExact : h3SpectralScalarDecodeRealL2 (V n j) =
      (Ψ n j).toLp 2 (volume : Measure V3) := by
    exact hDecoder n j
  exact thirdFullSchwartz_zerothRealization_of_decoderEquality244
    (V n j) (Ψ n j) hExact

/-- The original 243 signed 3+2+2 slots are genuinely Cauchy in their
L²/L⁴ roots for the SAME first-derivative-matched real Schwartz family. -/
theorem exists_thirdFullSchwartz_matchedAll243StrongJetCauchy244
    (U : H3SpectralVelocityState) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      Tendsto V atTop (𝓝 U) ∧
      (∀ n : ℕ, ∀ j : Fin 3,
        h3SchwartzPoint3Scalar (Ψ n j) =
          h3SpectralScalarRealC1RepresentativeOnPoint3 (V n j)) ∧
      Schwartz243StrongJetCauchy244
        (fun n j => Ψ n (h3ClassicalizationFinOfAxis j)) := by
  obtain ⟨V, Ψ, hWeighted, hPointwise, _hEnergy, hMixed, _hSecond, _hThird⟩ :=
    exists_thirdFullSchwartz_matchedDecoderAndMixedGraph244 U
  exact ⟨V, Ψ, hWeighted, hPointwise, hMixed.toStrongJets⟩

/-- In particular all 27 actual second-jet L⁴ differences become uniformly
small for the chosen approximation sequence, simultaneously in the axes. -/
theorem exists_thirdFullSchwartz_allSecondJetsL4Cauchy244
    (U : H3SpectralVelocityState) :
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
          ∀ j a b : A3,
            schwartzSecondJetDifferenceRoot244
              (fun j => Ψ m (h3ClassicalizationFinOfAxis j))
              (fun j => Ψ n (h3ClassicalizationFinOfAxis j)) j a b < ε := by
  obtain ⟨_V, Ψ, _hWeighted, _hPointwise, _hEnergy, hMixed, _hSecond, _hThird⟩ :=
    exists_thirdFullSchwartz_matchedDecoderAndMixedGraph244 U
  refine ⟨Ψ, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := hMixed ε hε
  refine ⟨N, ?_⟩
  intro m hm n hn j a b
  let f : ℕ → A3 → SchwartzMap V3 ℝ :=
    fun k i => Ψ k (h3ClassicalizationFinOfAxis i)
  have hUpper := hN m hm n hn
  have hSlots :=
    schwartzMixedJetGraphDistance_bounds_slots244 (f m) (f n)
      (j, (a, (b, (j, j))))
  exact lt_of_le_of_lt hSlots.2.1 hUpper

/-- Full first-derivative convergence AND the complete mixed L²/L⁴ Sobolev
graph are synchronized for a single family of physical real Schwartz fields. -/
theorem exists_thirdFullSchwartz_matchedFirstAndHigherJets244
    (U : H3SpectralVelocityState) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      Tendsto V atTop (𝓝 U) ∧
      SchwartzMixedJetGraphCauchy244
        (fun n j => Ψ n (h3ClassicalizationFinOfAxis j)) ∧
      (∀ j : Fin 3, ∀ i : A3, ∀ x : V3,
        Tendsto (fun n =>
          (∂_{h3FourierAxisDirection i} (Ψ n j)) x) atTop
          (𝓝 (spatial3.d i
            (h3SpectralScalarRealC1RepresentativeOnPoint3 (U j))
            ((WithLp.ofLp : V3 → Point3) x)))) := by
  obtain ⟨V, Ψ, hWeighted, hMatch, _hEnergy, hMixed, _hSecond, _hThird⟩ :=
    exists_thirdFullSchwartz_matchedDecoderAndMixedGraph244 U
  refine ⟨V, Ψ, hWeighted, hMixed, ?_⟩
  intro j i x
  have hCoordinate : Tendsto (fun n => V n j) atTop (𝓝 (U j)) :=
    (tendsto_pi_nhds.mp hWeighted) j
  have hNorm : Tendsto (fun n => ‖V n j - U j‖)
      atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hCoordinate
  exact thirdFullSchwartz_matchedFirstJet_tendsto_canonical244
    (fun n => V n j) (U j) (fun n => Ψ n j)
    (fun n => hMatch n j) hNorm i x

/-- These approximants converge to the already-established *canonical*
signed 243-slot completion, rather than merely an unnamed Cauchy limit. -/
theorem exists_thirdFullSchwartz_decoderMatchedCanonicalMonomial244
    (U : H3SpectralVelocityState) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      Tendsto V atTop (𝓝 U) ∧
      (∀ n j,
        h3SchwartzPoint3Scalar (Ψ n j) =
          h3SpectralScalarRealC1RepresentativeOnPoint3 (V n j)) ∧
      SchwartzMixedJetGraphCauchy244
        (fun n j => Ψ n (h3ClassicalizationFinOfAxis j)) ∧
      Tendsto
        (fun n => lowNormalRealSchwartzPoint3Monomial
          (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (weightedH3CanonicalSignedFirstMonomial244 U)) := by
  obtain ⟨V, Ψ, hWeighted, hMatch, hEnergy, hGraph, hSecond, hThird⟩ :=
    exists_thirdFullSchwartz_matchedDecoderAndMixedGraph244 U
  let f : ℕ → A3 → SchwartzMap V3 ℝ :=
    fun n j => Ψ n (h3ClassicalizationFinOfAxis j)
  let F : SchwartzH3CauchyFamily244 := ⟨f, hEnergy⟩
  let W : WeightedH3MatchedSchwartzCompletion244 U := {
    spectral := V
    family := F
    spectral_tendsto := hWeighted
    second_exact := by
      intro n j a b
      change (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (Ψ n (h3ClassicalizationFinOfAxis j)))).toLp
            2 (volume : Measure V3) =
        h3ToFourierRealL2
          (h3SpectralVelocitySecondPhysicalJetFamily244 (V n)
            (h3ClassicalizationFinOfAxis j) a b)
      exact hSecond n j a b
    third_exact := by
      intro n j a b c
      change (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c}
            (Ψ n (h3ClassicalizationFinOfAxis j))))).toLp
              2 (volume : Measure V3) =
        h3ToFourierRealL2
          (h3SpectralVelocityThirdPhysicalJetFamily244 (V n)
            (h3ClassicalizationFinOfAxis j) a b c)
      exact hThird n j a b c
  }
  refine ⟨V, Ψ, hWeighted, hMatch, hGraph, ?_⟩
  change Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial
      (W.family.approximants n)) atTop
    (𝓝 (weightedH3CanonicalSignedFirstMonomial244 U))
  exact weightedH3CanonicalSignedFirstMonomial_tendsto244 U W

end
end PrimeTensor.FirstMonomialTriad
