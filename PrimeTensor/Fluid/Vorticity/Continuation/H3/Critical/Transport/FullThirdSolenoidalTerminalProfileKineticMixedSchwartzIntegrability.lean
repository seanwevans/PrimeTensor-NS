import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticMixedWeightedSpectralBridge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalAnnularBudgetIntegrability
import Mathlib.Tactic

/-!
# Automatic integrability of the three-profile native sixth-flux contractions

The preceding mixed Young theorem works with THREE independent complex Fourier
polarization profiles.  Its mixed six-dimensional budget must genuinely be
integrable, rather than inferred from diagonal integrability by polarizing an
unordered trilinear form.  We prove this for arbitrary THREE Schwartz fields.

Every native contraction expands into a finite double coordinate sum. The
single Fourier frequency multiplier is placed on the Schwartz transform at
that SAME frequency. The existing measure-preserving Schwartz-triad L1 theorem
then proves unconditional global integrability of all three mixed contractions
and of their exact sum-of-norms budget, without solenoidality or extra moment
assumptions.

The low-maximum sixth-flux kernel is also integrable on its literal cutoff
sector. This last conclusion uses the exact cubic radial coefficient bound,
together with strong measurability obtained from the three integrable complex
contractions and continuous squared-radius coefficients. It is a local result:
no uniform-in-radius or global H3 bound is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev IA3 := PrimeTensor.Axis Depth.three
private abbrev IV3 := H3FourierPoint3
private abbrev IPair := IV3 × IV3

noncomputable local instance axisFintypeKineticMixedIntegrable244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- First genuine mixed contraction, with independent p, q, r Schwartz data. -/
noncomputable def thirdFullKineticMixedSchwartzFirstContraction244
    (v w h : IA3 → SchwartzMap IV3 ℂ) (z : IPair) : ℂ :=
  (∑ j : IA3, (𝓕 (v j)) z.1 * (𝓕 (h j)) z.2) *
    (∑ m : IA3, (((WithLp.ofLp z.2 m : ℝ) : ℂ) *
      (𝓕 (w m)) (-(z.1 + z.2))))

/-- Middle frequency acts on the actual THIRD independent Schwartz field. -/
noncomputable def thirdFullKineticMixedSchwartzSecondContraction244
    (v w h : IA3 → SchwartzMap IV3 ℂ) (z : IPair) : ℂ :=
  (∑ j : IA3, (𝓕 (v j)) z.1 * (𝓕 (w j)) (-(z.1 + z.2))) *
    (∑ m : IA3, (((WithLp.ofLp (-(z.1 + z.2)) m : ℝ) : ℂ) *
      (𝓕 (h m)) z.2))

/-- Last contraction: r differentiates the FIRST independent profile. -/
noncomputable def thirdFullKineticMixedSchwartzThirdContraction244
    (v w h : IA3 → SchwartzMap IV3 ℂ) (z : IPair) : ℂ :=
  (∑ j : IA3, (𝓕 (w j)) (-(z.1 + z.2)) * (𝓕 (h j)) z.2) *
    (∑ m : IA3, (((WithLp.ofLp z.2 m : ℝ) : ℂ) *
      (𝓕 (v m)) z.1))

private theorem thirdFullKinetic_mixedSchwartz_doubleSum244
    (a b c d : IA3 → ℂ) :
    (∑ j : IA3, a j * b j) * (∑ m : IA3, c m * d m) =
      ∑ j : IA3, ∑ m : IA3, (a j * (c m * b j)) * d m := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- A coordinate multiplier can be put on the third outer Schwartz slot. -/
private theorem thirdFullKinetic_mixedSchwartz_weightedOuter_integrable244
    (f g h : SchwartzMap IV3 ℂ) (m : IA3) :
    Integrable (fun z : IPair =>
      ((𝓕 f z.1 * (((WithLp.ofLp z.2 m : ℝ) : ℂ) * 𝓕 h z.2)) *
        𝓕 g (-(z.1 + z.2)))) (volume.prod volume) := by
  have hi := h3Schwartz_triad_integrable
    (𝓕 f) (𝓕 g)
    (h3Schwartz_frequencyWeight (h3FourierAxisDirection m) (𝓕 h))
  apply hi.congr
  filter_upwards with z
  simp only [h3Schwartz_frequencyWeight_apply, inner_h3FourierAxisDirection]

/-- A coordinate multiplier can instead be put on the middle Schwartz slot. -/
private theorem thirdFullKinetic_mixedSchwartz_weightedMiddle_integrable244
    (f g h : SchwartzMap IV3 ℂ) (m : IA3) :
    Integrable (fun z : IPair =>
      ((𝓕 f z.1 *
          (((WithLp.ofLp (-(z.1 + z.2)) m : ℝ) : ℂ) *
            𝓕 g (-(z.1 + z.2)))) * 𝓕 h z.2))
      (volume.prod volume) := by
  have hi := h3Schwartz_triad_integrable
    (𝓕 f)
    (h3Schwartz_frequencyWeight (h3FourierAxisDirection m) (𝓕 g))
    (𝓕 h)
  apply hi.congr
  filter_upwards with z
  simp only [h3Schwartz_frequencyWeight_apply, inner_h3FourierAxisDirection]
  ring

/-- No shared polarization profile is needed to integrate the first term. -/
theorem thirdFullKinetic_mixedSchwartz_first_integrable244
    (v w h : IA3 → SchwartzMap IV3 ℂ) :
    Integrable (thirdFullKineticMixedSchwartzFirstContraction244 v w h)
      (volume.prod volume) := by
  have hTerm (j m : IA3) :
      Integrable (fun z : IPair =>
        ((𝓕 (v j) z.1 *
          (((WithLp.ofLp z.2 m : ℝ) : ℂ) * 𝓕 (h j) z.2)) *
          𝓕 (w m) (-(z.1 + z.2)))) (volume.prod volume) :=
    thirdFullKinetic_mixedSchwartz_weightedOuter_integrable244
      (v j) (w m) (h j) m
  have hSum : Integrable (fun z : IPair =>
      ∑ j : IA3, ∑ m : IA3,
        ((𝓕 (v j) z.1 *
          (((WithLp.ofLp z.2 m : ℝ) : ℂ) * 𝓕 (h j) z.2)) *
          𝓕 (w m) (-(z.1 + z.2)))) (volume.prod volume) := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro m _
    exact hTerm j m
  apply hSum.congr
  filter_upwards with z
  exact (thirdFullKinetic_mixedSchwartz_doubleSum244
    (fun j => 𝓕 (v j) z.1) (fun j => 𝓕 (h j) z.2)
    (fun m => (((WithLp.ofLp z.2 m : ℝ) : ℂ)))
    (fun m => 𝓕 (w m) (-(z.1 + z.2)))).symm

/-- The q-frequency multiplier is attached to the middle Fourier factor. -/
theorem thirdFullKinetic_mixedSchwartz_second_integrable244
    (v w h : IA3 → SchwartzMap IV3 ℂ) :
    Integrable (thirdFullKineticMixedSchwartzSecondContraction244 v w h)
      (volume.prod volume) := by
  have hTerm (j m : IA3) :
      Integrable (fun z : IPair =>
        ((𝓕 (v j) z.1 *
          (((WithLp.ofLp (-(z.1 + z.2)) m : ℝ) : ℂ) *
            𝓕 (w j) (-(z.1 + z.2)))) * 𝓕 (h m) z.2))
        (volume.prod volume) :=
    thirdFullKinetic_mixedSchwartz_weightedMiddle_integrable244
      (v j) (w j) (h m) m
  have hSum : Integrable (fun z : IPair =>
      ∑ j : IA3, ∑ m : IA3,
        ((𝓕 (v j) z.1 *
          (((WithLp.ofLp (-(z.1 + z.2)) m : ℝ) : ℂ) *
            𝓕 (w j) (-(z.1 + z.2)))) * 𝓕 (h m) z.2))
        (volume.prod volume) := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro m _
    exact hTerm j m
  apply hSum.congr
  filter_upwards with z
  exact (thirdFullKinetic_mixedSchwartz_doubleSum244
    (fun j => 𝓕 (v j) z.1)
    (fun j => 𝓕 (w j) (-(z.1 + z.2)))
    (fun m => (((WithLp.ofLp (-(z.1 + z.2)) m : ℝ) : ℂ)))
    (fun m => 𝓕 (h m) z.2)).symm

/-- The differentiated first profile in the third term is still Schwartz. -/
theorem thirdFullKinetic_mixedSchwartz_third_integrable244
    (v w h : IA3 → SchwartzMap IV3 ℂ) :
    Integrable (thirdFullKineticMixedSchwartzThirdContraction244 v w h)
      (volume.prod volume) := by
  have hTerm (j m : IA3) :
      Integrable (fun z : IPair =>
        ((𝓕 (w j) (-(z.1 + z.2)) *
          (((WithLp.ofLp z.2 m : ℝ) : ℂ) * 𝓕 (h j) z.2)) *
          𝓕 (v m) z.1)) (volume.prod volume) := by
    have hi := thirdFullKinetic_mixedSchwartz_weightedOuter_integrable244
      (v m) (w j) (h j) m
    apply hi.congr
    filter_upwards with z
    ring
  have hSum : Integrable (fun z : IPair =>
      ∑ j : IA3, ∑ m : IA3,
        ((𝓕 (w j) (-(z.1 + z.2)) *
          (((WithLp.ofLp z.2 m : ℝ) : ℂ) * 𝓕 (h j) z.2)) *
          𝓕 (v m) z.1)) (volume.prod volume) := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro m _
    exact hTerm j m
  apply hSum.congr
  filter_upwards with z
  exact (thirdFullKinetic_mixedSchwartz_doubleSum244
    (fun j => 𝓕 (w j) (-(z.1 + z.2)))
    (fun j => 𝓕 (h j) z.2)
    (fun m => (((WithLp.ofLp z.2 m : ℝ) : ℂ)))
    (fun m => 𝓕 (v m) z.1)).symm

/-- The independent-Schwartz budget is EXACTLY these three complex norms. -/
theorem thirdFullKinetic_mixedSchwartzBudget_eq_norms244
    (v w h : IA3 → SchwartzMap IV3 ℂ) (z : IPair) :
    thirdFullKineticMixedPolarSixthBudget244
        (thirdFullKineticSchwartzPolarization244 v)
        (thirdFullKineticSchwartzPolarization244 w)
        (thirdFullKineticSchwartzPolarization244 h) z =
      ‖thirdFullKineticMixedSchwartzFirstContraction244 v w h z‖ +
      ‖thirdFullKineticMixedSchwartzSecondContraction244 v w h z‖ +
      ‖thirdFullKineticMixedSchwartzThirdContraction244 v w h z‖ := by
  simp only [thirdFullKineticMixedPolarSixthBudget244,
    thirdFullComplexSixthFluxContractionBudget244,
    thirdFullComplexPolarizationDot244, mixedDot,
    thirdFullKineticMixedSchwartzFirstContraction244,
    thirdFullKineticMixedSchwartzSecondContraction244,
    thirdFullKineticMixedSchwartzThirdContraction244,
    thirdFullKineticSchwartzPolarization244,
    h3SchwartzTriadPolarization, WithLp.toLp_ofLp]

/-- All mixed three-profile native contraction budgets are globally L1. -/
theorem thirdFullKinetic_mixedSchwartzBudget_integrable244
    (v w h : IA3 → SchwartzMap IV3 ℂ) :
    Integrable (thirdFullKineticMixedPolarSixthBudget244
      (thirdFullKineticSchwartzPolarization244 v)
      (thirdFullKineticSchwartzPolarization244 w)
      (thirdFullKineticSchwartzPolarization244 h))
      (volume.prod volume) := by
  have hSum : Integrable (fun z : IPair =>
      ‖thirdFullKineticMixedSchwartzFirstContraction244 v w h z‖ +
      ‖thirdFullKineticMixedSchwartzSecondContraction244 v w h z‖ +
      ‖thirdFullKineticMixedSchwartzThirdContraction244 v w h z‖)
      (volume.prod volume) :=
    ((thirdFullKinetic_mixedSchwartz_first_integrable244 v w h).norm.add
      (thirdFullKinetic_mixedSchwartz_second_integrable244 v w h).norm).add
      (thirdFullKinetic_mixedSchwartz_third_integrable244 v w h).norm
  exact hSum.congr (Filter.Eventually.of_forall (fun z =>
    (thirdFullKinetic_mixedSchwartzBudget_eq_norms244 v w h z).symm))

/-! ## Bounded-radius Fourier flux: measurability and integrability -/

private noncomputable def thirdFullKinetic_mixedRadialGapRP244 (z : IPair) : ℂ :=
  ((thirdTriadAxisDot244 (WithLp.ofLp z.2) (WithLp.ofLp z.2) : ℂ) ^ 3 -
    (thirdTriadAxisDot244 (WithLp.ofLp z.1) (WithLp.ofLp z.1) : ℂ) ^ 3)

private noncomputable def thirdFullKinetic_mixedRadialGapQP244 (z : IPair) : ℂ :=
  ((thirdTriadAxisDot244 (WithLp.ofLp (-(z.1 + z.2)))
      (WithLp.ofLp (-(z.1 + z.2))) : ℂ) ^ 3 -
    (thirdTriadAxisDot244 (WithLp.ofLp z.1) (WithLp.ofLp z.1) : ℂ) ^ 3)

private noncomputable def thirdFullKinetic_mixedRadialGapRQ244 (z : IPair) : ℂ :=
  ((thirdTriadAxisDot244 (WithLp.ofLp z.2) (WithLp.ofLp z.2) : ℂ) ^ 3 -
    (thirdTriadAxisDot244 (WithLp.ofLp (-(z.1 + z.2)))
      (WithLp.ofLp (-(z.1 + z.2))) : ℂ) ^ 3)

private theorem thirdFullKinetic_mixedAxisSquare_eq_normSq244 (ξ : IV3) :
    thirdTriadAxisDot244 (WithLp.ofLp ξ) (WithLp.ofLp ξ) = ‖ξ‖ ^ 2 := by
  simpa only [thirdTriadAxisDot244, dot, frequencyNorm, WithLp.toLp_ofLp]
    using (dot_self_eq_frequencyNorm_sq (WithLp.ofLp ξ))

private theorem thirdFullKinetic_mixedRadialGapRP_continuous244 :
    Continuous thirdFullKinetic_mixedRadialGapRP244 := by
  have hEq : thirdFullKinetic_mixedRadialGapRP244 =
      (fun z : IPair => ((‖z.2‖ ^ 2 : ℝ) : ℂ) ^ 3 -
        ((‖z.1‖ ^ 2 : ℝ) : ℂ) ^ 3) := by
    funext z
    simp only [thirdFullKinetic_mixedRadialGapRP244,
      thirdFullKinetic_mixedAxisSquare_eq_normSq244]
  rw [hEq]
  exact ((Complex.continuous_ofReal.comp (continuous_snd.norm.pow 2)).pow 3).sub
    ((Complex.continuous_ofReal.comp (continuous_fst.norm.pow 2)).pow 3)

private theorem thirdFullKinetic_mixedRadialGapQP_continuous244 :
    Continuous thirdFullKinetic_mixedRadialGapQP244 := by
  have hMiddle : Continuous (fun z : IPair => -(z.1 + z.2)) :=
    (continuous_fst.add continuous_snd).neg
  have hEq : thirdFullKinetic_mixedRadialGapQP244 =
      (fun z : IPair => ((‖-(z.1 + z.2)‖ ^ 2 : ℝ) : ℂ) ^ 3 -
        ((‖z.1‖ ^ 2 : ℝ) : ℂ) ^ 3) := by
    funext z
    simp only [thirdFullKinetic_mixedRadialGapQP244,
      thirdFullKinetic_mixedAxisSquare_eq_normSq244]
  rw [hEq]
  exact ((Complex.continuous_ofReal.comp (hMiddle.norm.pow 2)).pow 3).sub
    ((Complex.continuous_ofReal.comp (continuous_fst.norm.pow 2)).pow 3)

private theorem thirdFullKinetic_mixedRadialGapRQ_continuous244 :
    Continuous thirdFullKinetic_mixedRadialGapRQ244 := by
  have hMiddle : Continuous (fun z : IPair => -(z.1 + z.2)) :=
    (continuous_fst.add continuous_snd).neg
  have hEq : thirdFullKinetic_mixedRadialGapRQ244 =
      (fun z : IPair => ((‖z.2‖ ^ 2 : ℝ) : ℂ) ^ 3 -
        ((‖-(z.1 + z.2)‖ ^ 2 : ℝ) : ℂ) ^ 3) := by
    funext z
    simp only [thirdFullKinetic_mixedRadialGapRQ244,
      thirdFullKinetic_mixedAxisSquare_eq_normSq244]
  rw [hEq]
  exact ((Complex.continuous_ofReal.comp (continuous_snd.norm.pow 2)).pow 3).sub
    ((Complex.continuous_ofReal.comp (hMiddle.norm.pow 2)).pow 3)

/-- The FULL mixed Schwartz sixth flux is measurable without requiring
solenoidal identities, and retaining its three complex radial coefficients. -/
theorem thirdFullKinetic_mixedSchwartzFlux_aestronglyMeasurable244
    (v w h : IA3 → SchwartzMap IV3 ℂ) :
    AEStronglyMeasurable
      (thirdFullKineticMixedPolarSixthFlux244
        (thirdFullKineticSchwartzPolarization244 v)
        (thirdFullKineticSchwartzPolarization244 w)
        (thirdFullKineticSchwartzPolarization244 h))
      (volume.prod volume) := by
  have hEq :
      thirdFullKineticMixedPolarSixthFlux244
        (thirdFullKineticSchwartzPolarization244 v)
        (thirdFullKineticSchwartzPolarization244 w)
        (thirdFullKineticSchwartzPolarization244 h) =
      (fun z : IPair =>
        thirdFullKineticMixedSchwartzFirstContraction244 v w h z *
          thirdFullKinetic_mixedRadialGapRP244 z +
        thirdFullKineticMixedSchwartzSecondContraction244 v w h z *
          thirdFullKinetic_mixedRadialGapQP244 z +
        thirdFullKineticMixedSchwartzThirdContraction244 v w h z *
          thirdFullKinetic_mixedRadialGapRQ244 z) := by
    funext z
    unfold thirdFullKineticMixedPolarSixthFlux244
      thirdFullComplexSixthPowerFlux244
      thirdFullKineticMixedSchwartzFirstContraction244
      thirdFullKineticMixedSchwartzSecondContraction244
      thirdFullKineticMixedSchwartzThirdContraction244
      thirdFullKinetic_mixedRadialGapRP244
      thirdFullKinetic_mixedRadialGapQP244
      thirdFullKinetic_mixedRadialGapRQ244
      thirdFullComplexPolarizationDot244 mixedDot
      thirdFullKineticSchwartzPolarization244
    simp only [h3SchwartzTriadPolarization, WithLp.toLp_ofLp]
  rw [hEq]
  exact (((thirdFullKinetic_mixedSchwartz_first_integrable244 v w h).aestronglyMeasurable.mul
      thirdFullKinetic_mixedRadialGapRP_continuous244.aestronglyMeasurable).add
    ((thirdFullKinetic_mixedSchwartz_second_integrable244 v w h).aestronglyMeasurable.mul
        thirdFullKinetic_mixedRadialGapQP_continuous244.aestronglyMeasurable)).add
      ((thirdFullKinetic_mixedSchwartz_third_integrable244 v w h).aestronglyMeasurable.mul
        thirdFullKinetic_mixedRadialGapRQ_continuous244.aestronglyMeasurable)

/-- The mixed flux itself, not merely its unsigned contraction budget, is
integrable on the actual LowMax(R) sector for EVERY Schwartz triple. -/
theorem thirdFullKinetic_lowMax_mixedSchwartzFlux_integrable244
    (R : ℕ) (v w h : IA3 → SchwartzMap IV3 ℂ) :
    IntegrableOn
      (thirdFullKineticMixedPolarSixthFlux244
        (thirdFullKineticSchwartzPolarization244 v)
        (thirdFullKineticSchwartzPolarization244 w)
        (thirdFullKineticSchwartzPolarization244 h))
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume) := by
  let P := thirdFullKineticSchwartzPolarization244 v
  let Q := thirdFullKineticSchwartzPolarization244 w
  let W := thirdFullKineticSchwartzPolarization244 h
  let S : Set IPair := (thirdFullHighMaxSet244 R)ᶜ
  let μ : Measure IPair := volume.prod volume
  let K : ℝ := 3 * (2 * ((R : ℝ) + 1)) ^ 6
  have hBudget : Integrable
      (thirdFullKineticMixedPolarSixthBudget244 P Q W) μ :=
    thirdFullKinetic_mixedSchwartzBudget_integrable244 v w h
  have hMeas : AEStronglyMeasurable
      (thirdFullKineticMixedPolarSixthFlux244 P Q W) (μ.restrict S) :=
    (thirdFullKinetic_mixedSchwartzFlux_aestronglyMeasurable244 v w h).restrict
  have hDom : IntegrableOn
      (fun z : IPair => K * thirdFullKineticMixedPolarSixthBudget244 P Q W z)
      S μ := (hBudget.const_mul K).integrableOn
  apply hDom.mono' hMeas
  filter_upwards [ae_restrict_mem (thirdFullHighMaxSet_measurable244 R).compl]
    with z hz
  exact thirdFullKinetic_lowMax_mixedFlux_le_radiusBudget244 R P Q W z hz

/-- All prior analytic integrability contracts for the REAL mixed Schwartz
flux estimate now follow automatically, for three independently chosen
Schwartz profiles and any radial cutoff. -/
theorem thirdFullKinetic_lowMax_mixedSchwartzFlux_autoWeightedH3_244
    (R : ℕ)
    (v w h : IA3 → SchwartzMap IV3 ℂ)
    (V W H : H3SpectralVelocityState)
    (hv : ∀ j : IA3,
      (V (h3ClassicalizationFinOfAxis j) : IV3 → ℂ) =ᵐ[volume]
        (fun ξ : IV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : IA3,
      (W (h3ClassicalizationFinOfAxis j) : IV3 → ℂ) =ᵐ[volume]
        (fun ξ : IV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (hh : ∀ j : IA3,
      (H (h3ClassicalizationFinOfAxis j) : IV3 → ℂ) =ᵐ[volume]
        (fun ξ : IV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (h j)) ξ))
    (scale : ℝ) (hscale : 0 < scale) :
    (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      ‖thirdFullKineticMixedPolarSixthFlux244
        (thirdFullKineticSchwartzPolarization244 v)
        (thirdFullKineticSchwartzPolarization244 w)
        (thirdFullKineticSchwartzPolarization244 h) z‖
        ∂volume.prod volume) ≤
    (9 * (2 * ((R : ℝ) + 1)) ^ 7) *
      (((scale ^ 2 * (3 * ‖V‖ ^ 2) +
        scale⁻¹ ^ 2 * (3 * ‖H‖ ^ 2)) / 2) *
        (3 * h3SobolevDeweightingConstant * ‖W‖)) := by
  exact thirdFullKinetic_lowMax_mixedSchwartzFlux_le_spectralVelocities244
    R v w h V W H hv hw hh
    (thirdFullKinetic_lowMax_mixedSchwartzFlux_integrable244 R v w h)
    (thirdFullKinetic_mixedSchwartzBudget_integrable244 v w h)
    scale hscale

end
end PrimeTensor.FirstMonomialTriad
