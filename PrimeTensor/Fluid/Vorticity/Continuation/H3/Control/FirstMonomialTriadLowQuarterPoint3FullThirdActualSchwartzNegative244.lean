import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdActualHermitianIntegral244
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-!
# The complete actual Schwartz H³ commutator has a strictly negative witness

The preceding theorem identifies the TRUE real divergence-free Schwartz
third-order commutator with one product of three genuine compact frequency
windows times the fully projected Hermitian physical six-orbit. This module
proves a *global* sign, not merely a negative sharp-center polynomial or a
negative integral over a manually restricted subset.

The common window is nonnegative; if it is nonzero, the first and third
windows confine the entire Fourier pair to an arbitrarily small neighborhood
of the original (p,r) center. The projected six-orbit is strictly negative on
that neighborhood. The window equals one at the exact conserving center,
so continuity supplies a non-null region of STRICT negativity. Integrability
follows from the already proved sector-polynomial integrability and the six
measure-preserving permutations.

This is a static Schwartz noncancellation witness, not a singular solution
or an unforced dynamical continuation estimate.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology SchwartzMap

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev V3 := H3FourierPoint3
private abbrev PairV244 := V3 × V3

noncomputable local instance axisFintypeActualSchwartzNegative244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Each of the three real compact cutoffs is pointwise nonnegative. -/
theorem thirdFullPositiveCommonThreeWindow_nonneg244
    (ρ : ℝ) (hρ : 0 < ρ) (z : PairV244) :
    0 ≤ thirdFullPositiveCommonThreeWindow244 ρ hρ z := by
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p,r)
  have hp : 0 ≤ (thirdFullAxisWindowBump244 ρ hρ 0 : Freq244 → ℝ) p :=
    (thirdFullAxisWindowBump244 ρ hρ 0).nonneg' p
  have hq : 0 ≤ (thirdFullAxisWindowBump244 ρ hρ 1 : Freq244 → ℝ) q :=
    (thirdFullAxisWindowBump244 ρ hρ 1).nonneg' q
  have hr : 0 ≤ (thirdFullAxisWindowBump244 ρ hρ 2 : Freq244 → ℝ) r :=
    (thirdFullAxisWindowBump244 ρ hρ 2).nonneg' r
  change 0 ≤
    ((thirdFullAxisWindowBump244 ρ hρ 0 : Freq244 → ℝ) p *
      (thirdFullAxisWindowBump244 ρ hρ 1 : Freq244 → ℝ) q) *
      (thirdFullAxisWindowBump244 ρ hρ 2 : Freq244 → ℝ) r
  exact mul_nonneg (mul_nonneg hp hq) hr

/-- If the genuine three-window product is nonzero, BOTH independent
frequencies are within width ρ of their actual positive sharp centers. -/
theorem thirdFullPositiveCommonThreeWindow_support_closedBall244
    (ρ : ℝ) (hρ : 0 < ρ) (z : PairV244)
    (hW : thirdFullPositiveCommonThreeWindow244 ρ hρ z ≠ 0) :
    (WithLp.ofLp z.1, WithLp.ofLp z.2) ∈ Metric.closedBall
      (thirdFullAxisSixCenter244 0, thirdFullAxisSixCenter244 2) ρ := by
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p,r)
  let wp : ℝ := (thirdFullAxisWindowBump244 ρ hρ 0 : Freq244 → ℝ) p
  let wq : ℝ := (thirdFullAxisWindowBump244 ρ hρ 1 : Freq244 → ℝ) q
  let wr : ℝ := (thirdFullAxisWindowBump244 ρ hρ 2 : Freq244 → ℝ) r
  have hProduct : (wp * wq) * wr ≠ 0 := hW
  have hwp : wp ≠ 0 := by
    intro hz
    apply hProduct
    simp [hz]
  have hwr : wr ≠ 0 := by
    intro hz
    apply hProduct
    simp [hz]
  have hp := thirdFullAxisWindowBump_nonzero_ball244 ρ hρ 0 p hwp
  have hr := thirdFullAxisWindowBump_nonzero_ball244 ρ hρ 2 r hwr
  change dist (p,r)
    (thirdFullAxisSixCenter244 0, thirdFullAxisSixCenter244 2) ≤ ρ
  rw [Prod.dist_eq]
  exact max_le hp.le hr.le

/-- The original sharp triad center satisfies the *dependent* middle
frequency identity. No equality of Fourier carriers is assumed. -/
theorem thirdFullAxisFirstThreeCenters_middle244 :
    thirdFullMiddleFrequency244
      (thirdFullAxisSixCenter244 0, thirdFullAxisSixCenter244 2) =
        thirdFullAxisSixCenter244 1 := by
  funext a
  simp only [thirdFullMiddleFrequency244, Pi.neg_apply, Pi.add_apply]
  simp [thirdFullAxisSixCenter244, lowNormalSixCenter,
    lowNormalLatticeEmbedding, lowNormalSignedLatticeCenter] <;>
    split_ifs <;> norm_num

/-- At the sharp center, each of the THREE genuine smooth cutoffs is one. -/
theorem thirdFullPositiveCommonThreeWindow_at_center244
    (ρ : ℝ) (hρ : 0 < ρ) :
    thirdFullPositiveCommonThreeWindow244 ρ hρ
      (WithLp.toLp 2 (thirdFullAxisSixCenter244 0),
       WithLp.toLp 2 (thirdFullAxisSixCenter244 2)) = 1 := by
  change
    ((thirdFullAxisWindowBump244 ρ hρ 0 : Freq244 → ℝ)
        (WithLp.ofLp (WithLp.toLp 2 (thirdFullAxisSixCenter244 0))) *
     (thirdFullAxisWindowBump244 ρ hρ 1 : Freq244 → ℝ)
        (thirdFullMiddleFrequency244
          (WithLp.ofLp (WithLp.toLp 2 (thirdFullAxisSixCenter244 0)),
           WithLp.ofLp (WithLp.toLp 2 (thirdFullAxisSixCenter244 2))))) *
     (thirdFullAxisWindowBump244 ρ hρ 2 : Freq244 → ℝ)
        (WithLp.ofLp (WithLp.toLp 2 (thirdFullAxisSixCenter244 2))) = 1
  simp only [WithLp.ofLp_toLp, thirdFullAxisFirstThreeCenters_middle244,
    thirdFullAxisWindowBump_at_center244]
  norm_num

/-- Continuity of the actual three-window factor on the Hilbert Fourier
product carrier. The intermediate axis carrier has the Pi/sup topology. -/
theorem thirdFullPositiveCommonThreeWindow_continuous244
    (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (thirdFullPositiveCommonThreeWindow244 ρ hρ) := by
  have hOf : Continuous (WithLp.ofLp : V3 → Freq244) :=
    PiLp.continuous_ofLp 2 (fun _ : A3 => ℝ)
  have hp : Continuous (fun z : PairV244 => WithLp.ofLp z.1) :=
    hOf.comp continuous_fst
  have hr : Continuous (fun z : PairV244 => WithLp.ofLp z.2) :=
    hOf.comp continuous_snd
  have hMiddle : Continuous (fun z : PairV244 =>
      thirdFullMiddleFrequency244 (WithLp.ofLp z.1, WithLp.ofLp z.2)) := by
    have hAlt : Continuous (fun z : PairV244 =>
        WithLp.ofLp (-(z.1 + z.2))) :=
      hOf.comp ((continuous_fst.add continuous_snd).neg)
    have hEq : (fun z : PairV244 =>
        thirdFullMiddleFrequency244 (WithLp.ofLp z.1, WithLp.ofLp z.2)) =
        (fun z : PairV244 => WithLp.ofLp (-(z.1 + z.2))) := by
      funext z
      exact thirdFullMiddleFrequency_ofLp_pair244 z
    rw [hEq]
    exact hAlt
  have h0 : Continuous (fun z : PairV244 =>
      (thirdFullAxisWindowBump244 ρ hρ 0 : Freq244 → ℝ)
        (WithLp.ofLp z.1)) :=
    (thirdFullAxisWindowBump_contDiff244 ρ hρ 0).continuous.comp hp
  have h1 : Continuous (fun z : PairV244 =>
      (thirdFullAxisWindowBump244 ρ hρ 1 : Freq244 → ℝ)
        (thirdFullMiddleFrequency244
          (WithLp.ofLp z.1, WithLp.ofLp z.2))) :=
    (thirdFullAxisWindowBump_contDiff244 ρ hρ 1).continuous.comp hMiddle
  have h2 : Continuous (fun z : PairV244 =>
      (thirdFullAxisWindowBump244 ρ hρ 2 : Freq244 → ℝ)
        (WithLp.ofLp z.2)) :=
    (thirdFullAxisWindowBump_contDiff244 ρ hρ 2).continuous.comp hr
  change Continuous (fun z : PairV244 =>
    ((thirdFullAxisWindowBump244 ρ hρ 0 : Freq244 → ℝ) (WithLp.ofLp z.1) *
     (thirdFullAxisWindowBump244 ρ hρ 1 : Freq244 → ℝ)
       (thirdFullMiddleFrequency244 (WithLp.ofLp z.1, WithLp.ofLp z.2))) *
     (thirdFullAxisWindowBump244 ρ hρ 2 : Freq244 → ℝ) (WithLp.ofLp z.2))
  exact (h0.mul h1).mul h2

/-- The TRUE frequency-weighted full-third projected Hermitian density is
integrable, by the earlier six genuine physical sector integrals. -/
theorem thirdFullPositiveCommonThreeWindow_hermitian_integrable244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) :
    Integrable (fun z : PairV244 =>
      thirdFullPositiveCommonThreeWindow244 ρ hρ z *
        thirdFullProjectedHermitianKernel244
          (thirdFullAxisSixCenter244 0)
          (thirdFullAxisSixCenter244 1)
          (thirdFullAxisSixCenter244 2) A B C
          (WithLp.ofLp z.1, WithLp.ofLp z.2))
      (volume.prod volume) := by
  have hInt : ∀ n : Fin 6,
      Integrable (thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n)
        (volume.prod volume) := by
    intro n
    exact thirdFullPositiveSectorPhysicalPolynomial_integrable244
      ρ hρ hSmall δ hρδ hDisj A B C n
  have hTrans : Integrable (fun z : PairV244 =>
      ∑ n : Fin 6,
        thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n
          (thirdFullPositivePairPermutationEquiv244 n z))
        (volume.prod volume) := by
    apply integrable_finsetSum
    intro n _
    exact thirdFullPositivePairPermutation_integrable244 n (hInt n)
  have hEq : (fun z : PairV244 =>
      thirdFullPositiveCommonThreeWindow244 ρ hρ z *
        thirdFullProjectedHermitianKernel244
          (thirdFullAxisSixCenter244 0)
          (thirdFullAxisSixCenter244 1)
          (thirdFullAxisSixCenter244 2) A B C
          (WithLp.ofLp z.1, WithLp.ofLp z.2)) =
      (fun z : PairV244 =>
        ∑ n : Fin 6,
          thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n
            (thirdFullPositivePairPermutationEquiv244 n z)) := by
    funext z
    exact (thirdFullPositivePhysicalSixPolynomials_eq_window_hermitian244
      ρ hρ A B C z).symm
  rw [hEq]
  exact hTrans

/-- A global, integrable real density cannot cancel if it is everywhere
nonpositive, continuous and strictly negative at one point of full support. -/
theorem thirdFullContinuousNonpositive_negative_integral244
    (F : PairV244 → ℝ) (hF : Continuous F)
    (hInt : Integrable F (volume.prod volume))
    (hNonpos : ∀ z, F z ≤ 0)
    (z₀ : PairV244) (hAt : F z₀ < 0) :
    (∫ z : PairV244, F z ∂volume.prod volume) < 0 := by
  let G : PairV244 → ℝ := fun z => -F z
  have hCont : Continuous G := hF.neg
  have hPos : 0 < G z₀ := neg_pos.mpr hAt
  have hOpen : IsOpen {z : PairV244 | 0 < G z} :=
    isOpen_lt continuous_const hCont
  obtain ⟨ε, hε, hSub⟩ := Metric.mem_nhds_iff.mp
    (hOpen.mem_nhds hPos)
  have hBall : Metric.ball z₀ ε ⊆ Function.support G ∩ Set.univ := by
    intro z hz
    constructor
    · exact ne_of_gt (hSub hz)
    · exact Set.mem_univ z
  have hMeasure :
      0 < (volume.prod volume) (Function.support G ∩ Set.univ) :=
    (Metric.measure_ball_pos (volume.prod volume) z₀ hε).trans_le
      (measure_mono hBall)
  have hNonneg : 0 ≤ᵐ[(volume.prod volume).restrict Set.univ] G := by
    simp only [Measure.restrict_univ]
    exact Filter.Eventually.of_forall (fun z => neg_nonneg.mpr (hNonpos z))
  have hIntOn : IntegrableOn G Set.univ (volume.prod volume) := by
    have hGI : Integrable G (volume.prod volume) := by
      dsimp only [G]
      exact hInt.neg
    -- `IntegrableOn` is an `Integrable` statement for the restricted measure.
    -- Normalize the target before rewriting the restriction of `univ`.
    change Integrable G ((volume.prod volume).restrict Set.univ)
    rw [Measure.restrict_univ]
    exact hGI
  have hIntegral : 0 < ∫ z in Set.univ, G z ∂volume.prod volume :=
    (setIntegral_pos_iff_support_of_nonneg_ae hNonneg hIntOn).2 hMeasure
  have hPosWhole : 0 < ∫ z : PairV244, G z ∂volume.prod volume := by
    simpa only [Measure.restrict_univ] using hIntegral
  have hNegWhole : 0 < -(∫ z : PairV244, F z ∂volume.prod volume) := by
    change 0 < (∫ z : PairV244, -F z ∂volume.prod volume) at hPosWhole
    simpa only [integral_neg] using hPosWhole
  exact neg_pos.mp hNegWhole

/-- Once the strict negative tube contains the support of the actual
Schwartz cutoffs, the full UNRESTRICTED weighted integral is negative. -/
theorem thirdFullActualCommonWindowHermitian_negative_of_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (R : ℝ) (hρR : ρ ≤ R)
    (hNeg : ∀ z ∈ Metric.closedBall
      (thirdFullAxisSixCenter244 0, thirdFullAxisSixCenter244 2) R,
        thirdFullProjectedHermitianKernel244
          (thirdFullAxisSixCenter244 0)
          (thirdFullAxisSixCenter244 1)
          (thirdFullAxisSixCenter244 2) A B C z < 0) :
    (∫ z : PairV244,
      thirdFullPositiveCommonThreeWindow244 ρ hρ z *
        thirdFullProjectedHermitianKernel244
          (thirdFullAxisSixCenter244 0)
          (thirdFullAxisSixCenter244 1)
          (thirdFullAxisSixCenter244 2) A B C
          (WithLp.ofLp z.1, WithLp.ofLp z.2)
        ∂volume.prod volume) < 0 := by
  let W : PairV244 → ℝ := thirdFullPositiveCommonThreeWindow244 ρ hρ
  let K : PairV244 → ℝ := fun z =>
    thirdFullProjectedHermitianKernel244
      (thirdFullAxisSixCenter244 0) (thirdFullAxisSixCenter244 1)
      (thirdFullAxisSixCenter244 2) A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2)
  let F : PairV244 → ℝ := fun z => W z * K z
  let z₀ : PairV244 :=
    (WithLp.toLp 2 (thirdFullAxisSixCenter244 0),
     WithLp.toLp 2 (thirdFullAxisSixCenter244 2))
  have hOf : Continuous (WithLp.ofLp : V3 → Freq244) :=
    PiLp.continuous_ofLp 2 (fun _ : A3 => ℝ)
  have hp : Continuous (fun z : PairV244 => WithLp.ofLp z.1) :=
    hOf.comp continuous_fst
  have hr : Continuous (fun z : PairV244 => WithLp.ofLp z.2) :=
    hOf.comp continuous_snd
  have hK : Continuous K :=
    (thirdFullProjectedHermitianKernel_continuous244
      (thirdFullAxisSixCenter244 0) (thirdFullAxisSixCenter244 1)
      (thirdFullAxisSixCenter244 2) A B C).comp (hp.prodMk hr)
  have hW : Continuous W :=
    thirdFullPositiveCommonThreeWindow_continuous244 ρ hρ
  have hF : Continuous F := hW.mul hK
  have hInt : Integrable F (volume.prod volume) :=
    thirdFullPositiveCommonThreeWindow_hermitian_integrable244
      ρ hρ hSmall δ hρδ hDisj A B C
  have hNonpos (z : PairV244) : F z ≤ 0 := by
    by_cases hw : W z = 0
    · simp [F, hw]
    · have hIn : (WithLp.ofLp z.1, WithLp.ofLp z.2) ∈ Metric.closedBall
          (thirdFullAxisSixCenter244 0, thirdFullAxisSixCenter244 2) R := by
        apply Metric.mem_closedBall.mpr
        exact (Metric.mem_closedBall.mp
          (thirdFullPositiveCommonThreeWindow_support_closedBall244
            ρ hρ z hw)).trans hρR
      have hn : K z < 0 := hNeg _ hIn
      have hw0 : 0 ≤ W z := thirdFullPositiveCommonThreeWindow_nonneg244 ρ hρ z
      change W z * K z ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos hw0 hn.le
  have hAtW : W z₀ = 1 :=
    thirdFullPositiveCommonThreeWindow_at_center244 ρ hρ
  have hAtK : K z₀ < 0 := by
    apply hNeg
    change (WithLp.ofLp (WithLp.toLp 2 (thirdFullAxisSixCenter244 0)),
      WithLp.ofLp (WithLp.toLp 2 (thirdFullAxisSixCenter244 2))) ∈
        Metric.closedBall
          (thirdFullAxisSixCenter244 0, thirdFullAxisSixCenter244 2) R
    simp only [WithLp.ofLp_toLp]
    have hR : 0 ≤ R := le_trans (le_of_lt hρ) hρR
    simpa only [Metric.mem_closedBall, dist_self] using hR
  have hAt : F z₀ < 0 := by
    change W z₀ * K z₀ < 0
    rw [hAtW]
    simpa only [one_mul] using hAtK
  exact thirdFullContinuousNonpositive_negative_integral244
    F hF hInt hNonpos z₀ hAt

/-- The full, actually realized real Schwartz third commutator is negative
whenever the fixed-center projected orbit has a negative support tube. -/
theorem thirdFullActualSchwartzCommutator_negative_of_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ < δ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (R : ℝ) (hρR : ρ ≤ R)
    (hNeg : ∀ z ∈ Metric.closedBall
      (thirdFullAxisSixCenter244 0, thirdFullAxisSixCenter244 2) R,
        thirdFullProjectedHermitianKernel244
          (thirdFullAxisSixCenter244 0)
          (thirdFullAxisSixCenter244 1)
          (thirdFullAxisSixCenter244 2) A B C z < 0) :
    fullSchwartzThirdCommutator244
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) < 0 := by
  rw [thirdFullAxisRealThirdCommutator_eq_commonWindowHermitian244
    ρ hρ hSmall δ hρδ hDisj A B C]
  have hc : 0 < 2 * (2 * Real.pi) ^ 7 := by positivity
  exact mul_neg_of_pos_of_neg hc
    (thirdFullActualCommonWindowHermitian_negative_of_tube244
      ρ hρ hSmall δ (le_of_lt hρδ) hDisj A B C R hρR hNeg)


/-- Identify the three original positive Schwartz-window centers with the
explicit momentum-conserving triad of the exact -192 physical calculation. -/
theorem thirdFullAxisFirstThreeCenters_explicit_negative244 :
    thirdFullAxisSixCenter244 0 =
      (fun a : A3 => if axisRank a = 0 then (1 : ℝ) else 0) ∧
    thirdFullAxisSixCenter244 1 =
      (fun a : A3 => if axisRank a = 0 then (1 : ℝ)
        else if axisRank a = 1 then 1 else 0) ∧
    thirdFullAxisSixCenter244 2 =
      (fun a : A3 => if axisRank a = 0 then (-2 : ℝ)
        else if axisRank a = 1 then -1 else 0) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    funext a
    simp [thirdFullAxisSixCenter244, lowNormalSixCenter,
      lowNormalLatticeEmbedding, lowNormalSignedLatticeCenter] <;>
      split_ifs <;> norm_num

/-- Unconditional noncancellation of the COMPLETE true third-order physical
Schwartz commutator. Both the gradient G₃ and interpolation 3M terms are
present. The witness is an actual three-component smooth, rapidly decaying
real velocity with Fourier-exact physical divergence zero. -/
theorem thirdFullActualSchwartz_exists_solenoidal_negative244 :
    ∃ (f : A3 → SchwartzMap V3 ℝ),
      (∀ x : V3, ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify (f j)) x
          (h3FourierAxisDirection j) = 0) ∧
      fullSchwartzThirdCommutator244 f < 0 := by
  let coord (x y z : ℝ) (a : A3) : ℝ :=
    if axisRank a = 0 then x else if axisRank a = 1 then y else z
  let p : Freq244 := coord 1 0 0
  let q : Freq244 := coord 1 1 0
  let r : Freq244 := coord (-2) (-1) 0
  let A : Freq244 := coord 0 1 0
  let B : Freq244 := coord 1 (-1) 0
  let C : Freq244 := coord 1 (-2) 0
  have hCenters :
      p = thirdFullAxisSixCenter244 0 ∧
      q = thirdFullAxisSixCenter244 1 ∧
      r = thirdFullAxisSixCenter244 2 := by
    obtain ⟨h0, h1, h2⟩ := thirdFullAxisFirstThreeCenters_explicit_negative244
    refine ⟨?_, h1.symm, h2.symm⟩
    rw [h0]
    funext a
    simp [p, coord]
  have hTriad :
      (∀ a : A3, p a + q a + r a = 0) ∧
      thirdTriadAxisDot244 A p = 0 ∧
      thirdTriadAxisDot244 B q = 0 ∧
      thirdTriadAxisDot244 C r = 0 :=
    thirdFullPhysicalTriad_solenoidal244
  have hpNorm : thirdTriadAxisDot244 p p = 1 := by
    unfold thirdTriadAxisDot244
    rw [axis_sum_three]
    norm_num [p, coord, axisRank, xAxis, yAxis, zAxis]
  have hqNorm : thirdTriadAxisDot244 q q = 2 := by
    unfold thirdTriadAxisDot244
    rw [axis_sum_three]
    norm_num [q, coord, axisRank, xAxis, yAxis, zAxis]
  have hrNorm : thirdTriadAxisDot244 r r = 5 := by
    unfold thirdTriadAxisDot244
    rw [axis_sum_three]
    norm_num [r, coord, axisRank, xAxis, yAxis, zAxis]
  have hp : thirdTriadAxisDot244 p p ≠ 0 := by rw [hpNorm]; norm_num
  have hq : thirdTriadAxisDot244 q q ≠ 0 := by rw [hqNorm]; norm_num
  have hr : thirdTriadAxisDot244 r r ≠ 0 := by rw [hrNorm]; norm_num
  have hValue : thirdFullHermitianMomentumKernel244 A B C (p,r) = -192 := by
    rw [thirdFullHermitianMomentumKernel_at_conserving_triad244
      p q r A B C hTriad.1]
    exact thirdFullPhysicalHermitianOrbit_explicit244
  -- The negative-closed-ball constructor expects the UNPROJECTED
  -- Hermitian center value; it performs the projection transfer itself.
  have hAt : thirdFullHermitianMomentumKernel244 A B C (p,r) < 0 := by
    rw [hValue]
    norm_num
  obtain ⟨R, hR, hNegBall⟩ :=
    thirdFullProjectedHermitianKernel_exists_negative_closedBall244
      p q r A B C hTriad.1 hTriad.2.1 hTriad.2.2.1
      hTriad.2.2.2 hp hq hr hAt
  have hNeg : ∀ z ∈ Metric.closedBall
      (thirdFullAxisSixCenter244 0, thirdFullAxisSixCenter244 2) R,
      thirdFullProjectedHermitianKernel244
        (thirdFullAxisSixCenter244 0)
        (thirdFullAxisSixCenter244 1)
        (thirdFullAxisSixCenter244 2) A B C z < 0 := by
    simpa only [← hCenters.1, ← hCenters.2.1, ← hCenters.2.2]
      using hNegBall
  let ρ : ℝ := min (R / 2) (1 / 8)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (half_pos hR) (by norm_num)
  have hρR : ρ ≤ R := by
    have hle : ρ ≤ R / 2 := min_le_left _ _
    linarith
  have hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ) := by
    have hle : ρ ≤ (1 / 8 : ℝ) := min_le_right _ _
    have hsep : lowNormalSixCenterSeparationRadius (1 : ℝ) = 1 / 4 := by
      norm_num [lowNormalSixCenterSeparationRadius]
    rw [hsep]
    linarith
  have hρδ : ρ < (1 / 4 : ℝ) := by
    have hle : ρ ≤ (1 / 8 : ℝ) := min_le_right _ _
    linarith
  have hDisj : 2 * (1 / 4 : ℝ) ≤ 1 := by norm_num
  let f : A3 → SchwartzMap V3 ℝ :=
    thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C
  have hDiv : ∀ x : V3, ∑ j : A3,
      fderiv ℝ (h3SchwartzComplexify (f j)) x
        (h3FourierAxisDirection j) = 0 :=
    thirdFullAxisRealSchwartz_physical_divergence244 ρ hρ A B C
  have hNegative : fullSchwartzThirdCommutator244 f < 0 :=
    thirdFullActualSchwartzCommutator_negative_of_tube244
      ρ hρ hSmall (1/4) hρδ hDisj A B C R hρR hNeg
  exact ⟨f, hDiv, hNegative⟩

end
end PrimeTensor.FirstMonomialTriad
