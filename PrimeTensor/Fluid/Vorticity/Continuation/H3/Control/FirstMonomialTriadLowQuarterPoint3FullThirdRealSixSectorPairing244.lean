import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealImaginaryKernel244
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Measure-preserving Hermitian pairing of six full-third coherent sectors

The actual real, solenoidal Schwartz velocity's unphased imaginary H3
third-commutator kernel is pointwise even under simultaneous negation of
both Fourier variables, and its global physical integral is already exact.

We promote the pointwise reflection into an exact equality of integrals on
arbitrary measurable reflection-matched domains. Specializing to momentum-
pair balls and summing over the six positively oriented coherent labels
shows that their TWELVE labelled reflected-ball integrals are precisely
twice the six positive-orientation integrals.

CRUCIAL SCOPE: the labelled balls are not proved disjoint here, nor is the
complete coherent tube proved equal to their union. Thus the paired-ball
formula does not yet assert that their sum equals the global commutator;
that geometric partition and the remaining six-sector sign are separate.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 1000000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev V3 := H3FourierPoint3
private abbrev PairV244 := V3 × V3

noncomputable local instance axisFintypeSixPair244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact simultaneous frequency reflection on the product Hilbert
carrier. Both the forward and inverse maps negate BOTH momentum variables. -/
def thirdFullPairReflection244 : PairV244 ≃ᵐ PairV244 where
  toFun z := (-z.1, -z.2)
  invFun z := (-z.1, -z.2)
  left_inv z := by
    rcases z with ⟨p, r⟩
    simp
  right_inv z := by
    rcases z with ⟨p, r⟩
    simp
  measurable_toFun := measurable_fst.neg.prodMk measurable_snd.neg
  measurable_invFun := measurable_fst.neg.prodMk measurable_snd.neg

/-- Reflection preserves genuine six-dimensional PRODUCT Fourier volume;
there is no extra Jacobian or orientation determinant. -/
theorem thirdFullPairReflection_measurePreserving244 :
    MeasurePreserving thirdFullPairReflection244
      (volume.prod volume) (volume.prod volume) := by
  exact (Measure.measurePreserving_neg (volume : Measure V3)).prod
    (Measure.measurePreserving_neg (volume : Measure V3))

/-- Change of variables on the product Fourier carrier, with no hypotheses
on the integrand and hence no gratuitous integrability assumptions. -/
theorem thirdFullPairReflection_integral244 (f : PairV244 → ℝ) :
    (∫ z : PairV244, f (-z.1, -z.2) ∂volume.prod volume) =
      ∫ z : PairV244, f z ∂volume.prod volume := by
  exact thirdFullPairReflection_measurePreserving244.integral_comp
    thirdFullPairReflection244.measurableEmbedding f

/-- A generic exact equality of integrals over ANY two measurable domains
matched by Hermitian reflection. This is the main local-integration tool. -/
theorem thirdFullPairEven_integral_reflected_sets244
    (f : PairV244 → ℝ)
    (hf : ∀ z : PairV244, f (-z.1, -z.2) = f z)
    (s t : Set PairV244)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : ∀ z : PairV244, (-z.1, -z.2) ∈ t ↔ z ∈ s) :
    (∫ z in t, f z ∂volume.prod volume) =
      ∫ z in s, f z ∂volume.prod volume := by
  classical
  calc
    (∫ z in t, f z ∂volume.prod volume) =
        ∫ z : PairV244, t.indicator f z ∂volume.prod volume :=
      (integral_indicator ht).symm
    _ = ∫ z : PairV244, t.indicator f (-z.1, -z.2)
          ∂volume.prod volume :=
      (thirdFullPairReflection_integral244 (t.indicator f)).symm
    _ = ∫ z : PairV244, s.indicator f z ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ s
      · have hn : (-z.1, -z.2) ∈ t := (hst z).2 hz
        simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hn]
        exact hf z
      · have hn : (-z.1, -z.2) ∉ t := by
          intro hmem
          exact hz ((hst z).1 hmem)
        change (if (-z.1, -z.2) ∈ t then f (-z.1, -z.2) else 0) =
          (if z ∈ s then f z else 0)
        simp only [if_neg hn, if_neg hz]
    _ = (∫ z in s, f z ∂volume.prod volume) :=
      integral_indicator hs

/-- Reflection maps a product-Hilbert open ball to the open ball about
the opposite center, with exactly the same radius. -/
theorem thirdFullPairEven_integral_reflected_ball244
    (f : PairV244 → ℝ)
    (hf : ∀ z : PairV244, f (-z.1, -z.2) = f z)
    (center : PairV244) (δ : ℝ) :
    (∫ z in Metric.ball (-center) δ, f z ∂volume.prod volume) =
      ∫ z in Metric.ball center δ, f z ∂volume.prod volume := by
  apply thirdFullPairEven_integral_reflected_sets244 f hf
    (Metric.ball center δ) (Metric.ball (-center) δ)
    measurableSet_ball measurableSet_ball
  intro z
  change dist (-z) (-center) < δ ↔ dist z center < δ
  rw [dist_neg_neg]

/-- The same exact pairing for CLOSED frequency balls. This is convenient
when a later sign proof works with compact rather than open domains. -/
theorem thirdFullPairEven_integral_reflected_closedBall244
    (f : PairV244 → ℝ)
    (hf : ∀ z : PairV244, f (-z.1, -z.2) = f z)
    (center : PairV244) (δ : ℝ) :
    (∫ z in Metric.closedBall (-center) δ, f z ∂volume.prod volume) =
      ∫ z in Metric.closedBall center δ, f z ∂volume.prod volume := by
  apply thirdFullPairEven_integral_reflected_sets244 f hf
    (Metric.closedBall center δ) (Metric.closedBall (-center) δ)
    measurableSet_closedBall measurableSet_closedBall
  intro z
  change dist (-z) (-center) ≤ δ ↔ dist z center ≤ δ
  rw [dist_neg_neg]

/-- The unphased imaginary kernel satisfies the generic pointwise symmetry
because the physical Fourier coefficient was built from a REAL field. -/
theorem thirdFullAxisImaginaryKernel_even244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (z : PairV244) :
    (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C
      (-z.1, -z.2)).im =
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im :=
  thirdFullAxisRealThirdUnphasedImag_reflect244 ρ hρ A B C z

/-- The actual unphased imaginary physical H3 kernel contributes equally
on any two Hermitian-reflected open momentum-pair balls. -/
theorem thirdFullAxisImaginaryKernel_integral_reflected_ball244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (center : PairV244) (δ : ℝ) :
    (∫ z in Metric.ball (-center) δ,
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume) =
    ∫ z in Metric.ball center δ,
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume := by
  exact thirdFullPairEven_integral_reflected_ball244
    (fun z => (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im)
    (thirdFullAxisImaginaryKernel_even244 ρ hρ A B C) center δ

/-- The same local physical Fourier identity on two compact balls. -/
theorem thirdFullAxisImaginaryKernel_integral_reflected_closedBall244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (center : PairV244) (δ : ℝ) :
    (∫ z in Metric.closedBall (-center) δ,
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume) =
    ∫ z in Metric.closedBall center δ,
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume := by
  exact thirdFullPairEven_integral_reflected_closedBall244
    (fun z => (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im)
    (thirdFullAxisImaginaryKernel_even244 ρ hρ A B C) center δ

/-- Ordered pair of sharp positive Fourier centers for each of the SIX
coherent positive orientations, embedded in the genuine Hilbert carrier. -/
def thirdFullPositiveCoherentPair244 (n : Fin 6) : PairV244 :=
  (WithLp.toLp 2
      (thirdFullAxisSixCenter244
        (lowNormalQuarterCoherentLabelPair false n).1),
   WithLp.toLp 2
      (thirdFullAxisSixCenter244
        (lowNormalQuarterCoherentLabelPair false n).2))

/-- The six positively oriented open-ball integrals of the ACTUAL kernel.
Their sum is a labelled local sum, not yet the global Fourier integral. -/
noncomputable def thirdFullPositiveSixBallIntegral244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (δ : ℝ) : ℝ :=
  ∑ n : Fin 6,
    ∫ z in Metric.ball (thirdFullPositiveCoherentPair244 n) δ,
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume

/-- All twelve labelled positive+reflected open-ball contributions,
without presuming that the twelve balls are disjoint. -/
noncomputable def thirdFullTwelvePairedBallIntegral244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (δ : ℝ) : ℝ :=
  ∑ n : Fin 6,
    ((∫ z in Metric.ball (thirdFullPositiveCoherentPair244 n) δ,
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume) +
     (∫ z in Metric.ball (-(thirdFullPositiveCoherentPair244 n)) δ,
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume))

/-- EXACT SIX-ORIENTATION REDUCTION of the twelve LABELLED ball integrals.
The sign of the six-ball sum determines that of the twelve-ball sum.
No disjointness/coverage assumption is silently inferred. -/
theorem thirdFullTwelvePairedBallIntegral_eq_twice_six244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (δ : ℝ) :
    thirdFullTwelvePairedBallIntegral244 ρ hρ A B C δ =
      2 * thirdFullPositiveSixBallIntegral244 ρ hρ A B C δ := by
  unfold thirdFullTwelvePairedBallIntegral244
    thirdFullPositiveSixBallIntegral244
  calc
    (∑ n : Fin 6,
      ((∫ z in Metric.ball (thirdFullPositiveCoherentPair244 n) δ,
        (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
          ∂volume.prod volume) +
       (∫ z in Metric.ball (-(thirdFullPositiveCoherentPair244 n)) δ,
        (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
          ∂volume.prod volume))) =
      ∑ n : Fin 6, 2 *
        (∫ z in Metric.ball (thirdFullPositiveCoherentPair244 n) δ,
          (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
            ∂volume.prod volume) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [thirdFullAxisImaginaryKernel_integral_reflected_ball244]
        ring
    _ = _ := by rw [Finset.mul_sum]

/-- A strict sign of the six labelled local integrals transfers to the
twelve paired local integrals, with NO pointwise sign hypothesis. -/
theorem thirdFullTwelvePairedBallIntegral_neg_iff_six244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (δ : ℝ) :
    thirdFullTwelvePairedBallIntegral244 ρ hρ A B C δ < 0 ↔
      thirdFullPositiveSixBallIntegral244 ρ hρ A B C δ < 0 := by
  rw [thirdFullTwelvePairedBallIntegral_eq_twice_six244]
  constructor
  · intro h
    by_contra hn
    have hp : 0 ≤ thirdFullPositiveSixBallIntegral244 ρ hρ A B C δ :=
      le_of_not_gt hn
    exact (not_lt_of_ge (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp)) h
  · intro h
    exact mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 2) h

end
end PrimeTensor.FirstMonomialTriad
