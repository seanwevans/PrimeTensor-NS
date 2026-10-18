import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdCoherentHermitianPhase244
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-!
# Strict sign of an actually window-weighted full-third Hermitian local integral

The projected full-third coefficient was negative on a six-dimensional open
momentum tube, while later files supplied genuine compact smooth windows,
excluded noncoherent triple supports, and closed reflected phase algebra.
Here those windows enter the integrand itself. We show that the *weighted*
coherent coefficient is continuous and strictly negative at the sharp center,
then integrate on a positive-measure closed pair ball.

The conclusion is a real, window-weighted, nonzero local integral. It is NOT
an identity for the Fourier transform of a globally assembled Hermitian
Schwartz velocity, and it does not claim noncancellation of the complete
sum over all coherent sectors.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set Filter PrimeTensor.Bridge.Euclidean
open scoped Topology BigOperators

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Pair244 := (A3 → ℝ) × (A3 → ℝ)

noncomputable local instance axisFintypeWindowedLocal244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Continuity of the full labelled kernel, including all three actual smooth
cutoffs, two free momentum variables, and moving solenoidal projections. -/
theorem thirdFullLabelledWindowedProjectedKernel_continuous244
    (ρ : ℝ) (hρ : 0 < ρ) (i j k : Fin 6)
    (p₀ q₀ r₀ A B C : A3 → ℝ) :
    Continuous (thirdFullLabelledWindowedProjectedKernel_coherent244
      ρ hρ i j k p₀ q₀ r₀ A B C) := by
  have hp : Continuous (fun z : Pair244 =>
      (thirdFullAxisWindowBump244 ρ hρ i : (A3 → ℝ) → ℝ) z.1) :=
    (thirdFullAxisWindowBump_contDiff244 ρ hρ i).continuous.comp continuous_fst
  have hq : Continuous (fun z : Pair244 =>
      (thirdFullAxisWindowBump244 ρ hρ j : (A3 → ℝ) → ℝ)
        (thirdFullMiddleFrequency244 z)) :=
    (thirdFullAxisWindowBump_contDiff244 ρ hρ j).continuous.comp
      thirdFullMiddleFrequency_continuous244
  have hr : Continuous (fun z : Pair244 =>
      (thirdFullAxisWindowBump244 ρ hρ k : (A3 → ℝ) → ℝ) z.2) :=
    (thirdFullAxisWindowBump_contDiff244 ρ hρ k).continuous.comp continuous_snd
  exact ((hp.mul hq).mul hr).mul
    (thirdFullProjectedHermitianKernel_continuous244 p₀ q₀ r₀ A B C)

/-- At the coherent center, the three smooth cutoffs equal exactly one,
so no amplitude damping or sign changes enter the -192 center coefficient. -/
theorem thirdFullLabelledWindowedProjectedKernel_at_centers244
    (ρ : ℝ) (hρ : 0 < ρ) (i j k : Fin 6)
    (p q r A B C : A3 → ℝ)
    (hp : p = thirdFullAxisSixCenter244 i)
    (hq : q = thirdFullAxisSixCenter244 j)
    (hr : r = thirdFullAxisSixCenter244 k)
    (hm : ∀ a, p a + q a + r a = 0) :
    thirdFullLabelledWindowedProjectedKernel_coherent244
      ρ hρ i j k p q r A B C (p,r) =
      thirdFullProjectedHermitianKernel244 p q r A B C (p,r) := by
  have hMiddle : thirdFullMiddleFrequency244 (p,r) = q := by
    funext a
    dsimp [thirdFullMiddleFrequency244]
    linarith [hm a]
  have hwp :
      (thirdFullAxisWindowBump244 ρ hρ i : (A3 → ℝ) → ℝ) p = 1 := by
    rw [hp]
    exact thirdFullAxisWindowBump_at_center244 ρ hρ i
  have hwq :
      (thirdFullAxisWindowBump244 ρ hρ j : (A3 → ℝ) → ℝ) q = 1 := by
    rw [hq]
    exact thirdFullAxisWindowBump_at_center244 ρ hρ j
  have hwr :
      (thirdFullAxisWindowBump244 ρ hρ k : (A3 → ℝ) → ℝ) r = 1 := by
    rw [hr]
    exact thirdFullAxisWindowBump_at_center244 ρ hρ k
  unfold thirdFullLabelledWindowedProjectedKernel_coherent244
  rw [hMiddle, hwp, hwq, hwr]
  ring

/-- An arbitrary continuous strictly negative function on a closed
positive-radius ball has a strictly negative integral over that ball,
provided the carrier is the usual six-dimensional product volume. -/
private theorem thirdFullContinuousNegativeOnBall_integral244
    (F : Pair244 → ℝ) (hF : Continuous F)
    (z₀ : Pair244) (ε : ℝ) (hε : 0 < ε)
    (hNeg : ∀ z ∈ Metric.closedBall z₀ ε, F z < 0) :
    (∫ z in Metric.closedBall z₀ ε, F z ∂(volume.prod volume)) < 0 := by
  let s : Set Pair244 := Metric.closedBall z₀ ε
  have hCompact : IsCompact s := isCompact_closedBall _ _
  have hMeas : MeasurableSet s := measurableSet_closedBall
  have hInt : IntegrableOn (fun z => -F z) s (volume.prod volume) :=
    hF.neg.continuousOn.integrableOn_compact hCompact
  have hNonneg : 0 ≤ᵐ[(volume.prod volume).restrict s] (fun z => -F z) := by
    filter_upwards [ae_restrict_mem hMeas] with z hz
    exact (neg_pos.mpr (hNeg z hz)).le
  have hBall : Metric.ball z₀ ε ⊆ Function.support (fun z => -F z) ∩ s := by
    intro z hz
    constructor
    · change -F z ≠ 0
      exact ne_of_gt (neg_pos.mpr (hNeg z (Metric.ball_subset_closedBall hz)))
    · exact Metric.ball_subset_closedBall hz
  have hMeasure :
      0 < (volume.prod volume) (Function.support (fun z => -F z) ∩ s) :=
    (Metric.measure_ball_pos (volume.prod volume) z₀ hε).trans_le
      (measure_mono hBall)
  have hIntegral : 0 < ∫ z in s, -F z ∂(volume.prod volume) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hMeasure
  simp only [integral_neg] at hIntegral
  change (∫ z in s, F z ∂(volume.prod volume)) < 0
  exact neg_pos.mp hIntegral

/-- General local signed-integral principle for the ACTUAL labelled windows.
The hypotheses are concrete center matching and the projected Hermitian
coefficient's negative center sign; continuity produces the integral radius. -/
theorem thirdFullLabelledWindowedProjectedKernel_exists_negative_local_integral244
    (ρ : ℝ) (hρ : 0 < ρ) (i j k : Fin 6)
    (p q r A B C : A3 → ℝ)
    (hp : p = thirdFullAxisSixCenter244 i)
    (hq : q = thirdFullAxisSixCenter244 j)
    (hr : r = thirdFullAxisSixCenter244 k)
    (hm : ∀ a, p a + q a + r a = 0)
    (hNeg : thirdFullProjectedHermitianKernel244 p q r A B C (p,r) < 0) :
    ∃ ε : ℝ, 0 < ε ∧
      (∫ z in Metric.closedBall (p,r) ε,
        thirdFullLabelledWindowedProjectedKernel_coherent244
          ρ hρ i j k p q r A B C z ∂(volume.prod volume)) < 0 := by
  let F : Pair244 → ℝ :=
    thirdFullLabelledWindowedProjectedKernel_coherent244
      ρ hρ i j k p q r A B C
  have hCont : Continuous F :=
    thirdFullLabelledWindowedProjectedKernel_continuous244
      ρ hρ i j k p q r A B C
  have hAt : F (p,r) < 0 := by
    change thirdFullLabelledWindowedProjectedKernel_coherent244
      ρ hρ i j k p q r A B C (p,r) < 0
    rw [thirdFullLabelledWindowedProjectedKernel_at_centers244
      ρ hρ i j k p q r A B C hp hq hr hm]
    exact hNeg
  have hOpen : IsOpen {z : Pair244 | F z < 0} :=
    isOpen_lt hCont continuous_const
  obtain ⟨δ, hδ, hSub⟩ := Metric.mem_nhds_iff.mp
    (hOpen.mem_nhds hAt)
  have hNegBall : ∀ z ∈ Metric.closedBall (p,r) (δ / 2), F z < 0 := by
    intro z hz
    exact hSub (Metric.closedBall_subset_ball (half_lt_self hδ) hz)
  exact ⟨δ / 2, half_pos hδ,
    thirdFullContinuousNegativeOnBall_integral244 F hCont (p,r)
      (δ / 2) (half_pos hδ) hNegBall⟩


/-- The explicit full-third sharp center triple is exactly the first three
centers of the six-window axis geometry. -/
private theorem thirdFullAxisFirstThreeCenters_explicit244 :
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
    -- Normalize the integer lattice coordinate arithmetic in each branch.
    -- In particular, the r center has -1 + -1 = -2 at rank zero.
    simp [thirdFullAxisSixCenter244, lowNormalSixCenter,
      lowNormalLatticeEmbedding, lowNormalSignedLatticeCenter] <;>
      split_ifs <;> norm_num

/-- Unconditional strictly negative LOCAL Fourier integral with three
actual smooth compact windows and exact frequency-transverse polarizations.
This is a six-dimensional integral, not a coefficient evaluated at one triad.
The local domain intentionally does not include the other coherent sectors. -/
theorem thirdFullLabelledWindowedProjectedKernel_exists_concrete_negative_integral244
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (p q r A B C : A3 → ℝ) (ε : ℝ),
      p = thirdFullAxisSixCenter244 0 ∧
      q = thirdFullAxisSixCenter244 1 ∧
      r = thirdFullAxisSixCenter244 2 ∧
      0 < ε ∧
      (∫ z in Metric.closedBall (p,r) ε,
        thirdFullLabelledWindowedProjectedKernel_coherent244
          ρ hρ 0 1 2 p q r A B C z ∂(volume.prod volume)) < 0 := by
  let coord (x y z : ℝ) (a : A3) : ℝ :=
    if axisRank a = 0 then x else if axisRank a = 1 then y else z
  let p : A3 → ℝ := coord 1 0 0
  let q : A3 → ℝ := coord 1 1 0
  let r : A3 → ℝ := coord (-2) (-1) 0
  let A : A3 → ℝ := coord 0 1 0
  let B : A3 → ℝ := coord 1 (-1) 0
  let C : A3 → ℝ := coord 1 (-2) 0
  have hCenters :
      p = thirdFullAxisSixCenter244 0 ∧
      q = thirdFullAxisSixCenter244 1 ∧
      r = thirdFullAxisSixCenter244 2 := by
    obtain ⟨h0, h1, h2⟩ := thirdFullAxisFirstThreeCenters_explicit244
    refine ⟨?_, h1.symm, h2.symm⟩
    rw [h0]
    funext a
    simp [p, coord]
  have hTriad :
      (∀ a, p a + q a + r a = 0) ∧
      thirdTriadAxisDot244 A p = 0 ∧
      thirdTriadAxisDot244 B q = 0 ∧
      thirdTriadAxisDot244 C r = 0 := by
    exact thirdFullPhysicalTriad_solenoidal244
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
  have hNeg : thirdFullProjectedHermitianKernel244 p q r A B C (p,r) < 0 := by
    rw [thirdFullProjectedHermitianKernel_at_center244 p q r A B C
      hTriad.1 hTriad.2.1 hTriad.2.2.1 hTriad.2.2.2 hp hq hr,
      hValue]
    norm_num
  obtain ⟨ε, hε, hInt⟩ :=
    thirdFullLabelledWindowedProjectedKernel_exists_negative_local_integral244
      ρ hρ 0 1 2 p q r A B C
      hCenters.1 hCenters.2.1 hCenters.2.2 hTriad.1 hNeg
  exact ⟨p, q, r, A, B, C, ε,
    hCenters.1, hCenters.2.1, hCenters.2.2, hε, hInt⟩

end
end PrimeTensor.FirstMonomialTriad
