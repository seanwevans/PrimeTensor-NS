import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientPairModulus244
import Mathlib.Tactic

/-!
# All 243 physical five-axis gradient slots: spectral H³ two-profile modulus

The physical 3+3+1 top gradient consists of 243 four-term axis blocks.
The earlier two-profile estimate handled only ONE 3+3+1 product.
This file proves the exact finite-sum perturbation inequality for ALL four
third-order gradient products in each physical five-axis slot and then across
all 243 slots, preserving signs and the physical factor two.

The right-hand side is a concrete nonnegative spectral-pair error: third
Schwartz jets enter in their actual L² square-root norms, first derivatives
in the weighted H³ C¹ evaluation estimate. The two profiles need not be
Schwartz approximations of each other or of a Schwartz target.

A final theorem constructs a real gradient-channel limit as soon as this
explicit finite scalar error becomes Cauchy-small for a synchronized family.
Deriving that vanishing from the existing E₃ energy Cauchy theorem and H³
spectral convergence is a separate last analytic step; it is not assumed
as an identification with the independently defined physical transport.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev Slot5 := A3 × (A3 × (A3 × (A3 × A3)))

noncomputable local instance axisFintypeGradientFinitePair244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

private abbrev gradientPairThird244 (f : A3 → SchwartzMap V3 ℝ)
    (j i k l : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection k}
      (∂_{h3FourierAxisDirection l} (f j)))

/-- The actual sharp two-profile spectral bound on ONE Schwartz gradient
triple, with its factor 2 and all three separately controlled differences. -/
noncomputable def fullGradientTripleSpectralPairEnvelope244
    (a b a' b' : SchwartzMap V3 ℝ)
    (F G : H3SpectralScalarState) : ℝ :=
  let C := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  2 * ((C * ‖F‖) *
          (schwartzIntegralL2Root244 (a - a') *
            schwartzIntegralL2Root244 b) +
       (C * ‖F‖) *
          (schwartzIntegralL2Root244 a' *
            schwartzIntegralL2Root244 (b - b')) +
       (C * ‖F - G‖) *
          (schwartzIntegralL2Root244 a' *
            schwartzIntegralL2Root244 b'))

/-- Each spectral triple error is nonnegative, including zero states. -/
theorem fullGradientTripleSpectralPairEnvelope_nonneg244
    (a b a' b' : SchwartzMap V3 ℝ)
    (F G : H3SpectralScalarState) :
    0 ≤ fullGradientTripleSpectralPairEnvelope244 a b a' b' F G := by
  have hC : 0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  have hA := schwartzIntegralL2Root244_nonneg (a - a')
  have hB := schwartzIntegralL2Root244_nonneg b
  have hA' := schwartzIntegralL2Root244_nonneg a'
  have hB' := schwartzIntegralL2Root244_nonneg (b - b')
  have hBB' := schwartzIntegralL2Root244_nonneg b'
  unfold fullGradientTripleSpectralPairEnvelope244
  dsimp only
  positivity

/-- One physical 3+3+1 gradient-axis error: every indexed term retains its
own third-jet L² differences and the correct first-gradient component. -/
noncomputable def fullGradientAxisSpectralPairEnvelope244
    (f g : A3 → SchwartzMap V3 ℝ)
    (U W : H3SpectralVelocityState)
    (j i k l r : A3) : ℝ :=
  fullGradientTripleSpectralPairEnvelope244
    (gradientPairThird244 f j i k l)
    (gradientPairThird244 f r i k l)
    (gradientPairThird244 g j i k l)
    (gradientPairThird244 g r i k l)
    (U (h3ClassicalizationFinOfAxis j))
    (W (h3ClassicalizationFinOfAxis j)) +
  fullGradientTripleSpectralPairEnvelope244
    (gradientPairThird244 f j i k l)
    (gradientPairThird244 f j i k r)
    (gradientPairThird244 g j i k l)
    (gradientPairThird244 g j i k r)
    (U (h3ClassicalizationFinOfAxis r))
    (W (h3ClassicalizationFinOfAxis r)) +
  fullGradientTripleSpectralPairEnvelope244
    (gradientPairThird244 f j i k l)
    (gradientPairThird244 f j i r l)
    (gradientPairThird244 g j i k l)
    (gradientPairThird244 g j i r l)
    (U (h3ClassicalizationFinOfAxis r))
    (W (h3ClassicalizationFinOfAxis r)) +
  fullGradientTripleSpectralPairEnvelope244
    (gradientPairThird244 f j i k l)
    (gradientPairThird244 f j r k l)
    (gradientPairThird244 g j i k l)
    (gradientPairThird244 g j r k l)
    (U (h3ClassicalizationFinOfAxis r))
    (W (h3ClassicalizationFinOfAxis r))

/-- Four-summand absolute difference inequality, without positivity
hypotheses; it preserves all four signs before taking the absolute value. -/
private theorem four_signed_abs_sub_le_sum244
    (a b c d a' b' c' d' : ℝ) :
    |(a + b + c + d) - (a' + b' + c' + d')| ≤
      |a - a'| + |b - b'| + |c - c'| + |d - d'| := by
  have hEq :
      (a + b + c + d) - (a' + b' + c' + d') =
        ((a - a') + (b - b')) + ((c - c') + (d - d')) := by
    ring
  rw [hEq]
  calc
    |((a - a') + (b - b')) + ((c - c') + (d - d'))| ≤
        |(a - a') + (b - b')| + |(c - c') + (d - d')| :=
          abs_add_le _ _
    _ ≤ (|a - a'| + |b - b'|) +
          (|c - c'| + |d - d'|) :=
          add_le_add (abs_add_le _ _) (abs_add_le _ _)
    _ = _ := by ring

/-- ALL FOUR terms of one signed physical gradient block obey the sharp
sum of spectral two-profile errors. No physical Schwartz target is assumed. -/
theorem fullSchwartzGradientAxis_spectralPair_modulus244
    (f g : A3 → SchwartzMap V3 ℝ)
    (U W : H3SpectralVelocityState)
    (hf : ∀ j : A3,
      h3SchwartzPoint3Scalar (f j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (U (h3ClassicalizationFinOfAxis j)))
    (hg : ∀ j : A3,
      h3SchwartzPoint3Scalar (g j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (W (h3ClassicalizationFinOfAxis j)))
    (j i k l r : A3) :
    |fullSchwartzGradientAxis244 f j i k l r -
       fullSchwartzGradientAxis244 g j i k l r| ≤
      fullGradientAxisSpectralPairEnvelope244 f g U W j i k l r := by
  let A : ℝ := fullGradientTriple244
    (gradientPairThird244 f j i k l) (gradientPairThird244 f r i k l)
    (∂_{h3FourierAxisDirection r} (f j))
  let B : ℝ := fullGradientTriple244
    (gradientPairThird244 f j i k l) (gradientPairThird244 f j i k r)
    (∂_{h3FourierAxisDirection l} (f r))
  let C : ℝ := fullGradientTriple244
    (gradientPairThird244 f j i k l) (gradientPairThird244 f j i r l)
    (∂_{h3FourierAxisDirection k} (f r))
  let D : ℝ := fullGradientTriple244
    (gradientPairThird244 f j i k l) (gradientPairThird244 f j r k l)
    (∂_{h3FourierAxisDirection i} (f r))
  let A' : ℝ := fullGradientTriple244
    (gradientPairThird244 g j i k l) (gradientPairThird244 g r i k l)
    (∂_{h3FourierAxisDirection r} (g j))
  let B' : ℝ := fullGradientTriple244
    (gradientPairThird244 g j i k l) (gradientPairThird244 g j i k r)
    (∂_{h3FourierAxisDirection l} (g r))
  let C' : ℝ := fullGradientTriple244
    (gradientPairThird244 g j i k l) (gradientPairThird244 g j i r l)
    (∂_{h3FourierAxisDirection k} (g r))
  let D' : ℝ := fullGradientTriple244
    (gradientPairThird244 g j i k l) (gradientPairThird244 g j r k l)
    (∂_{h3FourierAxisDirection i} (g r))
  let EA : ℝ := fullGradientTripleSpectralPairEnvelope244
    (gradientPairThird244 f j i k l) (gradientPairThird244 f r i k l)
    (gradientPairThird244 g j i k l) (gradientPairThird244 g r i k l)
    (U (h3ClassicalizationFinOfAxis j))
    (W (h3ClassicalizationFinOfAxis j))
  let EB : ℝ := fullGradientTripleSpectralPairEnvelope244
    (gradientPairThird244 f j i k l) (gradientPairThird244 f j i k r)
    (gradientPairThird244 g j i k l) (gradientPairThird244 g j i k r)
    (U (h3ClassicalizationFinOfAxis r))
    (W (h3ClassicalizationFinOfAxis r))
  let EC : ℝ := fullGradientTripleSpectralPairEnvelope244
    (gradientPairThird244 f j i k l) (gradientPairThird244 f j i r l)
    (gradientPairThird244 g j i k l) (gradientPairThird244 g j i r l)
    (U (h3ClassicalizationFinOfAxis r))
    (W (h3ClassicalizationFinOfAxis r))
  let ED : ℝ := fullGradientTripleSpectralPairEnvelope244
    (gradientPairThird244 f j i k l) (gradientPairThird244 f j r k l)
    (gradientPairThird244 g j i k l) (gradientPairThird244 g j r k l)
    (U (h3ClassicalizationFinOfAxis r))
    (W (h3ClassicalizationFinOfAxis r))
  have hA : |A - A'| ≤ EA := by
    exact fullGradientTriple_spectralMatchedPair_modulus244
      (gradientPairThird244 f j i k l) (gradientPairThird244 f r i k l)
      (gradientPairThird244 g j i k l) (gradientPairThird244 g r i k l)
      (f j) (g j) (U (h3ClassicalizationFinOfAxis j))
      (W (h3ClassicalizationFinOfAxis j)) (hf j) (hg j) r
  have hB : |B - B'| ≤ EB := by
    exact fullGradientTriple_spectralMatchedPair_modulus244
      (gradientPairThird244 f j i k l) (gradientPairThird244 f j i k r)
      (gradientPairThird244 g j i k l) (gradientPairThird244 g j i k r)
      (f r) (g r) (U (h3ClassicalizationFinOfAxis r))
      (W (h3ClassicalizationFinOfAxis r)) (hf r) (hg r) l
  have hC : |C - C'| ≤ EC := by
    exact fullGradientTriple_spectralMatchedPair_modulus244
      (gradientPairThird244 f j i k l) (gradientPairThird244 f j i r l)
      (gradientPairThird244 g j i k l) (gradientPairThird244 g j i r l)
      (f r) (g r) (U (h3ClassicalizationFinOfAxis r))
      (W (h3ClassicalizationFinOfAxis r)) (hf r) (hg r) k
  have hD : |D - D'| ≤ ED := by
    exact fullGradientTriple_spectralMatchedPair_modulus244
      (gradientPairThird244 f j i k l) (gradientPairThird244 f j r k l)
      (gradientPairThird244 g j i k l) (gradientPairThird244 g j r k l)
      (f r) (g r) (U (h3ClassicalizationFinOfAxis r))
      (W (h3ClassicalizationFinOfAxis r)) (hf r) (hg r) i
  change |(A + B + C + D) - (A' + B' + C' + D')| ≤ EA + EB + EC + ED
  calc
    _ ≤ |A - A'| + |B - B'| + |C - C'| + |D - D'| :=
      four_signed_abs_sub_le_sum244 A B C D A' B' C' D'
    _ ≤ EA + EB + EC + ED := by linarith only [hA, hB, hC, hD]

/-- The complete 243-slot spectral perturbation envelope, with FOUR
separately tracked 3+3+1 triples in each axis block. -/
noncomputable def fullSchwartzGradientSpectralPairEnvelope244
    (f g : A3 → SchwartzMap V3 ℝ)
    (U W : H3SpectralVelocityState) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
    fullGradientAxisSpectralPairEnvelope244 f g U W j i k l r

/-- The complete physical signed gradient is locally Lipschitz under the
explicit sum of 972 (4×243) natural 2–2–infinity error envelopes.
Neither input is assumed to be the fixed nonschwartz physical target. -/
theorem fullSchwartzGradientTransport_spectralPair_modulus244
    (f g : A3 → SchwartzMap V3 ℝ)
    (U W : H3SpectralVelocityState)
    (hf : ∀ j : A3,
      h3SchwartzPoint3Scalar (f j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (U (h3ClassicalizationFinOfAxis j)))
    (hg : ∀ j : A3,
      h3SchwartzPoint3Scalar (g j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (W (h3ClassicalizationFinOfAxis j))) :
    |fullSchwartzGradientTransport244 f -
       fullSchwartzGradientTransport244 g| ≤
      fullSchwartzGradientSpectralPairEnvelope244 f g U W := by
  classical
  let X : Slot5 → ℝ := fun p =>
    fullSchwartzGradientAxis244 f
      p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  let Y : Slot5 → ℝ := fun p =>
    fullSchwartzGradientAxis244 g
      p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  let E : Slot5 → ℝ := fun p =>
    fullGradientAxisSpectralPairEnvelope244 f g U W
      p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  have hIndex : |(∑ p : Slot5, X p) - (∑ p : Slot5, Y p)| ≤
      ∑ p : Slot5, E p := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ p : Slot5, (X p - Y p)| ≤
          ∑ p : Slot5, |X p - Y p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : Slot5, E p := by
        apply Finset.sum_le_sum
        intro p _
        exact fullSchwartzGradientAxis_spectralPair_modulus244
          f g U W hf hg p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  simpa only [Fintype.sum_prod_type, X, Y, E,
    fullSchwartzGradientTransport244,
    fullSchwartzGradientSpectralPairEnvelope244] using hIndex

/-- If the explicit 972-term spectral perturbation gauge is Cauchy-small
on one decoder-matched Schwartz sequence, its entire 3+3+1 gradient channel
has a real limit. Importantly, the gauge is NOT the desired transport limit;
its vanishing remains an explicit analytic premise here. -/
theorem exists_fullSchwartzGradientTransport_limit_of_spectralPairGauge244
    (V : ℕ → H3SpectralVelocityState)
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hMatch : ∀ n j,
      h3SchwartzPoint3Scalar (f n j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (V n (h3ClassicalizationFinOfAxis j)))
    (hGauge : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
        fullSchwartzGradientSpectralPairEnvelope244
          (f m) (f n) (V m) (V n) < ε) :
    ∃ L : ℝ, Tendsto
      (fun n => fullSchwartzGradientTransport244 (f n))
        atTop (𝓝 L) := by
  have hCauchy : CauchySeq
      (fun n => fullSchwartzGradientTransport244 (f n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hGauge ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    rw [Real.dist_eq]
    exact lt_of_le_of_lt
      (fullSchwartzGradientTransport_spectralPair_modulus244
        (f m) (f n) (V m) (V n) (hMatch m) (hMatch n))
      (hN m hm n hn)
  exact cauchySeq_tendsto_of_complete hCauchy

end
end PrimeTensor.FirstMonomialTriad
