import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSharpGradientCoreBridge244
import Mathlib.Tactic

/-!
# Physical seven-derivative weight and a separated five-index contraction

The true full-third H3 gradient has five independent physical axis sums.
This module reduces the original complex seven-derivative weight to real
momentum coordinates, with no change of Fourier normalization, and proves
an abstract five-index separation lemma over the actual Axis Depth.three.

The four exact index patterns are retained as an explicitly separated real
coordinate polynomial. No substitution of the old sharp six-order symbol
for a single physical gradient slot is allowed here. The last analytic
step is to identify the coordinate polynomial with the corrected ordered
symbol after taking all five sums, and then specialize the six sharp centers.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev PairV244 := H3FourierPoint3 × H3FourierPoint3

noncomputable local instance axisFintypeSharpContraction244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The real part of the *actual* seven-Fourier-derivative weight, expressed
through its seven literal physical-axis coordinates. This uses the Hilbert
inner-product identification; no surrogate frequency multiplier enters. -/
theorem thirdFullSharpSevenWeight_coordinates244
    (z : PairV244) (a b c d e k v : A3) :
    (thirdFullGradientSevenWeight244
      (h3FourierAxisDirection a) (h3FourierAxisDirection b)
      (h3FourierAxisDirection c) (h3FourierAxisDirection d)
      (h3FourierAxisDirection e) (h3FourierAxisDirection k)
      (h3FourierAxisDirection v) z).re =
      (((WithLp.ofLp z.1 : Freq244) a *
        (WithLp.ofLp z.1 : Freq244) b *
        (WithLp.ofLp z.1 : Freq244) c) *
       ((WithLp.ofLp (-(z.1 + z.2)) : Freq244) d *
        (WithLp.ofLp (-(z.1 + z.2)) : Freq244) e *
        (WithLp.ofLp (-(z.1 + z.2)) : Freq244) k)) *
      (WithLp.ofLp z.2 : Freq244) v := by
  simp [thirdFullGradientSevenWeight244, inner_h3FourierAxisDirection]

/-- One exact five-index real coordinate block with the ORIGINAL four
physical gradient slots. The distinguished velocity index is j, and
(i,k,l,t) are the four other physical derivative axes. -/
noncomputable def thirdFullSharpFiveCoordinateAxis244
    (p q r U V W : Freq244) (j i k l t : A3) : ℝ :=
  2 * (((
    (((p i * p k * p l) * (q i * q k * q l)) * r t) *
      ((U j * V t) * W j) +
    (((p i * p k * p l) * (q i * q k * q t)) * r l) *
      ((U j * V j) * W t)) +
    (((p i * p k * p l) * (q i * q t * q l)) * r k) *
      ((U j * V j) * W t)) +
    (((p i * p k * p l) * (q t * q k * q l)) * r i) *
      ((U j * V j) * W t))

/-- The genuine four-gradient physical axis block equals the real seven-
derivative coordinate polynomial before ANY of the five sums are taken. -/
theorem thirdFullSharpGradientAxis_eq_coordinates244
    (z : PairV244) (j i k l t : A3) (U V W : Freq244) :
    thirdFullSharpPhysicalGradientAxis244 z U V W j i k l t =
      thirdFullSharpFiveCoordinateAxis244
        (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2)))
        (WithLp.ofLp z.2) U V W j i k l t := by
  unfold thirdFullSharpPhysicalGradientAxis244
    thirdFullSharpFiveCoordinateAxis244
  dsimp only
  simp only [thirdFullSharpSevenWeight_coordinates244]

/-- Five-fold coordinate sum of the real, original four-pattern polynomial. -/
noncomputable def thirdFullSharpFiveCoordinateTotal244
    (p q r U V W : Freq244) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ t : A3,
    thirdFullSharpFiveCoordinateAxis244 p q r U V W j i k l t

/-- Transfer the exact physical Hilbert seven-derivative multiplier to the
coordinate form THROUGH all five independent physical index sums. -/
theorem thirdFullSharpGradientFive_eq_coordinate_total244
    (z : PairV244) (U V W : Freq244) :
    thirdFullSharpPhysicalGradientFive244 z U V W =
      thirdFullSharpFiveCoordinateTotal244
        (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2)))
        (WithLp.ofLp z.2) U V W := by
  unfold thirdFullSharpPhysicalGradientFive244
    thirdFullSharpFiveCoordinateTotal244
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro t _
  exact thirdFullSharpGradientAxis_eq_coordinates244 z j i k l t U V W

/-- A reusable algebraic identity on the *actual* finite physical axes:
each independent axis sum separates into its own scalar contraction. -/
theorem thirdFullSharpFiveIndependentSums244
    (f g h u v : Freq244) :
    (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ t : A3,
      f j * g i * h k * u l * v t) =
      (∑ j : A3, f j) * (∑ i : A3, g i) *
        (∑ k : A3, h k) * (∑ l : A3, u l) *
        (∑ t : A3, v t) := by
  -- Distribute each outer coordinate factor into its *own* inner sum.
  -- Expanding both sides indiscriminately would reorder bound indices and
  -- leave an invalid pointwise comparison of differently indexed terms.
  calc
    _ = ∑ j : A3, f j *
          (∑ i : A3, g i *
            (∑ k : A3, h k *
              (∑ l : A3, u l * (∑ t : A3, v t)))) := by
          simp only [Finset.mul_sum, mul_assoc]
    _ = (∑ j : A3, f j) *
          ((∑ i : A3, g i) *
            ((∑ k : A3, h k) *
              ((∑ l : A3, u l) * (∑ t : A3, v t)))) := by
          simp only [Finset.sum_mul]
    _ = _ := by ring


/-- The real coordinate pairing is symmetric; this is needed only to
match the convention used by the corrected ordered physical symbol. -/
private theorem thirdFullSharpDot_comm244 (a b : Freq244) :
    dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The four real physical gradient slots factor into two kinds of exact
bilinear contractions after all five spatial sums: one U-W and three U-V.
This is a polynomial theorem for *arbitrary* momenta and polarizations. -/
theorem thirdFullSharpFiveCoordinateTotal_contract244
    (p q r U V W : Freq244) :
    thirdFullSharpFiveCoordinateTotal244 p q r U V W =
      2 * ((dot U W * dot V r) * (dot p q) ^ 3 +
        3 * ((dot U V * dot W q) * (dot p q) ^ 2 * dot p r)) := by
  let f1 : A3 → A3 → A3 → A3 → A3 → ℝ :=
    fun j i k l t =>
      (U j * W j) * (p i * q i) * (p k * q k) *
        (p l * q l) * (r t * V t)
  let f2 : A3 → A3 → A3 → A3 → A3 → ℝ :=
    fun j i k l t =>
      (U j * V j) * (p i * q i) * (p k * q k) *
        (p l * r l) * (q t * W t)
  let f3 : A3 → A3 → A3 → A3 → A3 → ℝ :=
    fun j i k l t =>
      (U j * V j) * (p i * q i) * (p k * r k) *
        (p l * q l) * (q t * W t)
  let f4 : A3 → A3 → A3 → A3 → A3 → ℝ :=
    fun j i k l t =>
      (U j * V j) * (p i * r i) * (p k * q k) *
        (p l * q l) * (q t * W t)
  have h1 :
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ t : A3,
        f1 j i k l t) =
        (dot U W) * (dot p q) ^ 3 * (dot r V) := by
    dsimp only [f1]
    rw [thirdFullSharpFiveIndependentSums244]
    dsimp only [dot]
    ring
  have h2 :
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ t : A3,
        f2 j i k l t) =
        (dot U V) * (dot p q) ^ 2 * (dot p r) * (dot q W) := by
    dsimp only [f2]
    rw [thirdFullSharpFiveIndependentSums244]
    dsimp only [dot]
    ring
  have h3 :
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ t : A3,
        f3 j i k l t) =
        (dot U V) * (dot p q) ^ 2 * (dot p r) * (dot q W) := by
    dsimp only [f3]
    rw [thirdFullSharpFiveIndependentSums244]
    dsimp only [dot]
    ring
  have h4 :
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ t : A3,
        f4 j i k l t) =
        (dot U V) * (dot p q) ^ 2 * (dot p r) * (dot q W) := by
    dsimp only [f4]
    rw [thirdFullSharpFiveIndependentSums244]
    dsimp only [dot]
    ring
  have hAxis (j i k l t : A3) :
      thirdFullSharpFiveCoordinateAxis244 p q r U V W j i k l t =
        2 * (((f1 j i k l t + f2 j i k l t) +
          f3 j i k l t) + f4 j i k l t) := by
    dsimp [thirdFullSharpFiveCoordinateAxis244, f1, f2, f3, f4]
    ring
  calc
    thirdFullSharpFiveCoordinateTotal244 p q r U V W =
        ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ t : A3,
          2 * (((f1 j i k l t + f2 j i k l t) +
            f3 j i k l t) + f4 j i k l t) := by
      unfold thirdFullSharpFiveCoordinateTotal244
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro t _
      exact hAxis j i k l t
    _ = 2 * ((((∑ j : A3, ∑ i : A3, ∑ k : A3,
                 ∑ l : A3, ∑ t : A3, f1 j i k l t) +
                (∑ j : A3, ∑ i : A3, ∑ k : A3,
                 ∑ l : A3, ∑ t : A3, f2 j i k l t)) +
                (∑ j : A3, ∑ i : A3, ∑ k : A3,
                 ∑ l : A3, ∑ t : A3, f3 j i k l t)) +
                (∑ j : A3, ∑ i : A3, ∑ k : A3,
                 ∑ l : A3, ∑ t : A3, f4 j i k l t)) := by
      simp only [mul_add, Finset.sum_add_distrib,
        Finset.mul_sum] <;> ring
    _ = _ := by
      rw [h1, h2, h3, h4,
        thirdFullSharpDot_comm244 r V,
        thirdFullSharpDot_comm244 q W]
      ring

/-- Exact polynomial reduction of the TRUE corrected physical gradient
and TRUE interpolation core. This is the missing five-index contraction:
no momenta, divergence or symmetry hypotheses beyond matching the carrier
frequency coordinates are needed. -/
theorem thirdFullSharpPhysicalOrderedCore_eq_twice_corrected244
    (z : PairV244) (p q r U V W : Freq244)
    (hp : WithLp.ofLp z.1 = p)
    (hq : WithLp.ofLp (-(z.1 + z.2)) = q)
    (hr : WithLp.ofLp z.2 = r) :
    thirdFullSharpPhysicalOrderedCore244 z p q r U V W =
      2 * thirdFullPhysicalOrderedSymbol244 p q r U V W := by
  unfold thirdFullSharpPhysicalOrderedCore244
  rw [thirdFullSharpGradientFive_eq_coordinate_total244,
      thirdFullSharpFiveCoordinateTotal_contract244]
  rw [hp, hq, hr]
  unfold thirdFullSharpInterpolationOrdered244
    thirdFullPhysicalOrderedSymbol244
  dsimp only
  -- Both coordinate dots and the old `thirdTriadAxisDot244` are the
  -- same finite real axis sum, only named differently.
  change 2 * ((dot U W * dot V r) * (dot p q) ^ 3 +
        3 * ((dot U V * dot W q) * (dot p q) ^ 2 * dot p r)) +
      6 * (dot p r * (dot p q) ^ 2 * dot r V * dot U W) =
    2 * ((dot U W * dot V r) *
      ((dot p q) ^ 3 + 3 * (dot p q) ^ 2 * dot p r) +
      (dot U V * dot W q) * (3 * (dot p q) ^ 2 * dot p r))
  rw [thirdFullSharpDot_comm244 r V]
  ring


/-- The genuine cutoff-free Schwartz physical core, evaluated at a sharp
positive coherent center, equals twice the CORRECTED ordered symbol at that
center with its three prescribed polarizations. This follows from the
actual moving-germ center bridge and the five-index contraction above. -/
theorem thirdFullPositiveSectorPhysicalCore_center_eq_twice_corrected244
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hp : WithLp.ofLp z.1 =
      thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).1)
    (hr : WithLp.ofLp z.2 =
      thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).2)
    (hq : thirdFullMiddleFrequency244
      (thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).1,
       thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).2) =
        thirdFullAxisSixCenter244 (thirdFullPositiveMiddleLabel244 n))
    (hTrans : ∀ i : Fin 6, (i = 0 ∨ i = 1 ∨ i = 2) →
      thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
        (thirdFullPositiveWindowPolarization244 A B C i) = 0)
    (hNonzero : ∀ i : Fin 6,
      thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
        (thirdFullAxisSixCenter244 i) ≠ 0) :
    thirdFullPositiveSectorPhysicalCore244 A B C n z =
      2 * thirdFullPhysicalOrderedSymbol244
        (thirdFullAxisSixCenter244
          (lowNormalQuarterCoherentLabelPair false n).1)
        (thirdFullAxisSixCenter244 (thirdFullPositiveMiddleLabel244 n))
        (thirdFullAxisSixCenter244
          (lowNormalQuarterCoherentLabelPair false n).2)
        (thirdFullPositiveWindowPolarization244 A B C
          (lowNormalQuarterCoherentLabelPair false n).1)
        (thirdFullPositiveWindowPolarization244 A B C
          (thirdFullPositiveMiddleLabel244 n))
        (thirdFullPositiveWindowPolarization244 A B C
          (lowNormalQuarterCoherentLabelPair false n).2) := by
  rw [thirdFullPositiveSectorPhysicalCore_at_center244
    A B C n z hp hr hq hTrans hNonzero]
  have hq' : WithLp.ofLp (-(z.1 + z.2)) =
      thirdFullAxisSixCenter244 (thirdFullPositiveMiddleLabel244 n) := by
    rw [← thirdFullMiddleFrequency_ofLp_pair244 z]
    rw [hp, hr]
    exact hq
  exact thirdFullSharpPhysicalOrderedCore_eq_twice_corrected244
    z _ _ _ _ _ _ hp hq' hr

end
end PrimeTensor.FirstMonomialTriad
