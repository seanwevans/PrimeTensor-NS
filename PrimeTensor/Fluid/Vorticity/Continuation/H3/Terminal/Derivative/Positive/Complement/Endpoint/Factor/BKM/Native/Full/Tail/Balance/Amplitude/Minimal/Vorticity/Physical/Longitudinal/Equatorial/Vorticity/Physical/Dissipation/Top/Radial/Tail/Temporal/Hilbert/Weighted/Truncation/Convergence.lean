import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Truncated.Derivative
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Strong convergence of the bounded `q²` truncations

For the natural radial cutoffs

    R_n = n + 1,

the high-frequency sets

    {|D| >= R_n}

decrease to the empty set.  Consequently every fixed Fourier `L²` state has
vanishing square mass on those high-frequency tails.

If `G` is an `L²` state satisfying

    G(ξ) = q(ξ)^2 F(ξ)

almost everywhere, then the bounded operators from the preceding checkpoint,

    T_R F = 1_{|D|<R} q² F,

therefore satisfy

    T_{n+1} F -> G

strongly in Fourier `L²`.

This is the reusable cutoff-removal lemma needed twice:

1. for the selected velocity, where `G = q² û_j`;
2. for the selected PDE right-hand side, where
   `G = q²(-q û_j - F_j) = -q³ û_j - q² F_j`.

No temporal argument appears here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedTruncationConvergence
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Natural high-frequency exhaustion -/

/--
The natural high-frequency complement at index `n`.
-/
def h3TopTailNaturalHighRadialSet
    (n : ℕ) :
    Set H3FourierPoint3 :=
  (
    h3TerminalRadialFrequencyBelow
      ((n : ℝ) + 1)
  )ᶜ

theorem measurableSet_h3TopTailNaturalHighRadialSet
    (n : ℕ) :
    MeasurableSet
      (h3TopTailNaturalHighRadialSet n) := by
  unfold h3TopTailNaturalHighRadialSet
  exact
    (
      measurableSet_h3TerminalRadialFrequencyBelow
        ((n : ℝ) + 1)
    ).compl

/--
The natural high-frequency sets are antitone.
-/
theorem antitone_h3TopTailNaturalHighRadialSet :
    Antitone h3TopTailNaturalHighRadialSet := by

  intro m n hmn
  intro ξ hξ

  simp only [
    h3TopTailNaturalHighRadialSet,
    Set.mem_compl_iff,
    h3TerminalRadialFrequencyBelow,
    Set.mem_ofPred_eq
  ] at hξ ⊢

  intro hLow

  apply hξ

  have hNat :
      m + 1 ≤ n + 1 :=
    Nat.add_le_add_right hmn 1

  have hCast :
      (m : ℝ) + 1
        ≤
      (n : ℝ) + 1 := by
    exact_mod_cast hNat

  exact
    lt_of_lt_of_le hLow hCast

/--
The intersection of all natural high-frequency sets is empty.
-/
theorem iInter_h3TopTailNaturalHighRadialSet_eq_empty :
    (⋂ n : ℕ, h3TopTailNaturalHighRadialSet n)
      =
    (∅ : Set H3FourierPoint3) := by

  ext ξ

  simp only [
    Set.mem_iInter,
    Set.mem_empty_iff_false,
    iff_false
  ]

  intro hAll

  obtain ⟨N : ℕ, hN⟩ :=
    exists_nat_gt
      (h3FourierGradientMagnitude ξ)

  have hHigh :=
    hAll N

  simp only [
    h3TopTailNaturalHighRadialSet,
    Set.mem_compl_iff,
    h3TerminalRadialFrequencyBelow,
    Set.mem_ofPred_eq
  ] at hHigh

  apply hHigh

  have hNN :
      (N : ℝ) < (N : ℝ) + 1 := by
    linarith

  exact
    lt_trans hN hNN

/-! ## Vanishing `L²` square tails -/

/--
Every fixed Fourier `L²` state has vanishing square mass on the natural
high-frequency tails.
-/
theorem tendsto_h3FourierComplexL2_highRadial_squareMass_zero
    (G : H3FourierComplexL2) :
    Tendsto
      (fun n : ℕ =>
        ∫ ξ in h3TopTailNaturalHighRadialSet n,
          ‖G ξ‖ ^ 2
        ∂volume)
      atTop
      (𝓝 0) := by

  have hInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖G ξ‖ ^ 2)
        volume :=
    (MeasureTheory.Lp.memLp G).norm.integrable_sq

  have hTail :=
    tendsto_setIntegral_of_antitone
      (f :=
        fun ξ : H3FourierPoint3 =>
          ‖G ξ‖ ^ 2)
      (fun n =>
        measurableSet_h3TopTailNaturalHighRadialSet n)
      antitone_h3TopTailNaturalHighRadialSet
      ⟨0, hInt.integrableOn⟩

  rw [
    iInter_h3TopTailNaturalHighRadialSet_eq_empty
  ] at hTail

  simpa using hTail

/-! ## Exact truncation-error identity -/

/--
If `G = q² F` almost everywhere, then the square `L²` error of the natural
truncation is exactly the square mass of `G` on the complementary high-radial
tail.
-/
theorem norm_sq_h3TopTailTruncatedQSqL2_sub_eq_highRadial_squareMass
    (F G : H3FourierComplexL2)
    (hFG :
      (
        (G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        F ξ))
    (n : ℕ) :
    ‖(
      h3TopTailTruncatedQSqL2
          ((n : ℝ) + 1)
          (by positivity)
          F
        -
      G
    )‖ ^ 2
      =
    ∫ ξ in h3TopTailNaturalHighRadialSet n,
      ‖G ξ‖ ^ 2
    ∂volume := by

  rw [
    h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
  ]

  rw [
    ← integral_indicator
      (measurableSet_h3TopTailNaturalHighRadialSet n)
  ]

  apply integral_congr_ae

  have hTrunc :=
    h3TopTailTruncatedQSqL2_ae
      ((n : ℝ) + 1)
      (by positivity)
      F

  filter_upwards [hTrunc, hFG] with ξ hTruncξ hFGξ

  rw [hTruncξ]

  unfold
    h3TopTailTruncatedQSqFunction
    h3TopTailTruncatedQSqMultiplier

  by_cases hLow :
      ξ ∈
        h3TerminalRadialFrequencyBelow
          ((n : ℝ) + 1)

  · rw [Set.indicator_of_mem hLow]
    rw [hFGξ]

    have hNotHigh :
        ξ ∉ h3TopTailNaturalHighRadialSet n := by
      simp only [
        h3TopTailNaturalHighRadialSet,
        Set.mem_compl_iff,
        not_not
      ]
      exact hLow

    rw [Set.indicator_of_notMem hNotHigh]

    simp

  · rw [Set.indicator_of_notMem hLow]

    have hHigh :
        ξ ∈ h3TopTailNaturalHighRadialSet n := by
      simpa only [
        h3TopTailNaturalHighRadialSet,
        Set.mem_compl_iff
      ] using hLow

    rw [Set.indicator_of_mem hHigh]

    simp

/-! ## Strong convergence on the weighted domain -/

/--
Whenever `G = q² F` almost everywhere, the natural bounded truncations of
`F` converge strongly in Fourier `L²` to `G`.
-/
theorem tendsto_h3TopTailTruncatedQSqL2_of_ae_eq
    (F G : H3FourierComplexL2)
    (hFG :
      (
        (G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        F ξ)) :
    Tendsto
      (fun n : ℕ =>
        h3TopTailTruncatedQSqL2
          ((n : ℝ) + 1)
          (by positivity)
          F)
      atTop
      (𝓝 G) := by

  apply
    tendsto_iff_norm_sub_tendsto_zero.2

  have hTail :=
    tendsto_h3FourierComplexL2_highRadial_squareMass_zero
      G

  have hSq :
      Tendsto
        (fun n : ℕ =>
          ‖(
            h3TopTailTruncatedQSqL2
                ((n : ℝ) + 1)
                (by positivity)
                F
              -
            G
          )‖ ^ 2)
        atTop
        (𝓝 0) := by

    apply
      hTail.congr'

    filter_upwards with n

    exact
      (
        norm_sq_h3TopTailTruncatedQSqL2_sub_eq_highRadial_squareMass
          F G hFG n
      ).symm

  have hSqrt :=
    (Real.continuous_sqrt.tendsto 0).comp
      hSq

  change
    Tendsto
      (fun n : ℕ =>
        Real.sqrt
          (
            ‖(
              h3TopTailTruncatedQSqL2
                  ((n : ℝ) + 1)
                  (by positivity)
                  F
                -
              G
            )‖ ^ 2
          ))
      atTop
      (𝓝 (Real.sqrt 0))
    at hSqrt

  simpa only [
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg,
    norm_nonneg,
    Real.sqrt_zero
  ] using hSqrt

end

end Euclidean
end Bridge
end PrimeTensor
