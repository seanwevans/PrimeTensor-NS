import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualOscillationDichotomy
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Two distinct finite native cluster factors from bounded residual oscillation

The preceding file identified persistent tail separation as the exact
obstruction to a full canonical native proportionality factor.

Persistent separation alone does not imply finite cluster states: the residual
could be unbounded.  But in the bounded cancellation branch we already have
eventual boundedness of the complementary residual logarithm.

This file combines exactly those two facts.

For an eventually bounded native sequence `Ω`, if its logarithmic coordinate
has one fixed positive separation scale on arbitrarily late tails, then there
are two cofinal refinements of the original sequence converging intrinsically
to two distinct finite native states.

Specialized to the terminal complementary residual, this says:

    bounded residual + failure of the full canonical factor

forces two distinct finite native cluster factors.

No claim is made that there are only two cluster states, that either cluster
state is selected canonically, or that the original full residual converges.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem terminalNative_twoDistinctClusterLimits_of_bounded_separated
    (Ω : ℕ → MulReal)
    (N : ℕ)
    (C : ℝ)
    (hBound :
      ∀ n : ℕ,
        N ≤ n →
        abs (PrimeTensor.Bridge.MulReal.logValue (Ω n)) ≤ C)
    (hSeparated :
      ∃ ε : ℝ,
        0 < ε ∧
        ∀ K : ℕ,
          ∃ m : ℕ,
            K ≤ m ∧
            ∃ n : ℕ,
              K ≤ n ∧
              ε ≤
                dist
                  (PrimeTensor.Bridge.MulReal.logValue (Ω m))
                  (PrimeTensor.Bridge.MulReal.logValue (Ω n))) :
    ∃ q₁ q₂ : MulReal,
      q₁ ≠ q₂ ∧
      ∃ k₁ k₂ : ℕ → ℕ,
        Tendsto k₁ atTop atTop ∧
        Tendsto k₂ atTop atTop ∧
        H3TerminalNativeNatConvergesTo (fun j : ℕ => Ω (k₁ j)) q₁ ∧
        H3TerminalNativeNatConvergesTo (fun j : ℕ => Ω (k₂ j)) q₂ := by

  obtain ⟨ε, hε, hSeparatedTail⟩ := hSeparated

  let R : ℕ → ℝ :=
    fun n : ℕ => PrimeTensor.Bridge.MulReal.logValue (Ω n)

  have hPairs :
      ∀ k : ℕ,
        ∃ m : ℕ,
          k + N ≤ m ∧
          ∃ n : ℕ,
            k + N ≤ n ∧
            ε ≤ dist (R m) (R n) := by
    intro k
    exact hSeparatedTail (k + N)

  choose m hm n hn hmn using hPairs

  have hmTop : Tendsto m atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro K
    filter_upwards [eventually_ge_atTop K] with k hk
    have hk_m : k ≤ m k :=
      le_trans
        (Nat.le_add_right k N)
        (hm k)
    exact le_trans hk hk_m

  have hnTop : Tendsto n atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro K
    filter_upwards [eventually_ge_atTop K] with k hk
    have hk_n : k ≤ n k :=
      le_trans
        (Nat.le_add_right k N)
        (hn k)
    exact le_trans hk hk_n

  let C₀ : ℝ := max C 0

  have hmMem :
      ∀ k : ℕ,
        R (m k) ∈ Set.Icc (-C₀) C₀ := by
    intro k
    have hNm : N ≤ m k :=
      le_trans
        (Nat.le_add_left N k)
        (hm k)
    have hAbs : abs (R (m k)) ≤ C := by
      dsimp only [R]
      exact hBound (m k) hNm
    have hAbs₀ : abs (R (m k)) ≤ C₀ :=
      le_trans hAbs (le_max_left C 0)
    exact abs_le.mp hAbs₀

  have hnMem :
      ∀ k : ℕ,
        R (n k) ∈ Set.Icc (-C₀) C₀ := by
    intro k
    have hNn : N ≤ n k :=
      le_trans
        (Nat.le_add_left N k)
        (hn k)
    have hAbs : abs (R (n k)) ≤ C := by
      dsimp only [R]
      exact hBound (n k) hNn
    have hAbs₀ : abs (R (n k)) ≤ C₀ :=
      le_trans hAbs (le_max_left C 0)
    exact abs_le.mp hAbs₀

  obtain ⟨r₁, _, φ, hφStrict, hmSub⟩ :=
    tendsto_subseq_of_bounded
      (Metric.isBounded_Icc (-C₀) C₀)
      hmMem

  let nφ : ℕ → ℝ :=
    fun k : ℕ => R (n (φ k))

  have hnφMem :
      ∀ k : ℕ,
        nφ k ∈ Set.Icc (-C₀) C₀ := by
    intro k
    exact hnMem (φ k)

  obtain ⟨r₂, _, ψ, hψStrict, hnSub⟩ :=
    tendsto_subseq_of_bounded
      (Metric.isBounded_Icc (-C₀) C₀)
      hnφMem

  have hφψTop :
      Tendsto (fun k : ℕ => φ (ψ k)) atTop atTop := by
    exact hφStrict.tendsto_atTop.comp hψStrict.tendsto_atTop

  have hmFinal :
      Tendsto
        (fun k : ℕ => R (m (φ (ψ k))))
        atTop
        (𝓝 r₁) := by
    simpa [Function.comp_def] using
      hmSub.comp hψStrict.tendsto_atTop

  have hnFinal :
      Tendsto
        (fun k : ℕ => R (n (φ (ψ k))))
        atTop
        (𝓝 r₂) := by
    simpa [Function.comp_def, nφ] using hnSub

  have hDistance :
      Tendsto
        (fun k : ℕ =>
          dist
            (R (m (φ (ψ k))))
            (R (n (φ (ψ k)))))
        atTop
        (𝓝 (dist r₁ r₂)) :=
    hmFinal.dist hnFinal

  have hLimitSeparated :
      ε ≤ dist r₁ r₂ := by
    apply ge_of_tendsto hDistance
    filter_upwards with k
    exact hmn (φ (ψ k))

  have hrNe : r₁ ≠ r₂ := by
    intro hr
    have hεZero : ε ≤ 0 := by
      simpa [hr] using hLimitSeparated
    linarith

  obtain ⟨q₁, hq₁⟩ :=
    PrimeTensor.Bridge.MulReal.logValue_surjective r₁

  obtain ⟨q₂, hq₂⟩ :=
    PrimeTensor.Bridge.MulReal.logValue_surjective r₂

  have hqNe : q₁ ≠ q₂ := by
    intro hq
    apply hrNe
    rw [← hq₁, ← hq₂, hq]

  let k₁ : ℕ → ℕ :=
    fun k : ℕ => m (φ (ψ k))

  let k₂ : ℕ → ℕ :=
    fun k : ℕ => n (φ (ψ k))

  have hk₁Top : Tendsto k₁ atTop atTop := by
    dsimp only [k₁]
    exact hmTop.comp hφψTop

  have hk₂Top : Tendsto k₂ atTop atTop := by
    dsimp only [k₂]
    exact hnTop.comp hφψTop

  have hNative₁ :
      H3TerminalNativeNatConvergesTo
        (fun k : ℕ => Ω (k₁ k))
        q₁ := by
    apply
      (terminalNativeNatConvergesTo_iff_logValue_tendsto
        (fun k : ℕ => Ω (k₁ k))
        q₁).2
    rw [hq₁]
    simpa [k₁, R] using hmFinal

  have hNative₂ :
      H3TerminalNativeNatConvergesTo
        (fun k : ℕ => Ω (k₂ k))
        q₂ := by
    apply
      (terminalNativeNatConvergesTo_iff_logValue_tendsto
        (fun k : ℕ => Ω (k₂ k))
        q₂).2
    rw [hq₂]
    simpa [k₂, R] using hnFinal

  exact
    ⟨q₁, q₂, hqNe, k₁, k₂, hk₁Top, hk₂Top, hNative₁, hNative₂⟩

def H3TerminalNativeComplementHasTwoDistinctClusterFactors
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∃ q₁ q₂ : MulReal,
    q₁ ≠ q₂ ∧
    ∃ k₁ k₂ : ℕ → ℕ,
      Tendsto k₁ atTop atTop ∧
      Tendsto k₂ atTop atTop ∧
      H3TerminalNativeComplementProportionalityFactor
        u p
        (fun j : ℕ => τ (k₁ j))
        (fun j : ℕ => x (k₁ j))
        q₁ ∧
      H3TerminalNativeComplementProportionalityFactor
        u p
        (fun j : ℕ => τ (k₂ j))
        (fun j : ℕ => x (k₂ j))
        q₂

theorem nativeComplementHasTwoDistinctClusterFactors_of_bounded_of_persistentTailSeparation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (N : ℕ)
    (C : ℝ)
    (hBound :
      ∀ n : ℕ,
        N ≤ n →
        abs
          (h3TerminalNativeComplementResidualLogSequence
            u p τ x n)
          ≤ C)
    (hSeparated :
      H3TerminalNativeComplementResidualPersistentTailSeparation
        u p τ x) :
    H3TerminalNativeComplementHasTwoDistinctClusterFactors
      u p τ x := by

  let Ω : ℕ → MulReal :=
    fun n : ℕ =>
      PrimeTensor.MulReal.ratio
        (h3TerminalNativeGradientForPair u p (τ n) (x n))
        (h3TerminalSelectedSignedNativeCurlForPair u p (τ n) (x n))

  have hΩBound :
      ∀ n : ℕ,
        N ≤ n →
        abs
          (PrimeTensor.Bridge.MulReal.logValue (Ω n))
          ≤ C := by
    intro n hn
    exact hBound n hn

  have hΩSeparated :
      ∃ ε : ℝ,
        0 < ε ∧
        ∀ K : ℕ,
          ∃ m : ℕ,
            K ≤ m ∧
            ∃ n : ℕ,
              K ≤ n ∧
              ε ≤
                dist
                  (PrimeTensor.Bridge.MulReal.logValue (Ω m))
                  (PrimeTensor.Bridge.MulReal.logValue (Ω n)) := by
    simpa [
      H3TerminalNativeComplementResidualPersistentTailSeparation,
      h3TerminalNativeComplementResidualLogSequence,
      Ω
    ] using hSeparated

  obtain
    ⟨q₁, q₂, hqNe, k₁, k₂, hk₁Top, hk₂Top, hNative₁, hNative₂⟩ :=
    terminalNative_twoDistinctClusterLimits_of_bounded_separated
      Ω N C hΩBound hΩSeparated

  refine
    ⟨q₁, q₂, hqNe, k₁, k₂, hk₁Top, hk₂Top, ?_, ?_⟩

  · unfold H3TerminalNativeComplementProportionalityFactor
    simpa [Ω] using hNative₁

  · unfold H3TerminalNativeComplementProportionalityFactor
    simpa [Ω] using hNative₂

theorem nativeComplementHasTwoDistinctClusterFactors_of_complementBound_of_persistentTailSeparation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (N : ℕ)
    (C : ℝ)
    (hComplementBound :
      ∀ n : ℕ,
        N ≤ n →
        abs
          (PrimeTensor.Bridge.MulReal.logValue
            (h3TerminalNativeComplementGradientForPair
              u p (τ n) (x n)))
          ≤ C)
    (hSeparated :
      H3TerminalNativeComplementResidualPersistentTailSeparation
        u p τ x) :
    H3TerminalNativeComplementHasTwoDistinctClusterFactors
      u p τ x := by

  apply
    nativeComplementHasTwoDistinctClusterFactors_of_bounded_of_persistentTailSeparation
      u p τ x N C ?_ hSeparated

  intro n hn

  have h :=
    hComplementBound n hn

  simpa [
    h3TerminalNativeComplementResidualLogSequence,
    ← h3TerminalNativeComplementGradientForPair_eq_residualRatio
  ] using h

end

end Euclidean
end Bridge
end PrimeTensor
