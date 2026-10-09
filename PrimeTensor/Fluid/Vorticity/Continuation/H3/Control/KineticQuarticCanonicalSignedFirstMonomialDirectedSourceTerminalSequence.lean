import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialFixedDirectedTenSource

/-!
# A single directed H³ obstruction with a normalized terminal blowup sequence

The fixed-ten-source theorem chooses one index (the gradient excess or one
ordered velocity-component channel) that exceeds every normalized threshold
arbitrarily late. This file extracts one *actual sequence* of times tending
to the terminal time on which that fixed source, divided by nine times the
physical H³ energy, tends to +infinity.

The conclusion is conditional on hypothetical nonextension. In particular,
it neither selects which source occurs nor proves any PDE sign estimate,
nonextension, or finite-time singularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- From nonextension, one fixed directed H³ source exceeds the normalized
index `n` along an actual sequence `τ n → T`. The same sequence also makes
the unnormalized signed source diverge to `+∞`, since `E_H3 ≥ 1`. -/
theorem h3PathCanonical_fixedDirectedTenSource_normalizedTerminalSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (τ : ℕ → ℝ),
      (∀ n : ℕ,
        τ n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto
        (fun n : ℕ =>
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i) atTop atTop := by
  obtain ⟨i, hPersistent⟩ :=
    h3PathCanonical_fixedJointDirectedTenSource_on_every_subtail
      hH3 hNoExtension hClass hb
  have hChoice (n : ℕ) :
      ∃ t : ℝ,
        t ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        9 * (n : ℝ) * velocityH3EnergyAt u t <
          h3PathCanonicalJointDirectedTenSourceAt u t i := by
    let ε : ℝ := (1 : ℝ) / ((n : ℝ) + 1)
    let d : ℝ := max ((b + T) / 2) (T - ε)
    have hε : 0 < ε := by
      dsimp only [ε]
      positivity
    have hMidLower : b < (b + T) / 2 := by
      linarith only [hb.2]
    have hMidUpper : (b + T) / 2 < T := by
      linarith only [hb.2]
    have hd : d ∈ Set.Ioo b T := by
      dsimp only [d]
      exact ⟨lt_of_lt_of_le hMidLower (le_max_left _ _),
        (max_lt_iff).2 ⟨hMidUpper, by linarith only [hε]⟩⟩
    obtain ⟨t, ht, hLarge⟩ :=
      hPersistent d hd (n : ℝ) (by positivity)
    refine ⟨t, ?_, hLarge⟩
    exact ⟨lt_of_le_of_lt (le_max_right _ _) ht.1, ht.2⟩
  choose τ hτ using hChoice
  have hRatio (n : ℕ) :
      (n : ℝ) <
        h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
          (9 * velocityH3EnergyAt u (τ n)) := by
    have hE : 0 < 9 * velocityH3EnergyAt u (τ n) := by
      have hOne := one_le_velocityH3EnergyAt u (τ n)
      linarith only [hOne]
    apply (lt_div_iff₀ hE).2
    nlinarith only [(hτ n).2]
  have hInv :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hNormBound : ∀ n : ℕ,
      ‖τ n - T‖ ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
    intro n
    have hNear := (hτ n).1
    rw [Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (le_of_lt hNear.2))]
    linarith only [hNear.1]
  have hTendsto : Tendsto τ atTop (𝓝 T) :=
    (tendsto_iff_norm_sub_tendsto_zero).2
      (squeeze_zero'
        (Filter.Eventually.of_forall (fun n => norm_nonneg (τ n - T)))
        (Filter.Eventually.of_forall hNormBound)
        hInv)
  have hRatioTendsto :
      Tendsto
        (fun n : ℕ =>
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M
    filter_upwards [eventually_ge_atTop N] with n hn
    have hMn : M < (n : ℝ) :=
      lt_of_lt_of_le hN (by exact_mod_cast hn)
    exact le_of_lt (lt_trans hMn (hRatio n))
  have hRaw (n : ℕ) :
      9 * (n : ℝ) < h3PathCanonicalJointDirectedTenSourceAt u (τ n) i := by
    have hOne := one_le_velocityH3EnergyAt u (τ n)
    have hScaled :
        9 * (n : ℝ) * 1 ≤
          9 * (n : ℝ) * velocityH3EnergyAt u (τ n) :=
      mul_le_mul_of_nonneg_left hOne (by positivity)
    linarith only [hScaled, (hτ n).2]
  have hRawTendsto :
      Tendsto (fun n : ℕ =>
        h3PathCanonicalJointDirectedTenSourceAt u (τ n) i) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M
    filter_upwards [eventually_ge_atTop N] with n hn
    have hMn : M < (n : ℝ) :=
      lt_of_lt_of_le hN (by exact_mod_cast hn)
    have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hScale : (n : ℝ) ≤ 9 * (n : ℝ) := by
      linarith only [hnNonneg]
    exact le_of_lt (lt_trans hMn (lt_of_le_of_lt hScale (hRaw n)))
  exact ⟨i, τ, (fun n => ⟨(hτ n).1, hRatio n⟩),
    hTendsto, hRatioTendsto, hRawTendsto⟩

end
end Euclidean
end Bridge
end PrimeTensor
