import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceTopShareLimitOne
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Full.Energy.Dissipation.Cascade

/-!
# Universal left-terminal H³ top-energy concentration

The earlier fixed-directed-source theorem proved E₃(τ n) / E(τ n) → 1
on one selected sequence. But independently, the terminal derivative cascade
proves E₃(t) → +∞ on the ENTIRE left terminal neighborhood under hypothetical
nonextension. A fixed kinetic anchor and the previously established adjustable
physical Fourier interpolation apply to all later admissible times.

Hence, without choosing an obstruction sequence, the normalized top energy
E₃(t)/E(t) tends to one as t approaches T from below; correspondingly,
E₁(t)+E₂(t) is negligible compared with E₃(t) on the entire terminal tail.
This is only a necessary consequence of hypothetical nonextension. Neither
the directed gradient channel nor the ordered signed-monomial alternative is
excluded, and no unconditional smooth continuation is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Uniform-in-time top-order concentration: every positive epsilon bounds
the full H³ energy by `(1+epsilon) E₃` throughout a sufficiently late
left terminal neighborhood. This strengthens a selected-sequence statement. -/
theorem h3PathCanonical_eventually_fullEnergy_le_one_add_epsilon_top_nhdsLT
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      velocityH3EnergyAt u t ≤
        (1 + ε) * velocityH3Energy3At u t := by
  let A : ℝ := 1 + 4 / ε
  have hA : 1 ≤ A := by
    dsimp only [A]
    have hDiv : 0 ≤ (4 : ℝ) / ε := div_nonneg (by norm_num) hε.le
    linarith only [hDiv]
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hRatio : 2 / A ≤ ε / 2 := by
    have hAHigh : 4 / ε ≤ A := by
      dsimp only [A]
      have hOne : 0 ≤ (1 : ℝ) := by norm_num
      linarith only [hOne]
    have hScaled := mul_le_mul_of_nonneg_left hAHigh hε.le
    have hCancel : ε * (4 / ε) = 4 := by
      field_simp [ne_of_gt hε]
    have hFour : 4 ≤ ε * A := by
      nlinarith only [hScaled, hCancel]
    exact (div_le_iff₀ hApos).2 (by nlinarith only [hFour])
  let C : ℝ := 1 + (1 + A + A ^ 2) * velocityH3Energy0At u b
  let M : ℝ := (2 * C) / ε
  have hTopT : Tendsto (velocityH3Energy3At u) (𝓝[<] T) atTop :=
    velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hTopLarge : ∀ᶠ t : ℝ in 𝓝[<] T,
      M ≤ velocityH3Energy3At u t :=
    (tendsto_atTop.1 hTopT) M
  have hTail : Set.Ioo b T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hb.2
  filter_upwards [hTopLarge, hTail] with t hLarge ht
  have hAnchor : velocityH3EnergyAt u t ≤
      C + (1 + 2 / A) * velocityH3Energy3At u t := by
    simpa only [C] using
      h3PathCanonical_fullEnergy_le_anchorCost_add_scaledTop
        hH3 hClass hb ht A hA
  have hScaled : (ε / 2) * M ≤
      (ε / 2) * velocityH3Energy3At u t :=
    mul_le_mul_of_nonneg_left hLarge (by positivity)
  have hCancel : (ε / 2) * M = C := by
    dsimp only [M]
    field_simp [ne_of_gt hε]
  have hSmall : C ≤ (ε / 2) * velocityH3Energy3At u t := by
    linarith only [hScaled, hCancel]
  have hRatioScaled :
      (2 / A) * velocityH3Energy3At u t ≤
        (ε / 2) * velocityH3Energy3At u t :=
    mul_le_mul_of_nonneg_right hRatio
      (velocityH3Energy3At_nonneg u t)
  calc
    velocityH3EnergyAt u t ≤
        C + (1 + 2 / A) * velocityH3Energy3At u t := hAnchor
    _ = C + velocityH3Energy3At u t +
          (2 / A) * velocityH3Energy3At u t := by ring
    _ ≤ (ε / 2) * velocityH3Energy3At u t +
          velocityH3Energy3At u t +
          (ε / 2) * velocityH3Energy3At u t := by
      linarith only [hSmall, hRatioScaled]
    _ = (1 + ε) * velocityH3Energy3At u t := by ring

/-- The normalized third-derivative energy approaches one along EVERY
left-terminal time sequence, indeed along the full one-sided neighborhood. -/
theorem h3PathCanonical_topShare_tendsto_one_nhdsLT_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    Tendsto (fun t : ℝ =>
        velocityH3Energy3At u t / velocityH3EnergyAt u t)
      (𝓝[<] T) (𝓝 1) := by
  have hUpper : ∀ ε : ℝ, 0 < ε →
      (∀ᶠ t : ℝ in 𝓝[<] T,
        velocityH3EnergyAt u t ≤
          (1 + ε) * velocityH3Energy3At u t) := by
    intro ε hε
    exact h3PathCanonical_eventually_fullEnergy_le_one_add_epsilon_top_nhdsLT
      hH3 hNoExtension hClass hb ε hε
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    let ε : ℝ := (1 - c) / 2
    have hε : 0 < ε := by
      dsimp only [ε]
      linarith only [hc]
    have hCoeff : 0 < 1 + ε := by linarith only [hε]
    have hFactor : 0 < (1 - c) * (2 - c) :=
      mul_pos (by linarith only [hc]) (by linarith only [hc])
    have hcBelow : c < 1 / (1 + ε) := by
      apply (lt_div_iff₀ hCoeff).2
      dsimp only [ε]
      nlinarith only [hFactor]
    filter_upwards [hUpper ε hε] with t ht
    exact lt_of_lt_of_le hcBelow
      (h3PathCanonical_topShare_ge_inv_one_add_epsilon u t ε hε ht)
  · intro c hc
    exact Filter.Eventually.of_forall (fun t => by
      have hE : 0 < velocityH3EnergyAt u t :=
        lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
      have hTop : velocityH3Energy3At u t ≤
          velocityH3EnergyAt u t :=
        velocityH3Energy3At_le_velocityH3EnergyAt u t
      exact lt_of_le_of_lt ((div_le_iff₀ hE).2 (by simpa using hTop)) hc)

/-- The physical first- and second-order blocks are negligible relative to
E₃ on the entire left terminal neighborhood, not just at selected times. -/
theorem h3PathCanonical_eventually_lowerOrders_le_epsilon_top_nhdsLT
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      velocityH3Energy1At u t + velocityH3Energy2At u t ≤
        ε * velocityH3Energy3At u t := by
  have hUpper :=
    h3PathCanonical_eventually_fullEnergy_le_one_add_epsilon_top_nhdsLT
      hH3 hNoExtension hClass hb ε hε
  filter_upwards [hUpper] with t ht
  have h0 : 0 ≤ velocityH3Energy0At u t :=
    velocityH3Energy0At_nonneg u t
  unfold velocityH3EnergyAt at ht
  nlinarith only [ht, h0]

end
end Euclidean
end Bridge
end PrimeTensor
