import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceTopShareClock

/-!
# Universal asymptotic third-order energy share on the fixed H³ obstruction

The selected indexed H³ nonextension sequence already has E₃(τ n) → +∞.
The physical zeroth-order kinetic energy is antitone on the admissible tail,
and the proved endpoint interpolation gives

    E(t) ≤ 1 + 3 (E₀(t) + E₃(t)).

Therefore, for *every* epsilon > 0, the same exact indexed sequence eventually
satisfies

    E₃(τ n) ≤ E(τ n) ≤ (3 + epsilon) E₃(τ n),
    1/(3 + epsilon) ≤ E₃(τ n)/E(τ n).

This is stronger than the fixed-anchor comparison E ≤ (4+3 E₀(b)) E₃:
the asymptotic coefficient is universal. It applies to either source branch.
The existing indexed gradient top-share clock and the alternative fixed
ordered signed monomial both remain intact. Nothing here makes either
nonextension branch impossible.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- A fixed kinetic anchor bounds the entire lower-order H³ contribution
at every later admissible time. -/
theorem h3PathCanonical_fullEnergy_le_kineticAnchor_add_threeTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    velocityH3EnergyAt u t ≤
      (1 + 3 * velocityH3Energy0At u b) +
        3 * velocityH3Energy3At u t := by
  have hAnti : AntitoneOn (velocityH3Energy0At u) (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3 hClass
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hKinetic : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    hAnti hb htClass (le_of_lt ht.1)
  have hEndpoint :=
    velocityH3EnergyAt_le_one_add_three_mul_energy0_add_energy3_on_h3Path
      hH3 hClass htClass
  linarith only [hEndpoint, hKinetic]

/-- Any terminal sequence with divergent physical E₃ eventually has
universal full/top energy coefficient `3 + epsilon`; the kinetic anchor
is used only in the proof, not in the resulting coefficient. -/
theorem h3PathCanonical_eventually_fullEnergy_le_three_add_epsilon_top
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hτT : Tendsto τ atTop (𝓝 T))
    (hτUpper : ∀ n : ℕ, τ n < T)
    (hTopT : Tendsto (fun n : ℕ => velocityH3Energy3At u (τ n))
      atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      velocityH3EnergyAt u (τ n) ≤
        (3 + ε) * velocityH3Energy3At u (τ n) := by
  let M : ℝ := (1 + 3 * velocityH3Energy0At u b) / ε
  have hTopLarge : ∀ᶠ n : ℕ in atTop,
      M ≤ velocityH3Energy3At u (τ n) :=
    (tendsto_atTop.1 hTopT) M
  have hLate : ∀ᶠ n : ℕ in atTop, b < τ n :=
    (tendsto_order.1 hτT).1 b hb.2
  filter_upwards [hTopLarge, hLate] with n hLarge hnLate
  have ht : τ n ∈ Set.Ioo b T := ⟨hnLate, hτUpper n⟩
  have hAnchor :=
    h3PathCanonical_fullEnergy_le_kineticAnchor_add_threeTop
      hH3 hClass hb ht
  have hScaled : ε * M ≤ ε * velocityH3Energy3At u (τ n) :=
    mul_le_mul_of_nonneg_left hLarge (le_of_lt hε)
  have hCancel : ε * M = 1 + 3 * velocityH3Energy0At u b := by
    dsimp only [M]
    field_simp [ne_of_gt hε] <;> ring
  have hSmall :
      1 + 3 * velocityH3Energy0At u b ≤
        ε * velocityH3Energy3At u (τ n) := by
    linarith only [hScaled, hCancel]
  calc
    velocityH3EnergyAt u (τ n) ≤
        (1 + 3 * velocityH3Energy0At u b) +
          3 * velocityH3Energy3At u (τ n) := hAnchor
    _ ≤ ε * velocityH3Energy3At u (τ n) +
          3 * velocityH3Energy3At u (τ n) :=
      add_le_add_left hSmall _
    _ = (3 + ε) * velocityH3Energy3At u (τ n) := by ring

/-- Turn the sharp universal full/top energy comparison into a uniform
positive lower bound on the physical top-order share E₃/E. -/
theorem h3PathCanonical_topShare_ge_inv_three_add_epsilon
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t ε : ℝ)
    (hε : 0 < ε)
    (hUpper : velocityH3EnergyAt u t ≤
      (3 + ε) * velocityH3Energy3At u t) :
    1 / (3 + ε) ≤
      velocityH3Energy3At u t / velocityH3EnergyAt u t := by
  have hE : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hCoeff : 0 < 3 + ε := by linarith only [hε]
  have hDivide : velocityH3EnergyAt u t / (3 + ε) ≤
      velocityH3Energy3At u t :=
    (div_le_iff₀ hCoeff).2 (by
      calc
        velocityH3EnergyAt u t ≤
            (3 + ε) * velocityH3Energy3At u t := hUpper
        _ = velocityH3Energy3At u t * (3 + ε) := by ring)
  apply (le_div_iff₀ hE).2
  calc
    (1 / (3 + ε)) * velocityH3EnergyAt u t =
        velocityH3EnergyAt u t / (3 + ε) := by ring
    _ ≤ velocityH3Energy3At u t := hDivide

/-- The original indexed directed signed-source witness, its exact physical
clocks, and its full gradient/velocity dichotomy all live on a terminal
sequence where E₃/E has the *universal* asymptotic lower share 1/3.
Precisely: every fixed epsilon > 0 supplies an eventual 1/(3+epsilon)
share bound on the SAME preselected sequence. -/
theorem h3PathCanonical_fixedDirectedSource_universalTopShare_withPhysicalAlternative
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
      Tendsto (fun n : ℕ => velocityH3Energy3At u (τ n)) atTop atTop ∧
      (∀ ε : ℝ, 0 < ε →
        (∀ᶠ n : ℕ in atTop,
          velocityH3Energy3At u (τ n) ≤ velocityH3EnergyAt u (τ n) ∧
          velocityH3EnergyAt u (τ n) ≤
            (3 + ε) * velocityH3Energy3At u (τ n) ∧
          1 / (3 + ε) ≤
            velocityH3Energy3At u (τ n) / velocityH3EnergyAt u (τ n))) ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (τ n)) ∧
      ((i = 0 ∧
          (∀ n : ℕ,
            h3PathCanonicalGradientFullDissipationBudgetAt u (τ n) (n : ℝ)) ∧
          (∀ᶠ n : ℕ in atTop,
            h3PathCanonicalGradientTopShareClockAt u T b (τ n) (n : ℝ))) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            ∀ n : ℕ,
              (n : ℝ) <
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
                  velocityH3EnergyAt u (τ n))) := by
  obtain ⟨i, τ, hWitness, hτT, hTopT, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_topShareClock_or_indexedSignedMonomial
      hH3 hNoExtension hClass hb
  refine ⟨i, τ, hWitness, hτT, hTopT, ?_, hClocks, hAlternative⟩
  intro ε hε
  have hUpper :=
    h3PathCanonical_eventually_fullEnergy_le_three_add_epsilon_top
      hH3 hClass hb hτT (fun n => (hWitness n).1.2) hTopT ε hε
  filter_upwards [hUpper] with n hn
  exact ⟨velocityH3Energy3At_le_velocityH3EnergyAt u (τ n), hn,
    h3PathCanonical_topShare_ge_inv_three_add_epsilon u (τ n) ε hε hn⟩

end
end Euclidean
end Bridge
end PrimeTensor
