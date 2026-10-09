import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceCubicRateCeiling

/-!
# Terminal kinetic-limit optimization of the full H³ cubic clock

The anchored physical clock is C_b R(t), where
  C_b = 3 K² (E₀(b)+1),  R(t)=(T-t)² (D(t)/E(t))³.

Suppose, as an additional explicit hypothesis, that the genuine zeroth-order
kinetic energy has a finite terminal left limit L≥0. The anchored coefficient
then converges to the physically terminal coefficient
  C_* = 3 K² (L+1)>0.

For hypothetical nonextension, the already proved anchored sharp threshold
for EVERY fixed anchor can be transferred to this terminal coefficient:
  for every q<1, eventually q≤C_* R(t).

This does NOT claim eventual C_* R(t)≥1, nor that a terminal kinetic limit
exists without the stated assumption. A subcritical ceiling C_* B<1 implies
smooth continuation, including when the rate ceiling is available only on a
preselected terminal sequence. The fixed ten-source witness retains both
signed-source branches and all three physical critical clocks.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Cubic physical-clock coefficient corresponding to a terminal kinetic
energy limit `L` rather than an anchored kinetic observation `E₀(b)`. -/
noncomputable def h3PathCanonicalKineticLimitCubicCoefficient
    (L : ℝ) : ℝ :=
  3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 * (L + 1)

/-- If the kinetic energy converges at the terminal time, then the fixed
kinetic coefficients converge to the coefficient built from its limit. -/
theorem h3PathCanonical_kineticCoefficient_tendsto_terminalLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T L : ℝ}
    (hLimit : Tendsto (velocityH3Energy0At u) (𝓝[<] T) (𝓝 L)) :
    Tendsto (h3PathCanonicalKineticCubicCoefficientAt u)
      (𝓝[<] T) (𝓝 (h3PathCanonicalKineticLimitCubicCoefficient L)) := by
  have hContinuous : ContinuousAt
      (fun x : ℝ => 3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 * (x + 1)) L := by
    fun_prop
  change Tendsto
    (fun b : ℝ => 3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (velocityH3Energy0At u b + 1))
    (𝓝[<] T)
    (𝓝 (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 * (L + 1)))
  simpa only [Function.comp_def] using hContinuous.tendsto.comp hLimit

/-- A nonnegative finite kinetic limit has a strictly positive limiting
clock coefficient; the Riccati coefficient and kinetic offset are positive. -/
theorem h3PathCanonical_kineticLimitCubicCoefficient_pos
    (L : ℝ) (hL : 0 ≤ L) :
    0 < h3PathCanonicalKineticLimitCubicCoefficient L := by
  unfold h3PathCanonicalKineticLimitCubicCoefficient
  have hK := h3PathSqrtEnergyRiccatiCoefficient_pos
  have hLPlus : 0 < L + 1 := by linarith only [hL]
  positivity

/-- If the terminal kinetic-limit coefficient multiplied by a proposed
cubic-rate ceiling is strictly subcritical, some real kinetic anchor already
has a strictly subcritical coefficient. No monotonicity assumption is used. -/
theorem h3PathCanonical_exists_subcritical_kineticAnchor_of_limit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a L B : ℝ}
    (haT : a < T)
    (hLimit : Tendsto (velocityH3Energy0At u) (𝓝[<] T) (𝓝 L))
    (hStrict : h3PathCanonicalKineticLimitCubicCoefficient L * B < 1) :
    ∃ b : ℝ, b ∈ Set.Ioo a T ∧
      h3PathCanonicalKineticCubicCoefficientAt u b * B < 1 := by
  have hContinuous : ContinuousAt
      (fun x : ℝ =>
        (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 * (x + 1)) * B) L := by
    fun_prop
  have hProduct : Tendsto
      (fun b : ℝ => h3PathCanonicalKineticCubicCoefficientAt u b * B)
      (𝓝[<] T)
      (𝓝 (h3PathCanonicalKineticLimitCubicCoefficient L * B)) := by
    change Tendsto
      (fun b : ℝ =>
        (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (velocityH3Energy0At u b + 1)) * B)
      (𝓝[<] T)
      (𝓝 ((3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 * (L + 1)) * B))
    simpa only [Function.comp_def] using hContinuous.tendsto.comp hLimit
  have hNear : ∀ᶠ b : ℝ in 𝓝[<] T,
      h3PathCanonicalKineticCubicCoefficientAt u b * B < 1 :=
    hProduct.eventually (Iio_mem_nhds hStrict)
  have hAnchors : ∀ᶠ b : ℝ in 𝓝[<] T, b ∈ Set.Ioo a T :=
    Ioo_mem_nhdsLT haT
  obtain ⟨b, hb, hB⟩ := (hAnchors.and hNear).exists
  exact ⟨b, hb, hB⟩

/-- An eventual physical cubic-rate ceiling strictly below the terminal
kinetic-limit threshold implies smooth H³ continuation. The existence of the
finite kinetic limit is a separate explicit hypothesis. -/
theorem h3PathCanonical_smoothExtension_of_terminalKineticLimit_rateCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a L B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hLimit : Tendsto (velocityH3Energy0At u) (𝓝[<] T) (𝓝 L))
    (hRate : ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalFullCubicRateAt u T t ≤ B)
    (hStrict : h3PathCanonicalKineticLimitCubicCoefficient L * B < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  obtain ⟨b, hb, hAnchor⟩ :=
    h3PathCanonical_exists_subcritical_kineticAnchor_of_limit
      hClass.terminal_start.2 hLimit hStrict
  exact h3PathCanonical_smoothExtension_of_subcritical_fullCubicRateCeiling
    hH3 hClass hb B hRate hAnchor

/-- The limit-optimized subcritical continuation test also works along an
arbitrary, already chosen, left-terminal sequence rather than a newly
selected witness. -/
theorem h3PathCanonical_smoothExtension_of_terminalKineticLimit_sequenceRateCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a L B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hLimit : Tendsto (velocityH3Energy0At u) (𝓝[<] T) (𝓝 L))
    (tau : ℕ → ℝ)
    (hTau : Tendsto tau atTop (𝓝[<] T))
    (hRate : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalFullCubicRateAt u T (tau n) ≤ B)
    (hStrict : h3PathCanonicalKineticLimitCubicCoefficient L * B < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  obtain ⟨b, hb, hAnchor⟩ :=
    h3PathCanonical_exists_subcritical_kineticAnchor_of_limit
      hClass.terminal_start.2 hLimit hStrict
  exact h3PathCanonical_smoothExtension_of_sequence_subcritical_fullCubicRateCeiling
    hH3 hClass hb tau hTau B hRate hAnchor

/-- A finite nonnegative kinetic terminal limit sharpens the conditional
nonextension cubic clock: its terminal coefficient inherits the entire
family of strict subunit lower thresholds, even though no fixed anchor
actually realizes the limiting coefficient. -/
theorem h3PathCanonical_terminalKineticLimit_sharpCubicClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a L : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hLimit : Tendsto (velocityH3Energy0At u) (𝓝[<] T) (𝓝 L))
    (hL : 0 ≤ L)
    (q : ℝ) (hq : q < 1) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      q ≤ h3PathCanonicalKineticLimitCubicCoefficient L *
        h3PathCanonicalFullCubicRateAt u T t := by
  let C : ℝ := h3PathCanonicalKineticLimitCubicCoefficient L
  have hC : 0 < C :=
    h3PathCanonical_kineticLimitCubicCoefficient_pos L hL
  have hQ : q * C < C := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hq hC
  have hContinuous : ContinuousAt
      (fun x : ℝ => q * (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 * (x + 1))) L := by
    fun_prop
  have hNearby : ∀ᶠ b : ℝ in 𝓝[<] T,
      q * h3PathCanonicalKineticCubicCoefficientAt u b < C := by
    have hTend : Tendsto
        (fun b : ℝ => q * h3PathCanonicalKineticCubicCoefficientAt u b)
        (𝓝[<] T) (𝓝 (q * C)) := by
      change Tendsto
        (fun b : ℝ => q * (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (velocityH3Energy0At u b + 1)))
        (𝓝[<] T)
        (𝓝 (q * (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 * (L + 1))))
      simpa only [Function.comp_def] using hContinuous.tendsto.comp hLimit
    exact hTend.eventually (Iio_mem_nhds hQ)
  have hAnchors : ∀ᶠ b : ℝ in 𝓝[<] T,
      b ∈ Set.Ioo a T := Ioo_mem_nhdsLT hClass.terminal_start.2
  obtain ⟨b, hb, hAnchor⟩ := (hAnchors.and hNearby).exists
  let Cb : ℝ := h3PathCanonicalKineticCubicCoefficientAt u b
  have hCbPos : 0 < Cb := by
    dsimp only [Cb]
    unfold h3PathCanonicalKineticCubicCoefficientAt
    have hK := h3PathSqrtEnergyRiccatiCoefficient_pos
    have hE0 := velocityH3Energy0At_nonneg u b
    positivity
  let r : ℝ := q * Cb / C
  have hr : r < 1 := by
    have hInequality : q * Cb < 1 * C := by
      simpa only [one_mul, Cb] using hAnchor
    exact (div_lt_iff₀ hC).2 hInequality
  have hFloor :=
    h3PathCanonical_fullCubicTerminalClock_eventually_ge_subunit
      hH3 hNoExtension hClass hb r hr
  filter_upwards [hFloor] with t ht
  have hFloorAt : r ≤ Cb * h3PathCanonicalFullCubicRateAt u T t := by
    simpa only [h3PathCanonical_fullCubicClock_eq_coefficient_mul_rate, Cb]
      using ht
  have hProduct := mul_le_mul_of_nonneg_right hFloorAt hC.le
  have hCancel : r * C = q * Cb := by
    dsimp only [r]
    exact div_mul_cancel₀ (q * Cb) (ne_of_gt hC)
  have hScaled : q * Cb ≤
      (C * h3PathCanonicalFullCubicRateAt u T t) * Cb := by
    calc
      q * Cb = r * C := hCancel.symm
      _ ≤ (Cb * h3PathCanonicalFullCubicRateAt u T t) * C := hProduct
      _ = (C * h3PathCanonicalFullCubicRateAt u T t) * Cb := by ring
  exact (mul_le_mul_iff_of_pos_right hCbPos).mp hScaled


/-- The original fixed directed-source index and physical clock witness also
carry the limiting-coefficient sharp cubic floor. The additional kinetic-limit
hypothesis changes no adverse signed-monomial or gradient alternatives. -/
theorem h3PathCanonical_fixedDirectedSource_kineticLimitSharpCubicClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b L : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hLimit : Tendsto (velocityH3Energy0At u) (𝓝[<] T) (𝓝 L))
    (hL : 0 ≤ L) :
    ∃ (i : Fin 10) (tau : ℕ → ℝ),
      (∀ n : ℕ,
        tau n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          h3PathCanonicalJointDirectedTenSourceAt u (tau n) i /
            (9 * velocityH3EnergyAt u (tau n))) ∧
      Tendsto tau atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3Energy3At u (tau n)) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalFullToTopPhysicalLengthRatioAt u (tau n))
        atTop (𝓝 1) ∧
      (∀ q : ℝ, q < 1 →
        ∀ᶠ n : ℕ in atTop,
          q ≤ h3PathCanonicalKineticLimitCubicCoefficient L *
            h3PathCanonicalFullCubicRateAt u T (tau n)) ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (tau n)) ∧
      ((i = 0 ∧
          (∀ n : ℕ,
            h3PathCanonicalGradientFullDissipationBudgetAt u (tau n) (n : ℝ)) ∧
          (∀ᶠ n : ℕ in atTop,
            h3PathCanonicalGradientTopShareClockAt u T b (tau n) (n : ℝ))) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            ∀ n : ℕ,
              (n : ℝ) <
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (tau n) j r) /
                  velocityH3EnergyAt u (tau n))) := by
  obtain ⟨i, tau, hWitness, hTauT, hTopT, hLengthRatioT,
    _hAnchoredClock, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_sharpCubicClock_withPhysicalAlternative
      hH3 hNoExtension hClass hb
  have hTauLT : Tendsto tau atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hTauT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hSharp : ∀ q : ℝ, q < 1 →
      ∀ᶠ n : ℕ in atTop,
        q ≤ h3PathCanonicalKineticLimitCubicCoefficient L *
          h3PathCanonicalFullCubicRateAt u T (tau n) := by
    intro q hq
    exact hTauLT.eventually
      (h3PathCanonical_terminalKineticLimit_sharpCubicClock
        hH3 hNoExtension hClass hLimit hL q hq)
  exact ⟨i, tau, hWitness, hTauT, hTopT, hLengthRatioT,
    hSharp, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
