import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSpectralDissipationGap

/-!
# Unbounded canonical spectral shortfall on a hypothetical terminal branch

The committed spectral gap bounds the exact signed transport margin excess,
but the commutator bound need not be sharp. Its zero-margin expression is

  max 0 (4422 + 4422*C1*sqrt(E) - 2*D/E).

Remove the fixed `4422` baseline to define the normalized nonlinear spectral
shortfall `S = 4422*C1*sqrt(E) - 2*D/E`. Hypothetical nonextension forces `S`
above every real threshold arbitrarily close to the terminal time. At any
positive kinetic anchor those witnesses can be exactly direct-selected, and
one explicit physical-clock sequence witnesses `S -> +infinity`.

This is a necessary consequence of hypothetical nonextension, not a proof
that the actual nonlinear transport saturates its commutator upper bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The normalized difference between the square-root-energy commutator term
and the full `2D/E` dissipation rate, with the constant `4422` removed. -/
noncomputable def h3PathCanonicalNonlinearDissipationShortfall
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) : ℝ → ℝ :=
  fun t => 4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
    Real.sqrt (velocityH3EnergyAt u t) -
    2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t

/-- Zero-margin spectral gap is exactly the positive part of the constant
transport baseline plus the normalized nonlinear dissipation shortfall. -/
theorem h3PathCanonical_spectralGap_zero_eq_shortfall
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    h3PathCanonicalSpectralDissipationGap u 0 t =
      max 0 (4422 + h3PathCanonicalNonlinearDissipationShortfall u t) := by
  have hProd : 0 ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t) :=
    mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  unfold h3PathCanonicalSpectralDissipationGap
    h3PathCanonicalNonlinearDissipationShortfall
  simp only [h3PathCanonicalKineticTransportCoefficient,
    h3PathCanonicalSqrtEnergyGradientEnvelope, abs_of_nonneg hProd,
    sub_zero]
  congr 1
  ring

/-- Exceeding the baseline plus a nonnegative target in the spectral gap
forces the baseline-free nonlinear shortfall above the original target. -/
theorem h3PathCanonical_shortfall_gt_of_spectralGap_large
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (M t : ℝ)
    (hGap : 4422 + max M 0 <
      h3PathCanonicalSpectralDissipationGap u 0 t) :
    M < h3PathCanonicalNonlinearDissipationShortfall u t := by
  rw [h3PathCanonical_spectralGap_zero_eq_shortfall] at hGap
  have hMNonneg : 0 ≤ max M 0 := le_max_right _ _
  have hThreshold : 0 ≤ (4422 : ℝ) + max M 0 := by linarith
  have hRaw : 4422 + max M 0 <
      4422 + h3PathCanonicalNonlinearDissipationShortfall u t := by
    by_contra hNot
    have hLe : 4422 + h3PathCanonicalNonlinearDissipationShortfall u t ≤
        4422 + max M 0 := le_of_not_gt hNot
    have hMax : max (0 : ℝ)
        (4422 + h3PathCanonicalNonlinearDissipationShortfall u t) ≤
          4422 + max M 0 := max_le hThreshold hLe
    exact (not_lt_of_ge hMax) hGap
  have hM : M ≤ max M 0 := le_max_left _ _
  linarith

/-- Without any positive kinetic-anchor premise, hypothetical nonextension
forces the nonlinear spectral dissipation shortfall arbitrarily high on
every strict terminal tail. -/
theorem h3PathCanonical_shortfall_arbitrarily_large_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      M < h3PathCanonicalNonlinearDissipationShortfall u t := by
  have hr : IntegrableOn (fun _ : ℝ => (4422 : ℝ) + max M 0)
      (Set.Ioo d T) := integrableOn_const measure_Ioo_lt_top.ne
  obtain ⟨t, ht, hGap⟩ :=
    h3PathCanonicalSpectralDissipationGap_exceeds_integrable_envelope
      (fun _ : ℝ => (4422 : ℝ) + max M 0)
      hH3 hNoExtension hClass hd (le_refl (0 : ℝ)) hr
  exact ⟨t, ht, h3PathCanonical_shortfall_gt_of_spectralGap_large u M t hGap⟩

/-- At each positive kinetic anchor the arbitrarily large normalized
spectral shortfall can be witnessed on the exact direct branch, with
zero selected absorption. -/
theorem h3PathCanonical_shortfall_arbitrarily_large_in_direct_regime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hd : d ∈ Set.Ioo a T) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t =
          h3PathCanonicalKineticTransportCoefficient u t ∧
      h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t = 0 ∧
      M < h3PathCanonicalNonlinearDissipationShortfall u t := by
  have hr : IntegrableOn (fun _ : ℝ => (4422 : ℝ) + max M 0)
      (Set.Ioo d T) := integrableOn_const measure_Ioo_lt_top.ne
  obtain ⟨t, ht, hDirect, hAbsorbed, hGap⟩ :=
    h3PathCanonicalSpectralDissipationGap_exceeds_envelope_in_direct_regime
      (fun _ : ℝ => (4422 : ℝ) + max M 0)
      hH3 hNoExtension hClass hMass hd (le_refl (0 : ℝ)) hr
  exact ⟨t, ht, hDirect, hAbsorbed,
    h3PathCanonical_shortfall_gt_of_spectralGap_large u M t hGap⟩

/-- The normalized spectral shortfall diverges on a chosen explicit terminal
physical-clock sequence while canonical direct selection is exact. -/
theorem h3PathCanonical_exists_direct_shortfall_blowup_sequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∃ σ : ℕ → ℝ,
      (∀ n : ℕ,
        σ n ∈ Set.Ioo a T ∧
        σ n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) =
            h3PathCanonicalKineticTransportCoefficient u (σ n) ∧
        h3ExactAdaptiveSelectedAbsorbedCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) = 0 ∧
        (n : ℝ) < h3PathCanonicalNonlinearDissipationShortfall u (σ n)) ∧
      Tendsto σ atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalNonlinearDissipationShortfall u (σ n)) atTop atTop := by
  classical
  let m : ℝ := h3BKMKineticTailMidpoint a T
  have hm : m ∈ Set.Ioo a T :=
    h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2
  have hChoice : ∀ n : ℕ, ∃ t : ℝ,
      t ∈ Set.Ioo a T ∧
      t ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
      h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t =
          h3PathCanonicalKineticTransportCoefficient u t ∧
      h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t = 0 ∧
      (n : ℝ) < h3PathCanonicalNonlinearDissipationShortfall u t := by
    intro n
    let δ : ℝ := (1 : ℝ) / ((n : ℝ) + 1)
    have hδ : 0 < δ := by dsimp only [δ]; positivity
    let d : ℝ := max m (T - δ)
    have hd : d ∈ Set.Ioo a T := by
      exact ⟨lt_of_lt_of_le hm.1 (le_max_left _ _),
        max_lt hm.2 (sub_lt_self T hδ)⟩
    obtain ⟨t, ht, hDirect, hAbsorbed, hLarge⟩ :=
      h3PathCanonical_shortfall_arbitrarily_large_in_direct_regime
        (n : ℝ) hH3 hNoExtension hClass hMass hd
    have htOld : t ∈ Set.Ioo a T :=
      ⟨lt_trans hd.1 ht.1, ht.2⟩
    have htNear : t ∈ Set.Ioo (T - δ) T :=
      ⟨lt_of_le_of_lt (le_max_right m (T - δ)) ht.1, ht.2⟩
    exact ⟨t, htOld, htNear, hDirect, hAbsorbed, hLarge⟩
  choose σ hσ using hChoice
  have hClock : Tendsto σ atTop (𝓝 T) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, ?_⟩
    intro n hn
    have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hDenN : 0 < (N : ℝ) + 1 := by positivity
    have hInvN : (1 : ℝ) / ((n : ℝ) + 1) ≤
        1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hDenN (by linarith)
    have hSmallN : 1 / ((N : ℝ) + 1) < ε := by
      have hInvEps : 1 / ε < (N : ℝ) := hN
      have hNPlus : 1 / ε < (N : ℝ) + 1 := by linarith
      have hMulRaw : 1 < ((N : ℝ) + 1) * ε :=
        (div_lt_iff₀ hε).1 hNPlus
      have hMul : 1 < ε * ((N : ℝ) + 1) := by
        simpa only [mul_comm] using hMulRaw
      exact (div_lt_iff₀ hDenN).2 (by simpa only [one_mul] using hMul)
    have hSmall : (1 : ℝ) / ((n : ℝ) + 1) < ε :=
      lt_of_le_of_lt hInvN hSmallN
    have hLower := (hσ n).2.1.1
    have hUpper := (hσ n).2.1.2
    rw [Real.dist_eq]
    have hDiffNonpos : σ n - T ≤ 0 := by linarith [hUpper]
    rw [abs_of_nonpos hDiffNonpos]
    linarith
  have hDiverges : Tendsto (fun n : ℕ =>
      h3PathCanonicalNonlinearDissipationShortfall u (σ n)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M
    filter_upwards [eventually_ge_atTop N] with n hn
    have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact le_of_lt (lt_of_lt_of_le hN (le_trans hCast (le_of_lt (hσ n).2.2.2.2)))
  exact ⟨σ, hσ, hClock, hDiverges⟩

/-- Neutral alternative: extension, or cofinally unbounded spectral transport
shortfall despite subtracting the full two copies of normalized dissipation. -/
theorem h3PathCanonical_extension_or_unbounded_nonlinear_shortfall
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ d : ℝ, d ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo d T ∧
        M < h3PathCanonicalNonlinearDissipationShortfall u t := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro d hd M
    exact h3PathCanonical_shortfall_arbitrarily_large_of_noExtension
      M hH3 hExt hClass hd

end Euclidean
end Bridge
end PrimeTensor
