import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalHighRadialViscousCoercivity
import Mathlib.Tactic

/-!
# One physical terminal sequence of quadratic radial viscous concentration

The previously closed unconditional low-band H³ terminal theorem proves that
failure of the strong weighted H³ terminal trace forces a single positive
high-frequency threshold beyond every radius, at arbitrarily late times.
The exact physical high-radial viscous coercivity converts that into one
terminal sequence with lower bound epsilon² (n+1)² for BOTH the high-radial
and full physical H³ dissipation. Every fixed high-radial cutoff diverges
along that same sequence by monotonicity of the genuine Fourier dissipation.

This gives an instantaneous viscous obstruction, not a claim that the time
integral of dissipation is infinite: the high spikes may have shrinking widths.
No lower bound on width or endpoint H³ regularity is assumed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeTerminalViscousEscapeDiagonal244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact quadratic Fourier radius cost grows without bound for every
fixed positive high-frequency mass threshold. -/
theorem thirdFullPositiveRadialQuadratic_tendsto_atTop244
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * ε ^ 2) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  obtain ⟨N, hN⟩ := exists_nat_gt (M / ε ^ 2)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hM : M < (N : ℝ) * ε ^ 2 :=
    (div_lt_iff₀ (pow_pos hε 2)).mp hN
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hSq : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  calc
    M ≤ (N : ℝ) * ε ^ 2 := hM.le
    _ ≤ (n : ℝ) * ε ^ 2 :=
      mul_le_mul_of_nonneg_right hCast (sq_nonneg ε)
    _ ≤ ((n : ℝ) + 1) ^ 2 * ε ^ 2 :=
      mul_le_mul_of_nonneg_right hSq (sq_nonneg ε)

/-- If the actual weighted H³ solution has no strong terminal trace, a
SINGLE terminal sequence has a FIXED positive highpass norm threshold at
radius n+1. Both its high-radial and full physical viscous heights exceed
that threshold squared times (n+1)².

The times depend on n; no lower bound on their separation or duration is
asserted. No physical kinetic L² nontrace premise is used. -/
theorem thirdFullPhysical_noH3Trace_quadraticViscousDiagonal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo b T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) ^ 2 * ε ^ 2 ≤
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) ^ 2 * ε ^ 2 ≤
          velocityH3DissipationAt u (τ n)) := by
  classical
  obtain ⟨ε, hε, hEscape⟩ :=
    (thirdFullPhysical_noH3Trace_iff_cofinalHighRadialEscape244
      hH3 hClass b hb).mp hNoTrace
  have hWitness (n : ℕ) :
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        T - t < (1 : ℝ) / ((n : ℝ) + 1) ∧
        ε ≤ ‖thirdFullSpectralVelocityHighRadialApply244 n
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ :=
    hEscape n ((1 : ℝ) / ((n : ℝ) + 1)) (by positivity)
  choose τ hτ hNear hTail using hWitness
  have hDist (n : ℕ) :
      dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1) := by
    simpa only [Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (hτ n).2.le), neg_sub] using hNear n
  have hLimit : Tendsto τ atTop (𝓝 T) := by
    apply Metric.tendsto_atTop.2
    intro η hη
    have hRadius : Tendsto
        (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hEvent : ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) / ((n : ℝ) + 1) < η :=
      hRadius.eventually (eventually_lt_nhds hη)
    rw [Filter.eventually_atTop] at hEvent
    obtain ⟨N, hN⟩ := hEvent
    exact ⟨N, fun n hn => (hDist n).trans (hN n hn)⟩
  have hStrength (n : ℕ) :
      ((n : ℝ) + 1) ^ 2 * ε ^ 2 ≤
      ((n : ℝ) + 1) ^ 2 *
        ‖thirdFullSpectralVelocityHighRadialApply244 n
          (h3AuditActualSpectralVelocityTotal hH3 (τ n))‖ ^ 2 := by
    have hSq : ε ^ 2 ≤
        ‖thirdFullSpectralVelocityHighRadialApply244 n
          (h3AuditActualSpectralVelocityTotal hH3 (τ n))‖ ^ 2 :=
      (sq_le_sq₀ hε.le (norm_nonneg _)).mpr (hTail n)
    exact mul_le_mul_of_nonneg_left hSq (sq_nonneg _)
  refine ⟨ε, hε, τ, hτ, hDist, hLimit, ?_, ?_⟩
  · intro n
    have ht : τ n ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hτ n).1, (hτ n).2⟩
    exact (hStrength n).trans
      (thirdFullPhysical_highRadialViscousCoercivity244
        hH3 hClass (τ n) ht n)
  · intro n
    have ht : τ n ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hτ n).1, (hτ n).2⟩
    exact (hStrength n).trans
      (thirdFullPhysical_fullViscousCoercivity244
        hH3 hClass (τ n) ht n)

/-- The SAME actual terminal sequence has divergent full physical H³
viscosity and divergent high-radial H³ viscosity at EVERY fixed radius.
The common sequence is independent of the fixed frequency cutoff. -/
theorem thirdFullPhysical_noH3Trace_allFixedViscousDivergenceDiagonal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo b T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3DissipationAt u (τ n)) atTop atTop ∧
      (∀ σ : ℝ,
        Tendsto (fun n : ℕ =>
          h3PathActualHighRadialDissipation244 σ
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) atTop atTop) := by
  obtain ⟨ε, hε, τ, hτ, _hNear, hLimit, hHigh, hFull⟩ :=
    thirdFullPhysical_noH3Trace_quadraticViscousDiagonal244
      hH3 hClass b hb hNoTrace
  have hGrowth := thirdFullPositiveRadialQuadratic_tendsto_atTop244 ε hε
  refine ⟨τ, hτ, hLimit, ?_, ?_⟩
  · exact tendsto_atTop_mono hFull hGrowth
  · intro σ
    have hCutoff : ∀ᶠ n : ℕ in atTop, σ ≤ (n : ℝ) + 1 := by
      obtain ⟨N, hN⟩ := exists_nat_gt σ
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith only [hN, hNn]
    apply Filter.tendsto_atTop.2
    intro M
    have hLarge : ∀ᶠ n : ℕ in atTop,
        M ≤ ((n : ℝ) + 1) ^ 2 * ε ^ 2 :=
      hGrowth.eventually (eventually_ge_atTop M)
    filter_upwards [hCutoff, hLarge] with n hσ hM
    have ht : τ n ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hτ n).1, (hτ n).2⟩
    have hMono := h3Path_actualHighRadialDissipation_antitone_radius244
      hH3 hClass (τ n) ht hσ
    exact ((hM.trans (hHigh n))).trans hMono

/-- Failure of the strong H³ trace forces arbitrarily large ACTUAL physical
H³ viscous heights inside every strict terminal neighborhood. This does not
say that the time integral of these spikes diverges. -/
theorem thirdFullPhysical_noH3Trace_cofinalFullViscousSpikes244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) :
    ∀ M δ : ℝ, 0 < δ →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ T - t < δ ∧
        M < velocityH3DissipationAt u t := by
  obtain ⟨ε, hε, τ, hτ, hDist, _hLimit, _hHigh, hFull⟩ :=
    thirdFullPhysical_noH3Trace_quadraticViscousDiagonal244
      hH3 hClass b hb hNoTrace
  have hGrowth := thirdFullPositiveRadialQuadratic_tendsto_atTop244 ε hε
  intro M δ hδ
  have hRadius : Tendsto
      (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hNear : ∀ᶠ n : ℕ in atTop, T - τ n < δ := by
    have hEvent : ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) / ((n : ℝ) + 1) < δ :=
      hRadius.eventually (eventually_lt_nhds hδ)
    filter_upwards [hEvent] with n hn
    have hEq : dist (τ n) T = T - τ n := by
      simp only [Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr (hτ n).2.le), neg_sub]
    linarith only [hDist n, hn, hEq]
  have hBig : ∀ᶠ n : ℕ in atTop,
      M + 1 ≤ velocityH3DissipationAt u (τ n) := by
    have hEvent : ∀ᶠ n : ℕ in atTop,
        M + 1 ≤ ((n : ℝ) + 1) ^ 2 * ε ^ 2 :=
      hGrowth.eventually (eventually_ge_atTop (M + 1))
    filter_upwards [hEvent] with n hn
    exact hn.trans (hFull n)
  obtain ⟨n, hnNear, hnBig⟩ := (hNear.and hBig).exists
  exact ⟨τ n, hτ n, hnNear, by linarith only [hnBig]⟩

/-- An eventual bound on the genuine full H³ viscous density is a sufficient
criterion for a strong H³ spectral endpoint trace. No terminal kinetic L²
trace, uniform Fourier moment, or extra temporal-joint-continuity premise. -/
theorem thirdFullPhysical_terminalH3Trace_of_boundedFullViscousTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hBound : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo b T →
      velocityH3DissipationAt u t ≤ M) :
    ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L) := by
  classical
  by_contra hNoTrace
  obtain ⟨M, hM⟩ := hBound
  obtain ⟨t, ht, _htNear, hSpike⟩ :=
    thirdFullPhysical_noH3Trace_cofinalFullViscousSpikes244
      hH3 hClass b hb hNoTrace M (T - b) (sub_pos.mpr hb.2)
  exact (not_lt_of_ge (hM t ht)) hSpike

/-- The resulting Navier–Stokes endpoint alternative: either the weighted
H³ velocity has a terminal trace or the physical H³ viscous density has
cofinally unbounded instantaneous heights on every strict tail. -/
theorem thirdFullPhysical_terminalH3Trace_or_cofinalFullViscousSpikes244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    (∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) ∨
    (∀ M δ : ℝ, 0 < δ →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ T - t < δ ∧
        M < velocityH3DissipationAt u t) := by
  classical
  by_cases hTrace : ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)
  · exact Or.inl hTrace
  · exact Or.inr
      (thirdFullPhysical_noH3Trace_cofinalFullViscousSpikes244
        hH3 hClass b hb hTrace)

end
end PrimeTensor.FirstMonomialTriad
