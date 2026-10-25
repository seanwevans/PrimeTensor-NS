import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFourChannelDissipationLocalization244
import Mathlib.Tactic

/-!
# Fixed-frequency evacuation on the unified physical H³ dissipation witness

The four-channel theorem gives one sequence t_n -> T with the actual physical
H³ Fourier dissipation above the moving cutoff n+1 exceeding (n+1) times
the dissipation inside that cutoff.

This module proves a stronger and quantifier-clean consequence: on that SAME
sequence, the normalized viscous dissipation within EVERY fixed finite
frequency radius tends to zero. We do not reselect times for different radii.

The substantive new bridge is monotonicity of the true low-frequency
spectral dissipation integral in its radial cutoff. The remaining squeeze
is quantitative: for each fixed rho and all sufficiently large n,

  0 <= D_low(rho,t_n)/D(t_n) < 1/(n+2).

The final neutral alternative retains the possibility of a strong physical
kinetic L² terminal trace with exactly the canonical terminal kinetic mass.
No temporal integral lower bound, H³ continuation, or blowup conclusion is
inferred from these pointwise statements.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3FixedFrequencyDissipation244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3FixedFrequencyDissipation244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Low radial *physical* H³ Fourier dissipation is monotone in its cutoff.
The comparison uses positivity of the genuine spectral dissipation density
and monotonicity of restricted measure, not a pointwise spectral trace. -/
theorem h3Path_actualLowRadialDissipation_mono_radius244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    {ρ σ : ℝ} (hρσ : ρ ≤ σ) :
    h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      h3PathActualLowRadialDissipation244 σ
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  unfold h3PathActualLowRadialDissipation244
  rw [h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
  let G : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let f : H3FourierPoint3 → ℝ :=
    h3TerminalSpectralDissipationSingleDensity G
  have hSubset :
      h3TerminalRadialFrequencyBelow ρ ⊆
        h3TerminalRadialFrequencyBelow σ := by
    intro ξ hξ
    change h3FourierGradientMagnitude ξ < ρ at hξ
    change h3FourierGradientMagnitude ξ < σ
    exact lt_of_lt_of_le hξ hρσ
  have hMeasure :
      (volume : Measure H3FourierPoint3).restrict
          (h3TerminalRadialFrequencyBelow ρ) ≤
        (volume : Measure H3FourierPoint3).restrict
          (h3TerminalRadialFrequencyBelow σ) :=
    Measure.restrict_mono hSubset le_rfl
  have hInt : Integrable f volume := by
    dsimp only [f, G]
    exact h3TerminalSpectralDissipationSingleDensity_integrable
      hH3 hClass ht
  have hNonneg :
      0 ≤ᵐ[(volume : Measure H3FourierPoint3).restrict
        (h3TerminalRadialFrequencyBelow σ)] f := by
    exact Filter.Eventually.of_forall (fun ξ => by
      dsimp only [f]
      exact h3TerminalSpectralDissipationSingleDensity_nonneg G ξ)
  have hIntSigma : Integrable f
      ((volume : Measure H3FourierPoint3).restrict
        (h3TerminalRadialFrequencyBelow σ)) :=
    hInt.mono_measure Measure.restrict_le_self
  exact integral_mono_measure hMeasure hNonneg hIntSigma

/-- Abstract fixed-radius consequence of a single moving-radius dissipation
witness. For every finite fixed radius, the low-frequency fraction tends to
zero on the SAME chosen times; the witness is not reselected by radius. -/
theorem h3Path_movingDissipationDominance_forces_allFixedLowShares_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hDom : ∀ n : ℕ,
      ((n : ℝ) + 1) *
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) <
        h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n))) :
    ∀ ρ : ℝ, 0 ≤ ρ →
      Tendsto (fun n : ℕ =>
        h3PathActualLowRadialDissipation244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) /
        velocityH3DissipationAt u (τ n)) atTop (𝓝 0) := by
  let L : ℕ → ℝ := fun n =>
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 (τ n))
  let H : ℕ → ℝ := fun n =>
    h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 (τ n))
  let D : ℕ → ℝ := fun n => velocityH3DissipationAt u (τ n)
  have hLowNonneg (n : ℕ) : 0 ≤ L n := by
    dsimp only [L, h3PathActualLowRadialDissipation244]
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg
      (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ξ
  have hDom' (n : ℕ) : ((n : ℝ) + 1) * L n < H n := hDom n
  have hPartition (n : ℕ) : L n + H n = D n := by
    dsimp only [L, H, D]
    exact h3Path_actualRadialDissipation_partition244
      hH3 hClass (τ n) (hτ n) ((n : ℝ) + 1)
  have hDPos (n : ℕ) : 0 < D n := by
    rw [← hPartition n]
    exact (h3Path_highDissipationDominance_lowShare_bound244
      ((n : ℝ) + 1) (L n) (H n) (by positivity)
      (hLowNonneg n) (hDom' n)).1
  have hMovingLowShare (n : ℕ) :
      L n / D n < 1 / ((n : ℝ) + 2) := by
    have hShare := (h3Path_highDissipationDominance_lowShare_bound244
      ((n : ℝ) + 1) (L n) (H n) (by positivity)
      (hLowNonneg n) (hDom' n)).2.2
    rw [← hPartition n]
    simpa only [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
      using hShare
  intro ρ hρ
  let F : ℕ → ℝ := fun n =>
    h3PathActualLowRadialDissipation244 ρ
      (h3AuditActualSpectralVelocityTotal hH3 (τ n))
  have hFNonneg (n : ℕ) : 0 ≤ F n := by
    dsimp only [F, h3PathActualLowRadialDissipation244]
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg
      (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ξ
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ρ
  have hEventuallyBound : ∀ᶠ n in (atTop : Filter ℕ),
      ‖F n / D n‖ ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hCutoff : ρ ≤ (n : ℝ) + 1 := by
      linarith only [hN, hCast]
    have hMono : F n ≤ L n := by
      dsimp only [F, L]
      exact h3Path_actualLowRadialDissipation_mono_radius244
        hH3 hClass (τ n) (hτ n) hCutoff
    have hRatioNonneg : 0 ≤ F n / D n :=
      div_nonneg (hFNonneg n) (hDPos n).le
    have hRatioLe : F n / D n ≤ L n / D n :=
      (div_le_div_iff₀ (hDPos n) (hDPos n)).2
        (mul_le_mul_of_nonneg_right hMono (hDPos n).le)
    have hR : 0 < (n : ℝ) + 1 := by positivity
    have hDen : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
    have hInv : (1 : ℝ) / ((n : ℝ) + 2) ≤
        1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hR hDen
    rw [Real.norm_eq_abs, abs_of_nonneg hRatioNonneg]
    exact le_trans (le_trans hRatioLe (le_of_lt (hMovingLowShare n))) hInv
  have hInverse : Tendsto (fun n : ℕ =>
      (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun n : ℕ => F n / D n) atTop (𝓝 0)
  exact (tendsto_iff_norm_sub_tendsto_zero).2
    (by simpa only [sub_zero] using
      (squeeze_zero'
        (Filter.Eventually.of_forall (fun n => norm_nonneg (F n / D n)))
        hEventuallyBound hInverse))

/-- No strong physical kinetic terminal L² trace, together with positive
canonical terminal kinetic mass, forces evacuation of all fixed-frequency
fractions of the physical H³ dissipation along ONE common sequence. -/
theorem h3Path_physicalNoL2Trace_forces_fixedFrequencyDissipationEvacuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) *
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) <
        h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
      (∀ ρ : ℝ, 0 ≤ ρ →
        Tendsto (fun n : ℕ =>
          h3PathActualLowRadialDissipation244 ρ
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) /
          velocityH3DissipationAt u (τ n)) atTop (𝓝 0)) := by
  obtain ⟨τ, hτ, hNear, hLimit, hDom, _hHighShare⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialDissipationLocalization244
      hH3 hClass hL hNoTrace
  exact ⟨τ, hτ, hNear, hLimit, hDom,
    h3Path_movingDissipationDominance_forces_allFixedLowShares_zero244
      hH3 hClass τ hτ hDom⟩

/-- Unconditional-in-path endpoint alternative (within admissibility):
exact-mass strong kinetic L² trace, or all fixed Fourier balls carry
asymptotically zero fractions of physical H³ dissipation on a common
strict-time terminal sequence. This is not a time-integrated statement. -/
theorem h3Path_physicalL2Trace_or_fixedFrequencyDissipationEvacuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U) ∧
      ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T) ∨
    (∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ ρ : ℝ, 0 ≤ ρ →
        Tendsto (fun n : ℕ =>
          h3PathActualLowRadialDissipation244 ρ
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) /
          velocityH3DissipationAt u (τ n)) atTop (𝓝 0))) := by
  rcases h3Path_physicalL2Trace_or_highRadialDissipationLocalization244
      hH3 hClass with hTrace | hEscape
  · exact Or.inl hTrace
  · right
    obtain ⟨τ, hτ, hNear, hLimit, hDom, _hHighShare⟩ := hEscape
    exact ⟨τ, hτ, hNear, hLimit,
      h3Path_movingDissipationDominance_forces_allFixedLowShares_zero244
        hH3 hClass τ hτ hDom⟩

end
end PrimeTensor.FirstMonomialTriad
