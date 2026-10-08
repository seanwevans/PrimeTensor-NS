import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalClockWidthCluster

/-!
# Arbitrarily fast terminal selection of divergent actual H3 excess

A witness `n < q₀(tₙ)` inside `(T - 1/(n+1), T)` controls neither
`(T-tₙ) q₀(tₙ)` nor `(T-tₙ) sqrt(E(tₙ))` from below. The earlier exact
nonextension witness is available on *every* terminal interval. Hence its
physical times can be selected inside any user-prescribed positive widths
`δ n` without sacrificing the thresholds `n < q₀` and `n < S`.

When `δ n -> 0` and `n*δ n -> 0`, the selected physical times converge to
T and their indexed widths `n*(T-tₙ)` converge to zero. A compact
cancellation-share cluster survives a cofinal extraction. Thus the zero
indexed-width alternative is always selectable on the hypothetical
nonextension branch; a positive indexed-width cluster is not forced by
this witness-selection argument. These statements neither constrain the
*intrinsic* physical-time growth profile nor settle continuation/blowup.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- Positive, shrinking physical terminal windows force the chosen sample
times to converge to their common terminal endpoint. -/
theorem h3PathCanonical_terminalClock_tendsto_of_shrinking_windows
    {T : ℝ} {σ δ : ℕ → ℝ}
    (hNear : ∀ n : ℕ, σ n ∈ Set.Ioo (T - δ n) T)
    (hδ : Tendsto δ atTop (𝓝 (0 : ℝ))) :
    Tendsto σ atTop (𝓝 T) := by
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  have hNormUpper : ∀ n : ℕ, ‖σ n - T‖ ≤ δ n := by
    intro n
    have hLo := (hNear n).1
    have hHi := (hNear n).2
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hHi.le)]
    linarith only [hLo]
  exact squeeze_zero'
    (Filter.Eventually.of_forall (fun n => norm_nonneg (σ n - T)))
    (Filter.Eventually.of_forall hNormUpper) hδ

/-- If the allowed terminal width is small relative to the selected index,
then the indexed physical width converges to zero. -/
theorem h3PathCanonical_indexedWidth_tendsto_zero_of_fast_windows
    {T : ℝ} {σ δ : ℕ → ℝ}
    (hNear : ∀ n : ℕ, σ n ∈ Set.Ioo (T - δ n) T)
    (hScaled : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n : ℕ =>
      h3PathCanonicalIndexedTerminalWidth T n (σ n)) atTop (𝓝 (0 : ℝ)) := by
  have hLower : ∀ n : ℕ,
      0 ≤ h3PathCanonicalIndexedTerminalWidth T n (σ n) := by
    intro n
    unfold h3PathCanonicalIndexedTerminalWidth
    exact mul_nonneg (by positivity) (sub_pos.mpr (hNear n).2).le
  have hUpper : ∀ n : ℕ,
      h3PathCanonicalIndexedTerminalWidth T n (σ n) ≤ (n : ℝ) * δ n := by
    intro n
    have hLe : T - σ n ≤ δ n := by
      linarith only [(hNear n).1]
    unfold h3PathCanonicalIndexedTerminalWidth
    exact mul_le_mul_of_nonneg_left hLe (by positivity)
  exact squeeze_zero'
    (Filter.Eventually.of_forall hLower)
    (Filter.Eventually.of_forall hUpper) hScaled

/-- Nonextension admits actual-and-spectral excess witnesses with any
positive terminal-width gauge. A vanishing index-weighted gauge forces
a zero indexed-width cluster without any new PDE growth assumption. -/
theorem h3PathCanonical_exists_direct_excess_fastWidth_sequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {δ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hδPos : ∀ n : ℕ, 0 < δ n)
    (hδTop : Tendsto δ atTop (𝓝 (0 : ℝ)))
    (hδScaled : Tendsto (fun n : ℕ => (n : ℝ) * δ n)
      atTop (𝓝 (0 : ℝ))) :
    ∃ σ : ℕ → ℝ,
      (∀ n : ℕ,
        σ n ∈ Set.Ioo (T - δ n) T ∧
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) =
            h3PathCanonicalKineticTransportCoefficient u (σ n) ∧
        h3ExactAdaptiveSelectedAbsorbedCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) = 0 ∧
        (n : ℝ) < h3PathCanonicalMarginExcessRate u 0 (σ n) ∧
        (n : ℝ) < h3PathCanonicalNonlinearDissipationShortfall u (σ n) ∧
        0 ≤ h3PathCanonicalTransportCancellationGap u (σ n)) ∧
      Tendsto σ atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalIndexedTerminalWidth T n (σ n)) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n : ℕ => h3PathCanonicalMarginExcessRate u 0 (σ n))
        atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalNonlinearDissipationShortfall u (σ n)) atTop atTop := by
  classical
  have hChoice : ∀ n : ℕ, ∃ t : ℝ,
      t ∈ Set.Ioo (T - δ n) T ∧
      h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t =
          h3PathCanonicalKineticTransportCoefficient u t ∧
      h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t = 0 ∧
      (n : ℝ) < h3PathCanonicalMarginExcessRate u 0 t ∧
      (n : ℝ) < h3PathCanonicalNonlinearDissipationShortfall u t ∧
      0 ≤ h3PathCanonicalTransportCancellationGap u t := by
    intro n
    let m : ℝ := h3BKMKineticTailMidpoint a T
    have hm : m ∈ Set.Ioo a T :=
      h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2
    let d : ℝ := max m (T - δ n)
    have hd : d ∈ Set.Ioo a T := by
      exact ⟨lt_of_lt_of_le hm.1 (le_max_left _ _),
        max_lt hm.2 (sub_lt_self T (hδPos n))⟩
    obtain ⟨s, hs, hsDirect, hsAbsorbed, hsActual, hsSpectral⟩ :=
      h3PathCanonical_actualAndSpectralExcess_simultaneously_large_in_directRegime
        (n : ℝ) hH3 hNoExtension hClass hMass hd
    have hsNear : s ∈ Set.Ioo (T - δ n) T :=
      ⟨lt_of_le_of_lt (le_max_right m (T - δ n)) hs.1, hs.2⟩
    have hsClass : s ∈ Set.Ioo a T :=
      ⟨lt_trans hd.1 hs.1, hs.2⟩
    exact ⟨s, hsNear, hsDirect, hsAbsorbed, hsActual, hsSpectral,
      h3PathCanonicalTransportCancellationGap_nonneg hH3 hClass hsClass⟩
  choose σ hσ using hChoice
  have hNear : ∀ n : ℕ, σ n ∈ Set.Ioo (T - δ n) T :=
    fun n => (hσ n).1
  have hClock := h3PathCanonical_terminalClock_tendsto_of_shrinking_windows
    hNear hδTop
  have hWidth := h3PathCanonical_indexedWidth_tendsto_zero_of_fast_windows
    hNear hδScaled
  have hActual : Tendsto (fun n : ℕ =>
      h3PathCanonicalMarginExcessRate u 0 (σ n)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M
    filter_upwards [eventually_ge_atTop N] with n hn
    have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact le_of_lt (lt_of_lt_of_le hN
      (le_trans hCast (le_of_lt (hσ n).2.2.2.1)))
  have hSpectral : Tendsto (fun n : ℕ =>
      h3PathCanonicalNonlinearDissipationShortfall u (σ n)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M
    filter_upwards [eventually_ge_atTop N] with n hn
    have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact le_of_lt (lt_of_lt_of_le hN
      (le_trans hCast (le_of_lt (hσ n).2.2.2.2.1)))
  exact ⟨σ, hσ, hClock, hWidth, hActual, hSpectral⟩


/-- Compactness still extracts a cancellation-share cluster after the terminal
clock has been selected with *vanishing* indexed physical width. Actual
transport excess and spectral shortfall remain divergent on this same
cofinal subsequence. -/
theorem h3PathCanonical_exists_direct_zeroIndexedWidth_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {δ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hδPos : ∀ n : ℕ, 0 < δ n)
    (hδTop : Tendsto δ atTop (𝓝 (0 : ℝ)))
    (hδScaled : Tendsto (fun n : ℕ => (n : ℝ) * δ n)
      atTop (𝓝 (0 : ℝ))) :
    ∃ σ : ℕ → ℝ, ∃ k : ℕ → ℕ, ∃ θ : ℝ,
      StrictMono k ∧ θ ∈ Set.Icc (0 : ℝ) 1 ∧
      (∀ n : ℕ,
        σ n ∈ Set.Ioo (T - δ n) T ∧
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) =
            h3PathCanonicalKineticTransportCoefficient u (σ n) ∧
        h3ExactAdaptiveSelectedAbsorbedCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) = 0 ∧
        (n : ℝ) < h3PathCanonicalMarginExcessRate u 0 (σ n) ∧
        (n : ℝ) < h3PathCanonicalNonlinearDissipationShortfall u (σ n) ∧
        0 ≤ h3PathCanonicalTransportCancellationGap u (σ n)) ∧
      Tendsto (fun n : ℕ => σ (k n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalIndexedTerminalWidth T (k n) (σ (k n)))
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalMarginExcessRate u 0 (σ (k n))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalNonlinearDissipationShortfall u (σ (k n))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalCancellationBudgetShare u (σ (k n)))
        atTop (𝓝 θ) := by
  classical
  obtain ⟨σ, hSamples, hClock, hWidth, hActual, hSpectral⟩ :=
    h3PathCanonical_exists_direct_excess_fastWidth_sequence
      hH3 hNoExtension hClass hMass hδPos hδTop hδScaled
  have hShareMem : ∀ n : ℕ,
      h3PathCanonicalCancellationBudgetShare u (σ n) ∈
        Set.Icc (0 : ℝ) 1 := by
    intro n
    obtain ⟨_, _, _, hActualN, _, hCancel⟩ := hSamples n
    have hPos : 0 < h3PathCanonicalMarginExcessRate u 0 (σ n) :=
      lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ (n : ℝ)) hActualN
    exact (h3PathCanonical_cancellationAndGrowthShares_mem_Icc
      u (σ n) hCancel hPos).1
  have hMem : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalCancellationBudgetShare u (σ n) ∈
        Set.Icc (0 : ℝ) 1 := by
    filter_upwards [] with n
    exact hShareMem n
  obtain ⟨θ, hθ, k, hkMono, hShare⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).tendsto_subseq'
      hMem.frequently
  have hkTop : Tendsto k atTop atTop := hkMono.tendsto_atTop
  have hClockSub : Tendsto (fun n : ℕ => σ (k n)) atTop (𝓝 T) := by
    simpa only [Function.comp_def] using hClock.comp hkTop
  have hWidthSub : Tendsto (fun n : ℕ =>
      h3PathCanonicalIndexedTerminalWidth T (k n) (σ (k n)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def] using hWidth.comp hkTop
  have hActualSub : Tendsto (fun n : ℕ =>
      h3PathCanonicalMarginExcessRate u 0 (σ (k n))) atTop atTop := by
    simpa only [Function.comp_def] using hActual.comp hkTop
  have hSpectralSub : Tendsto (fun n : ℕ =>
      h3PathCanonicalNonlinearDissipationShortfall u (σ (k n)))
      atTop atTop := by
    simpa only [Function.comp_def] using hSpectral.comp hkTop
  exact ⟨σ, k, θ, hkMono, hθ, hSamples, hClockSub,
    hWidthSub, hActualSub, hSpectralSub, hShare⟩

/-- An explicit gauge `δₙ = 1/(n+1)²` always yields a zero indexed-width
cluster on the hypothetical nonextension branch, with the actual and
spectral excesses both divergent and cancellation-share compactness intact. -/
theorem h3PathCanonical_exists_direct_quadraticWidth_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∃ σ : ℕ → ℝ, ∃ k : ℕ → ℕ, ∃ θ : ℝ,
      StrictMono k ∧ θ ∈ Set.Icc (0 : ℝ) 1 ∧
      (∀ n : ℕ,
        σ n ∈ Set.Ioo (T - (1 : ℝ) / (((n : ℝ) + 1) ^ 2)) T ∧
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) =
            h3PathCanonicalKineticTransportCoefficient u (σ n) ∧
        h3ExactAdaptiveSelectedAbsorbedCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) = 0 ∧
        (n : ℝ) < h3PathCanonicalMarginExcessRate u 0 (σ n) ∧
        (n : ℝ) < h3PathCanonicalNonlinearDissipationShortfall u (σ n)) ∧
      Tendsto (fun n : ℕ => σ (k n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalIndexedTerminalWidth T (k n) (σ (k n)))
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalMarginExcessRate u 0 (σ (k n))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalNonlinearDissipationShortfall u (σ (k n))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalCancellationBudgetShare u (σ (k n)))
        atTop (𝓝 θ) := by
  let ρ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let δ : ℕ → ℝ := fun n => (ρ n) ^ 2
  have hρ : Tendsto ρ atTop (𝓝 (0 : ℝ)) := by
    simpa only [ρ, Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hδPos : ∀ n : ℕ, 0 < δ n := by
    intro n
    dsimp only [δ, ρ]
    positivity
  have hδTop : Tendsto δ atTop (𝓝 (0 : ℝ)) := by
    simpa [δ] using (hρ.pow 2)
  have hδScaled : Tendsto (fun n : ℕ => (n : ℝ) * δ n)
      atTop (𝓝 (0 : ℝ)) := by
    have hLower : ∀ n : ℕ, 0 ≤ (n : ℝ) * δ n := by
      intro n
      exact mul_nonneg (by positivity) (hδPos n).le
    have hUpper : ∀ n : ℕ, (n : ℝ) * δ n ≤ ρ n := by
      intro n
      have hDen : 0 < (n : ℝ) + 1 := by positivity
      have hLe : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have hMul := mul_le_mul_of_nonneg_right hLe (sq_nonneg (ρ n))
      calc
        (n : ℝ) * δ n ≤ ((n : ℝ) + 1) * (ρ n) ^ 2 := by
          simpa only [δ] using hMul
        _ = ρ n := by
          dsimp only [ρ]
          field_simp [ne_of_gt hDen]
          <;> ring
    exact squeeze_zero'
      (Filter.Eventually.of_forall hLower)
      (Filter.Eventually.of_forall hUpper) hρ
  obtain ⟨σ, k, θ, hkMono, hθ, hSamples, hClock, hWidth,
    hActual, hSpectral, hShare⟩ :=
    h3PathCanonical_exists_direct_zeroIndexedWidth_shareCluster
      hH3 hNoExtension hClass hMass hδPos hδTop hδScaled
  refine ⟨σ, k, θ, hkMono, hθ, ?_, hClock, hWidth,
    hActual, hSpectral, hShare⟩
  intro n
  obtain ⟨hNear, hDirect, hAbsorbed, hActualN, hSpectralN, _hCancel⟩ :=
    hSamples n
  have hNear' : σ n ∈ Set.Ioo
      (T - (1 : ℝ) / (((n : ℝ) + 1) ^ 2)) T := by
    simpa [δ, ρ, div_pow] using hNear
  exact ⟨hNear', hDirect, hAbsorbed, hActualN, hSpectralN⟩

/-- In addition to the earlier compact-width alternative, a vanishing
indexed-width witness sequence can always be selected on the hypothetical
nonextension side. Its vanishing index clock is not a PDE growth ceiling. -/
theorem h3PathCanonical_extension_or_direct_quadraticWidth_zeroCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, 0 < velocityH3Energy0At u b →
      ∃ σ : ℕ → ℝ, ∃ k : ℕ → ℕ, ∃ θ : ℝ,
        StrictMono k ∧ θ ∈ Set.Icc (0 : ℝ) 1 ∧
        Tendsto (fun n : ℕ => σ (k n)) atTop (𝓝 T) ∧
        Tendsto (fun n : ℕ =>
          h3PathCanonicalIndexedTerminalWidth T (k n) (σ (k n)))
          atTop (𝓝 (0 : ℝ)) ∧
        Tendsto (fun n : ℕ =>
          h3PathCanonicalMarginExcessRate u 0 (σ (k n))) atTop atTop ∧
        Tendsto (fun n : ℕ =>
          h3PathCanonicalNonlinearDissipationShortfall u (σ (k n))) atTop atTop ∧
        Tendsto (fun n : ℕ =>
          h3PathCanonicalCancellationBudgetShare u (σ (k n)))
          atTop (𝓝 θ) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro b hMass
    obtain ⟨σ, k, θ, hkMono, hθ, _hSamples, hClock, hWidth,
      hActual, hSpectral, hShare⟩ :=
      h3PathCanonical_exists_direct_quadraticWidth_shareCluster
        hH3 hExt hClass hMass
    exact ⟨σ, k, θ, hkMono, hθ, hClock, hWidth,
      hActual, hSpectral, hShare⟩

end Euclidean
end Bridge
end PrimeTensor
