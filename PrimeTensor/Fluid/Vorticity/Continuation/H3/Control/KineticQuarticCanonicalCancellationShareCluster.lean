import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalTransportCancellationGap

/-!
# Compact cancellation-share cluster on the synchronized terminal clock

The exact physical transport/commutator budget on the positive actual-excess
branch is

    Delta(t) + q(t) = 4422 + S(t),

where Delta is the nonnegative normalized cancellation slack, q is the
positive normalized full-dissipation transport excess, and S is the
baseline-free spectral shortfall.  The preceding module produced one
nonextension terminal sequence with q and S both tending to +infinity.

Normalizing the two nonnegative summands by their *actual* sum produces
complementary shares between zero and one. Compactness extracts a cofinal
subsequence with a limiting cancellation share theta in [0,1] and an actual
transport-growth share 1-theta. Both unnormalized quantities q and S still
diverge on that same subsequence, and exact direct selection persists.

The endpoints theta=0 and theta=1 are both retained. In particular, theta=1
is compatible with unbounded q if the overall spectral budget grows faster;
no cancellation-sharpness or continuation conclusion is inferred.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- Fraction of the positive exact cancellation/transport budget occupied by
commutator cancellation slack; used only when the denominator is positive. -/
noncomputable def h3PathCanonicalCancellationBudgetShare
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) : ℝ → ℝ :=
  fun t => h3PathCanonicalTransportCancellationGap u t /
    (h3PathCanonicalTransportCancellationGap u t +
      h3PathCanonicalMarginExcessRate u 0 t)

/-- Complementary positive actual-growth fraction of the same exact budget. -/
noncomputable def h3PathCanonicalActualGrowthBudgetShare
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) : ℝ → ℝ :=
  fun t => h3PathCanonicalMarginExcessRate u 0 t /
    (h3PathCanonicalTransportCancellationGap u t +
      h3PathCanonicalMarginExcessRate u 0 t)

/-- Positive actual excess and nonnegative cancellation slack put both
normalized shares in the compact unit interval. -/
theorem h3PathCanonical_cancellationAndGrowthShares_mem_Icc
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (hCancel : 0 ≤ h3PathCanonicalTransportCancellationGap u t)
    (hActual : 0 < h3PathCanonicalMarginExcessRate u 0 t) :
    h3PathCanonicalCancellationBudgetShare u t ∈ Set.Icc (0 : ℝ) 1 ∧
    h3PathCanonicalActualGrowthBudgetShare u t ∈ Set.Icc (0 : ℝ) 1 := by
  have hDen : 0 < h3PathCanonicalTransportCancellationGap u t +
      h3PathCanonicalMarginExcessRate u 0 t := by
    linarith only [hCancel, hActual]
  constructor
  · constructor
    · unfold h3PathCanonicalCancellationBudgetShare
      exact div_nonneg hCancel (le_of_lt hDen)
    · unfold h3PathCanonicalCancellationBudgetShare
      apply (div_le_iff₀ hDen).2
      simpa only [one_mul] using
        (show h3PathCanonicalTransportCancellationGap u t ≤
          h3PathCanonicalTransportCancellationGap u t +
            h3PathCanonicalMarginExcessRate u 0 t by
              linarith only [hActual])
  · constructor
    · unfold h3PathCanonicalActualGrowthBudgetShare
      exact div_nonneg (le_of_lt hActual) (le_of_lt hDen)
    · unfold h3PathCanonicalActualGrowthBudgetShare
      apply (div_le_iff₀ hDen).2
      simpa only [one_mul] using
        (show h3PathCanonicalMarginExcessRate u 0 t ≤
          h3PathCanonicalTransportCancellationGap u t +
            h3PathCanonicalMarginExcessRate u 0 t by
              linarith only [hCancel])

/-- The exact normalized cancellation and transport-growth fractions exhaust
the positive budget; this is a partition, not an analytic estimate. -/
theorem h3PathCanonical_cancellationAndGrowthShares_sum_one
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (hCancel : 0 ≤ h3PathCanonicalTransportCancellationGap u t)
    (hActual : 0 < h3PathCanonicalMarginExcessRate u 0 t) :
    h3PathCanonicalCancellationBudgetShare u t +
      h3PathCanonicalActualGrowthBudgetShare u t = 1 := by
  have hDen : 0 < h3PathCanonicalTransportCancellationGap u t +
      h3PathCanonicalMarginExcessRate u 0 t := by
    linarith only [hCancel, hActual]
  unfold h3PathCanonicalCancellationBudgetShare
    h3PathCanonicalActualGrowthBudgetShare
  field_simp [ne_of_gt hDen]
  <;> ring

/-- On a positive-excess H3 slice, the common denominator of the two shares
is precisely the spectral shortfall plus its constant commutator baseline. -/
theorem h3PathCanonical_cancellationBudget_denominator_eq_spectral
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (hActual : 0 < h3PathCanonicalMarginExcessRate u 0 t) :
    h3PathCanonicalTransportCancellationGap u t +
      h3PathCanonicalMarginExcessRate u 0 t =
        4422 + h3PathCanonicalNonlinearDissipationShortfall u t :=
  h3PathCanonical_cancellationGap_add_actualExcess_eq_spectralBudget_of_pos
    u t hActual

/-- A lower bound on cancellation's fractional share produces a quantitative
upper bound on the actual transport excess relative to the exact budget.
It does not bound either quantity absolutely. -/
theorem h3PathCanonical_actualGrowthShare_le_of_cancellationShare_lower
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t δ : ℝ)
    (hCancel : 0 ≤ h3PathCanonicalTransportCancellationGap u t)
    (hActual : 0 < h3PathCanonicalMarginExcessRate u 0 t)
    (hShare : δ ≤ h3PathCanonicalCancellationBudgetShare u t) :
    h3PathCanonicalActualGrowthBudgetShare u t ≤ 1 - δ := by
  have hSum := h3PathCanonical_cancellationAndGrowthShares_sum_one
    u t hCancel hActual
  linarith only [hSum, hShare]

/-- The nonextension branch admits a single terminal physical-clock sequence
and a cofinal subsequence with a finite cancellation fraction cluster. Both
unnormalized rates remain divergent and both share limits are complementary.
Neither endpoint of the compact interval is excluded. -/
theorem h3PathCanonical_exists_direct_cancellationShare_cluster
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
        σ n ∈ Set.Ioo a T ∧
        σ n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
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
        h3PathCanonicalMarginExcessRate u 0 (σ (k n))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalNonlinearDissipationShortfall u (σ (k n))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalCancellationBudgetShare u (σ (k n)))
        atTop (𝓝 θ) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalActualGrowthBudgetShare u (σ (k n)))
        atTop (𝓝 (1 - θ)) := by
  classical
  obtain ⟨σ, hσ, hClock, hActualTop, hSpectralTop⟩ :=
    h3PathCanonical_exists_direct_cancellationBudget_sequence
      hH3 hNoExtension hClass hMass
  have hShares : ∀ n : ℕ,
      h3PathCanonicalCancellationBudgetShare u (σ n) ∈ Set.Icc (0 : ℝ) 1 ∧
      h3PathCanonicalCancellationBudgetShare u (σ n) +
        h3PathCanonicalActualGrowthBudgetShare u (σ n) = 1 := by
    intro n
    obtain ⟨_, _, _, _, hActual, _, hCancel, _⟩ := hσ n
    have hActualPos : 0 < h3PathCanonicalMarginExcessRate u 0 (σ n) :=
      lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ (n : ℝ)) hActual
    exact ⟨(h3PathCanonical_cancellationAndGrowthShares_mem_Icc
      u (σ n) hCancel hActualPos).1,
      h3PathCanonical_cancellationAndGrowthShares_sum_one
        u (σ n) hCancel hActualPos⟩
  have hInInterval : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalCancellationBudgetShare u (σ n) ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [] with n
    exact (hShares n).1
  obtain ⟨θ, hθ, k, hkMono, hShareTop⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).tendsto_subseq'
      hInInterval.frequently
  have hkTop : Tendsto k atTop atTop := hkMono.tendsto_atTop
  have hClockSub : Tendsto (fun n : ℕ => σ (k n)) atTop (𝓝 T) := by
    simpa only [Function.comp_def] using hClock.comp hkTop
  have hActualSub : Tendsto (fun n : ℕ =>
      h3PathCanonicalMarginExcessRate u 0 (σ (k n))) atTop atTop := by
    simpa only [Function.comp_def] using hActualTop.comp hkTop
  have hSpectralSub : Tendsto (fun n : ℕ =>
      h3PathCanonicalNonlinearDissipationShortfall u (σ (k n))) atTop atTop := by
    simpa only [Function.comp_def] using hSpectralTop.comp hkTop
  have hActualShareSub : Tendsto (fun n : ℕ =>
      h3PathCanonicalActualGrowthBudgetShare u (σ (k n)))
      atTop (𝓝 (1 - θ)) := by
    have hComplement : Tendsto (fun n : ℕ =>
        1 - h3PathCanonicalCancellationBudgetShare u (σ (k n)))
        atTop (𝓝 (1 - θ)) :=
      tendsto_const_nhds.sub hShareTop
    apply hComplement.congr'
    filter_upwards [] with n
    linarith only [(hShares (k n)).2]
  refine ⟨σ, k, θ, hkMono, hθ, ?_, hClockSub,
    hActualSub, hSpectralSub, hShareTop, hActualShareSub⟩
  intro n
  obtain ⟨hAt, hNear, hDirect, hAbsorbed, hActual, hSpectral,
    hCancel, _⟩ := hσ n
  exact ⟨hAt, hNear, hDirect, hAbsorbed, hActual, hSpectral, hCancel⟩

/-- The neutral terminal alternative retains every possible cancellation-share
cluster; a limiting full cancellation *fraction* does not eliminate a divergent
absolute actual transport excess. -/
theorem h3PathCanonical_extension_or_direct_cancellationShare_cluster
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
          h3PathCanonicalMarginExcessRate u 0 (σ (k n))) atTop atTop ∧
        Tendsto (fun n : ℕ =>
          h3PathCanonicalNonlinearDissipationShortfall u (σ (k n))) atTop atTop ∧
        Tendsto (fun n : ℕ =>
          h3PathCanonicalCancellationBudgetShare u (σ (k n)))
          atTop (𝓝 θ) ∧
        Tendsto (fun n : ℕ =>
          h3PathCanonicalActualGrowthBudgetShare u (σ (k n)))
          atTop (𝓝 (1 - θ)) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro b hMass
    obtain ⟨σ, k, θ, hkMono, hθ, _hSamples, hClock, hActual,
      hSpectral, hCancel, hGrowth⟩ :=
      h3PathCanonical_exists_direct_cancellationShare_cluster
        hH3 hExt hClass hMass
    exact ⟨σ, k, θ, hkMono, hθ, hClock, hActual,
      hSpectral, hCancel, hGrowth⟩

end Euclidean
end Bridge
end PrimeTensor
