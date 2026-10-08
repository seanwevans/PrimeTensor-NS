import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalUnabsorbedRiccatiIntegrability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalIntrinsicClockBridge

/-!
# Synchronize unabsorbed Riccati growth with direct H3 terminal witnesses

On strict H3 energy-class times the canonical full-dissipation positive
transport excess is exactly q0=max(0,E'/E). The unabsorbed nonlinear
Riccati rate is U=max(0,E'/E-4422). The positive-part truncation yields

    U <= q0 <= U + 4422.

Thus the rates differ by a uniformly bounded baseline. Divergence of
actual transport excess automatically carries divergence of U on the
*same* physical sequence, with no new selection or analytic hypothesis.

The earlier quadratically fast direct clock retains zero indexed width,
a compact cancellation-share cluster, and divergent actual and spectral
excesses. This module transfers U divergence to that same cofinal clock
and retains the intrinsic Riccati-derived quartic indexed energy floor.
The latter remains an indexed consequence of the existing intrinsic
inverse-square terminal growth bound, not a new physical-time exponent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- On strict H3 energy-class times, the zero-margin positive transport
excess is the positive normalized derivative of the physical H3 energy. -/
theorem h3PathCanonical_actualExcess_eq_positiveNormalizedGrowth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathCanonicalMarginExcessRate u 0 t =
      max 0 (deriv (velocityH3EnergyAt u) t /
        velocityH3EnergyAt u t) := by
  calc
    h3PathCanonicalMarginExcessRate u 0 t =
        h3PathFullDissipationTransportExcessRate u t := by
          simp only [h3PathCanonicalMarginExcessRate,
            h3PathFullDissipationTransportExcessRate, sub_zero]
    _ = h3PathPositiveEnergyGrowthRate u t :=
      h3PathFullDissipationTransportExcessRate_eq_positiveEnergyGrowthRate
        hH3 hClass ht
    _ = max 0 (deriv (velocityH3EnergyAt u) t /
        velocityH3EnergyAt u t) := rfl

/-- The positive unabsorbed Riccati rate and positive full-dissipation
transport excess differ by no more than the fixed commutator baseline. -/
theorem h3PathCanonical_unabsorbedRate_actualExcess_sandwich
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathCanonicalUnabsorbedRiccatiRate u t ≤
        h3PathCanonicalMarginExcessRate u 0 t ∧
      h3PathCanonicalMarginExcessRate u 0 t ≤
        4422 + h3PathCanonicalUnabsorbedRiccatiRate u t := by
  let x : ℝ := deriv (velocityH3EnergyAt u) t /
    velocityH3EnergyAt u t
  have hU : h3PathCanonicalUnabsorbedRiccatiRate u t =
      max 0 (x - 4422) := by
    simpa only [x] using
      h3PathCanonical_unabsorbedRiccatiRate_eq_positiveAboveBaseline
        hH3 hClass ht
  have hQ : h3PathCanonicalMarginExcessRate u 0 t = max 0 x := by
    simpa only [x] using
      h3PathCanonical_actualExcess_eq_positiveNormalizedGrowth
        hH3 hClass ht
  rw [hU, hQ]
  constructor
  · apply max_le
    · exact le_max_left _ _
    · have hx : x ≤ max (0 : ℝ) x := le_max_right _ _
      linarith only [hx]
  · apply max_le
    · have h0 : (0 : ℝ) ≤ max 0 (x - 4422) := le_max_left _ _
      linarith only [h0]
    · have hx : x - 4422 ≤ max (0 : ℝ) (x - 4422) :=
        le_max_right _ _
      linarith only [hx]

/-- The actual excess minus the unabsorbed excess is always within the
closed fixed baseline interval [0,4422]. -/
theorem h3PathCanonical_actualExcess_sub_unabsorbedRate_mem_Icc
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathCanonicalMarginExcessRate u 0 t -
        h3PathCanonicalUnabsorbedRiccatiRate u t ∈
      Set.Icc (0 : ℝ) 4422 := by
  obtain ⟨hLo, hHi⟩ :=
    h3PathCanonical_unabsorbedRate_actualExcess_sandwich hH3 hClass ht
  constructor <;> linarith only [hLo, hHi]

/-- Any exact actual-excess witness above the baseline plus a prescribed
threshold is automatically an unabsorbed-growth witness at that threshold. -/
theorem h3PathCanonical_unabsorbedRate_gt_of_actualExcess_gt_baseline
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hActual : M + 4422 < h3PathCanonicalMarginExcessRate u 0 t) :
    M < h3PathCanonicalUnabsorbedRiccatiRate u t := by
  have hUpper :=
    (h3PathCanonical_unabsorbedRate_actualExcess_sandwich
      hH3 hClass ht).2
  linarith only [hActual, hUpper]

/-- Divergence of the full-dissipation positive normalized transport
excess forces divergence of the unabsorbed nonlinear growth on the same
cofinal sequence. No selection-specific clock relation is needed. -/
theorem h3PathCanonical_unabsorbedRate_tendsto_atTop_of_actualExcess
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTimes : ∀ᶠ n : ℕ in atTop, τ n ∈ Set.Ioo a T)
    (hActual : Tendsto (fun n : ℕ =>
      h3PathCanonicalMarginExcessRate u 0 (τ n)) atTop atTop) :
    Tendsto (fun n : ℕ =>
      h3PathCanonicalUnabsorbedRiccatiRate u (τ n)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  have hAbove : ∀ᶠ n : ℕ in atTop,
      M + 4422 ≤ h3PathCanonicalMarginExcessRate u 0 (τ n) :=
    (tendsto_atTop.1 hActual) (M + 4422)
  filter_upwards [hTimes, hAbove] with n ht hn
  have hUpper :=
    (h3PathCanonical_unabsorbedRate_actualExcess_sandwich
      hH3 hClass ht).2
  linarith only [hn, hUpper]

/-- Conversely, divergent unabsorbed nonlinear growth forces divergent
positive actual full-dissipation transport excess on the same terminal clock. -/
theorem h3PathCanonical_actualExcess_tendsto_atTop_of_unabsorbedRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTimes : ∀ᶠ n : ℕ in atTop, τ n ∈ Set.Ioo a T)
    (hU : Tendsto (fun n : ℕ =>
      h3PathCanonicalUnabsorbedRiccatiRate u (τ n)) atTop atTop) :
    Tendsto (fun n : ℕ =>
      h3PathCanonicalMarginExcessRate u 0 (τ n)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  have hAbove : ∀ᶠ n : ℕ in atTop,
      M ≤ h3PathCanonicalUnabsorbedRiccatiRate u (τ n) :=
    (tendsto_atTop.1 hU) M
  filter_upwards [hTimes, hAbove] with n ht hn
  have hLower :=
    (h3PathCanonical_unabsorbedRate_actualExcess_sandwich
      hH3 hClass ht).1
  exact le_trans hn hLower

/-- Along any sequence eventually inside the energy-class tail,
the actual transport excess diverges precisely when its unabsorbed
Riccati portion diverges: the fixed 4422 baseline cannot affect escape. -/
theorem h3PathCanonical_actualExcess_atTop_iff_unabsorbedRate_atTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTimes : ∀ᶠ n : ℕ in atTop, τ n ∈ Set.Ioo a T) :
    Tendsto (fun n : ℕ =>
      h3PathCanonicalMarginExcessRate u 0 (τ n)) atTop atTop ↔
    Tendsto (fun n : ℕ =>
      h3PathCanonicalUnabsorbedRiccatiRate u (τ n)) atTop atTop := by
  constructor
  · exact h3PathCanonical_unabsorbedRate_tendsto_atTop_of_actualExcess
      hH3 hClass hTimes
  · exact h3PathCanonical_actualExcess_tendsto_atTop_of_unabsorbedRate
      hH3 hClass hTimes

/-- Under hypothetical nonextension, every prescribed strict terminal
subtail contains a direct-selected time with both unabsorbed nonlinear
transport growth and spectral shortfall above any scalar threshold. -/
theorem h3PathCanonical_direct_unabsorbedAndSpectral_witness
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
      M < h3PathCanonicalUnabsorbedRiccatiRate u t ∧
      M < h3PathCanonicalNonlinearDissipationShortfall u t := by
  obtain ⟨t, ht, hDirect, hAbsorbed, hActual, hSpectral⟩ :=
    h3PathCanonical_actualAndSpectralExcess_simultaneously_large_in_directRegime
      (M + 4422) hH3 hNoExtension hClass hMass hd
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  have hU := h3PathCanonical_unabsorbedRate_gt_of_actualExcess_gt_baseline
    hH3 hClass htClass hActual
  refine ⟨t, ht, hDirect, hAbsorbed, hU, ?_⟩
  linarith only [hSpectral]

/-- Fast direct terminal witnesses jointly synchronize divergent actual
and unabsorbed growth with the spectral shortfall, zero indexed width,
cancellation-share compactness, and the pre-existing Riccati quartic
indexed-energy floor. -/
theorem h3PathCanonical_exists_direct_unabsorbed_fastClock_cluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∃ σ : ℕ → ℝ, ∃ k : ℕ → ℕ, ∃ θ : ℝ,
      StrictMono k ∧ θ ∈ Set.Icc (0 : ℝ) 1 ∧
      Tendsto (fun n : ℕ => σ (k n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalIndexedTerminalWidth T (k n) (σ (k n)))
          atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalCancellationBudgetShare u (σ (k n)))
          atTop (𝓝 θ) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalMarginExcessRate u 0 (σ (k n))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalUnabsorbedRiccatiRate u (σ (k n))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalNonlinearDissipationShortfall u (σ (k n))) atTop atTop ∧
      (∀ n : ℕ,
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ (k n)) =
            h3PathCanonicalKineticTransportCoefficient u (σ (k n)) ∧
        h3ExactAdaptiveSelectedAbsorbedCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ (k n)) = 0) ∧
      (∀ᶠ n : ℕ in atTop,
        4 * (((k n : ℕ) : ℝ) + 1) ^ 4 ≤
          h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
            velocityH3EnergyAt u (σ (k n))) := by
  obtain ⟨σ, k, θ, hkMono, hθ, hSamples, hClock, hWidth,
    hActual, hSpectral, hShare⟩ :=
    h3PathCanonical_exists_direct_quadraticWidth_shareCluster
      hH3 hNoExtension hClass hMass
  have hAbove : ∀ᶠ n : ℕ in atTop, a < σ (k n) :=
    (tendsto_order.1 hClock).1 a hClass.terminal_start.2
  have hTimes : ∀ᶠ n : ℕ in atTop, σ (k n) ∈ Set.Ioo a T := by
    filter_upwards [hAbove] with n hn
    exact ⟨hn, (hSamples (k n)).1.2⟩
  have hU := h3PathCanonical_unabsorbedRate_tendsto_atTop_of_actualExcess
    hH3 hClass hTimes hActual
  have hQuartic : ∀ᶠ n : ℕ in atTop,
      4 * (((k n : ℕ) : ℝ) + 1) ^ 4 ≤
        h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          velocityH3EnergyAt u (σ (k n)) := by
    filter_upwards [hTimes] with n ht
    exact h3PathCanonical_intrinsicEnergy_quartic_of_quadraticWindow
      (k n) hH3 hNoExtension hClass ht (hSamples (k n)).1
  refine ⟨σ, k, θ, hkMono, hθ, hClock, hWidth, hShare,
    hActual, hU, hSpectral, ?_, hQuartic⟩
  intro n
  exact ⟨(hSamples (k n)).2.1, (hSamples (k n)).2.2.1⟩

/-- Neutral continuation alternative retaining the synchronized
unabsorbed-growth blowup rate on the original compact fast-clock cluster. -/
theorem h3PathCanonical_extension_or_direct_unabsorbed_fastClock_cluster
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
          h3PathCanonicalCancellationBudgetShare u (σ (k n)))
            atTop (𝓝 θ) ∧
        Tendsto (fun n : ℕ =>
          h3PathCanonicalUnabsorbedRiccatiRate u (σ (k n))) atTop atTop ∧
        (∀ᶠ n : ℕ in atTop,
          4 * (((k n : ℕ) : ℝ) + 1) ^ 4 ≤
            h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
              velocityH3EnergyAt u (σ (k n))) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro b hMass
    obtain ⟨σ, k, θ, hkMono, hθ, hClock, hWidth, hShare,
      _hActual, hU, _hSpectral, _hDirect, hQuartic⟩ :=
      h3PathCanonical_exists_direct_unabsorbed_fastClock_cluster
        hH3 hExt hClass hMass
    exact ⟨σ, k, θ, hkMono, hθ, hClock, hWidth, hShare, hU, hQuartic⟩

end Euclidean
end Bridge
end PrimeTensor
