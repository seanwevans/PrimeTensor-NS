import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalFastClockSelection
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.Lower.Bound

/-!
# Intrinsic Riccati clock versus freely selected direct witnesses

The already proved `Terminal.Riccati.Lower.Bound` supplies an *intrinsic*,
pointwise terminal blowup lower bound under hypothetical nonextension:

  2 <= K * (T-t) * sqrt(E(t)),   K = 4422 * (C1+1).

This is valid at every strict H3 energy-class time; it does not depend on
where the terminal witness selection algorithm places its samples.  In
particular it is stronger than the indexed witness-only clock alternatives.

We expose the corresponding quadratic pointwise energy bound and its
contrapositive one-time continuation tests.  At the faster selected times
`t_n in (T - 1/(n+1)^2,T)`, the intrinsic estimate also forces the *indexed*
quartic energy floor `4(n+1)^4 <= K^2 E(t_n)`.  Both the fast clock width
and the prior cancellation-share cluster survive unchanged.  The selected
index still does not fix an intrinsic PDE clock: the quadratic Riccati floor
is the intrinsic bound and the quartic index rate is its consequence along
these deliberately chosen narrow windows.

No unconditional extension or existence of a finite-time blowup is claimed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The already proved Riccati bound, squared into a division-free
pointwise physical-time energy lower bound on every strict terminal tail. -/
theorem h3PathCanonical_intrinsic_terminalEnergy_quadraticFloor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    (4 : ℝ) ≤
      h3PathSqrtEnergyRiccatiCoefficient ^ 2 * (T - t) ^ 2 *
        velocityH3EnergyAt u t := by
  have hRate :=
    two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrtEnergy_of_noH3PathExtension
      hH3 hNoExtension hClass ht
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hSquare : (4 : ℝ) ≤
      (h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
        Real.sqrt (velocityH3EnergyAt u t)) ^ 2 := by
    nlinarith only [hRate,
      sq_nonneg
        (h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
          Real.sqrt (velocityH3EnergyAt u t) - 2)]
  calc
    (4 : ℝ) ≤
        (h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
          Real.sqrt (velocityH3EnergyAt u t)) ^ 2 := hSquare
    _ = h3PathSqrtEnergyRiccatiCoefficient ^ 2 * (T - t) ^ 2 *
          velocityH3EnergyAt u t := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hE]

/-- An exported inverse-square-root formulation of the intrinsic terminal
Riccati bound, useful when comparing energy and remaining physical time. -/
theorem h3PathCanonical_intrinsic_inverseSqrtEnergy_le_terminalWidth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    (Real.sqrt (velocityH3EnergyAt u t))⁻¹ ≤
      (h3PathSqrtEnergyRiccatiCoefficient / 2) * (T - t) := by
  have hRate :=
    two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrtEnergy_of_noH3PathExtension
      hH3 hNoExtension hClass ht
  have hSqrtPos : 0 < Real.sqrt (velocityH3EnergyAt u t) :=
    Real.sqrt_pos.2
      (lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t))
  have hDiv : (1 : ℝ) / Real.sqrt (velocityH3EnergyAt u t) ≤
      (h3PathSqrtEnergyRiccatiCoefficient / 2) * (T - t) := by
    apply (div_le_iff₀ hSqrtPos).2
    calc
      (1 : ℝ) = (1 / 2 : ℝ) * 2 := by norm_num
      _ ≤ (1 / 2 : ℝ) *
          (h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
            Real.sqrt (velocityH3EnergyAt u t)) :=
        mul_le_mul_of_nonneg_left hRate (by norm_num)
      _ = ((h3PathSqrtEnergyRiccatiCoefficient / 2) * (T - t)) *
            Real.sqrt (velocityH3EnergyAt u t) := by ring
  simpa only [one_div] using hDiv

/-- A *single* subcritical normalized physical-clock energy observation
ensures smooth continuation, by contraposition of the intrinsic Riccati
lower bound. This is not a new a priori PDE estimate. -/
theorem h3PathCanonical_extension_of_subcritical_terminalEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hSmall :
      h3PathSqrtEnergyRiccatiCoefficient ^ 2 * (T - t) ^ 2 *
        velocityH3EnergyAt u t < 4) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hFloor := h3PathCanonical_intrinsic_terminalEnergy_quadraticFloor
    hH3 hNoExtension hClass ht
  exact (not_lt_of_ge hFloor) hSmall

/-- The same one-time continuation test before squaring: if the
Riccati-normalized square-root energy falls below two anywhere on a strict
tail, nonextension is impossible. -/
theorem h3PathCanonical_extension_of_subcritical_terminalSqrtEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hSmall :
      h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
        Real.sqrt (velocityH3EnergyAt u t) < 2) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hFloor :=
    two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrtEnergy_of_noH3PathExtension
      hH3 hNoExtension hClass ht
  exact (not_lt_of_ge hFloor) hSmall

/-- The intrinsic inverse-time Riccati floor becomes quartic in the freely
selected index for *quadratically narrowing* witness windows. This is an
indexed result, not a separate intrinsic time exponent. -/
theorem h3PathCanonical_intrinsicEnergy_quartic_of_quadraticWindow
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ} (n : ℕ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hNear : t ∈ Set.Ioo
      (T - (1 : ℝ) / (((n : ℝ) + 1) ^ 2)) T) :
    4 * (((n : ℝ) + 1) ^ 4) ≤
      h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
        velocityH3EnergyAt u t := by
  have hRate :=
    two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrtEnergy_of_noH3PathExtension
      hH3 hNoExtension hClass ht
  have hDen : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  have hWidth : T - t < (1 : ℝ) / (((n : ℝ) + 1) ^ 2) := by
    linarith only [hNear.1]
  have hWidthScaled : (T - t) * (((n : ℝ) + 1) ^ 2) ≤ 1 :=
    le_of_lt ((lt_div_iff₀ hDen).1 hWidth)
  have hK : 0 ≤ h3PathSqrtEnergyRiccatiCoefficient :=
    le_of_lt h3PathSqrtEnergyRiccatiCoefficient_pos
  have hRoot : 0 ≤ Real.sqrt (velocityH3EnergyAt u t) :=
    Real.sqrt_nonneg _
  have hCoeff : 0 ≤ h3PathSqrtEnergyRiccatiCoefficient *
      Real.sqrt (velocityH3EnergyAt u t) := mul_nonneg hK hRoot
  have hBoundRoot : 2 * (((n : ℝ) + 1) ^ 2) ≤
      h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u t) := by
    calc
      2 * (((n : ℝ) + 1) ^ 2) ≤
          (h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
            Real.sqrt (velocityH3EnergyAt u t)) * (((n : ℝ) + 1) ^ 2) :=
        mul_le_mul_of_nonneg_right hRate hDen.le
      _ = (h3PathSqrtEnergyRiccatiCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) *
            ((T - t) * (((n : ℝ) + 1) ^ 2)) := by ring
      _ ≤ (h3PathSqrtEnergyRiccatiCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * 1 :=
        mul_le_mul_of_nonneg_left hWidthScaled hCoeff
      _ = h3PathSqrtEnergyRiccatiCoefficient *
          Real.sqrt (velocityH3EnergyAt u t) := by ring
  have hSquare : (2 * (((n : ℝ) + 1) ^ 2)) ^ 2 ≤
      (h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) ^ 2 := by
    nlinarith only [hBoundRoot,
      sq_nonneg
        (h3PathSqrtEnergyRiccatiCoefficient *
          Real.sqrt (velocityH3EnergyAt u t) -
          2 * (((n : ℝ) + 1) ^ 2))]
  have hEnergy : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  calc
    4 * (((n : ℝ) + 1) ^ 4) =
        (2 * (((n : ℝ) + 1) ^ 2)) ^ 2 := by ring
    _ ≤ (h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) ^ 2 := hSquare
    _ = h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
        velocityH3EnergyAt u t := by
      rw [mul_pow, Real.sq_sqrt hEnergy]

/-- The quadratic-window, zero-indexed-width nonextension sequence has a
quartic **indexed** energy floor on its cofinal cancellation-share cluster.
The actual excess and spectral shortfall still both diverge. -/
theorem h3PathCanonical_exists_direct_fastClock_intrinsicEnergy_cluster
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
  have hQuartic : ∀ᶠ n : ℕ in atTop,
      4 * (((k n : ℕ) : ℝ) + 1) ^ 4 ≤
        h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          velocityH3EnergyAt u (σ (k n)) := by
    filter_upwards [hAbove] with n hn
    have hNear := (hSamples (k n)).1
    exact h3PathCanonical_intrinsicEnergy_quartic_of_quadraticWindow
      (k n) hH3 hNoExtension hClass ⟨hn, hNear.2⟩ hNear
  refine ⟨σ, k, θ, hkMono, hθ, hClock, hWidth, hShare,
    hActual, hSpectral, ?_, hQuartic⟩
  intro n
  exact ⟨(hSamples (k n)).2.1, (hSamples (k n)).2.2.1⟩

/-- Either continuation, or freely selected fast terminal witnesses retain
both a vanishing indexed width and an intrinsic Riccati-derived quartic
indexed energy floor. This does not supply any new physical-time exponent. -/
theorem h3PathCanonical_extension_or_fastClock_intrinsicEnergy_cluster
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
      _hActual, _hSpectral, _hSelected, hQuartic⟩ :=
      h3PathCanonical_exists_direct_fastClock_intrinsicEnergy_cluster
        hH3 hExt hClass hMass
    exact ⟨σ, k, θ, hkMono, hθ, hClock, hWidth, hShare, hQuartic⟩

end Euclidean
end Bridge
end PrimeTensor
