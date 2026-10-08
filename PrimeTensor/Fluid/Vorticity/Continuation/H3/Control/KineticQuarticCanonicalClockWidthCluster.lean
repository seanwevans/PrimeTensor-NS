import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalPhysicalRateConsequences

/-!
# Indexed terminal width and genuine physical-clock alternatives

The established direct-selected witnesses satisfy n < q₀(tₙ) and
n < S(tₙ), together with T - 1/(n+1) < tₙ < T.  This localization
does not imply a positive physical-time lower bound for either
(T-tₙ)*q₀(tₙ) or (T-tₙ)*sqrt(E(tₙ)): the chosen witness can lie
arbitrarily close to T inside its permitted window.

Define the dimensionless indexed clock width w(n,t) = n*(T-t).
On those witnesses 0 ≤ w < 1 and the exact PDE balance implies

    w(n,t) < (T-t)*E'(t)/E(t),
    w(n,t) < (T-t)*4422*C₁*sqrt(E(t)).

Extracting a second compact subsequence makes w converge to χ in [0,1]
while preserving the earlier cancellation-share limit θ, the physical
terminal clock and the divergent actual and spectral excesses.  If χ > 0,
this forces genuine inverse-terminal-width lower bounds.  If χ = 0,
no such physical-rate conclusion follows from the indexed witnesses alone.
Both branches remain possible.  No new PDE coercivity estimate is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The selected witness index measured in units of remaining physical time. -/
def h3PathCanonicalIndexedTerminalWidth (T : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  (m : ℝ) * (T - t)

/-- Localization to the `1/(m+1)` terminal interval puts the indexed
physical clock in the compact unit interval. -/
theorem h3PathCanonical_indexedTerminalWidth_mem_Icc
    (T : ℝ) (m : ℕ) (t : ℝ)
    (ht : t ∈ Set.Ioo (T - (1 : ℝ) / ((m : ℝ) + 1)) T) :
    h3PathCanonicalIndexedTerminalWidth T m t ∈ Set.Icc (0 : ℝ) 1 := by
  have hWidth : 0 < T - t := sub_pos.mpr ht.2
  have hDen : 0 < (m : ℝ) + 1 := by positivity
  have hNear : T - t < 1 / ((m : ℝ) + 1) := by
    linarith only [ht.1]
  have hUpper : ((m : ℝ) + 1) * (T - t) < 1 := by
    calc
      _ < ((m : ℝ) + 1) * (1 / ((m : ℝ) + 1)) :=
        mul_lt_mul_of_pos_left hNear hDen
      _ = 1 := by field_simp [ne_of_gt hDen]
  have hN : 0 ≤ (m : ℝ) := by positivity
  constructor
  · unfold h3PathCanonicalIndexedTerminalWidth
    exact mul_nonneg hN hWidth.le
  · unfold h3PathCanonicalIndexedTerminalWidth
    nlinarith only [hUpper, hWidth]

/-- The indexed slope bound yields the corresponding dimensionless physical
clock lower bound, without claiming an absolute physical-time exponent. -/
theorem h3PathCanonical_indexedWidth_lt_physicalLogSlope
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) (m : ℕ)
    (ht : t < T)
    (hSlope : (m : ℝ) * velocityH3EnergyAt u t <
      deriv (velocityH3EnergyAt u) t) :
    h3PathCanonicalIndexedTerminalWidth T m t <
      (T - t) * (deriv (velocityH3EnergyAt u) t /
        velocityH3EnergyAt u t) := by
  have hE : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hRatio : (m : ℝ) <
      deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t :=
    (lt_div_iff₀ hE).2 hSlope
  have hWidth : 0 < T - t := sub_pos.mpr ht
  have hMul := mul_lt_mul_of_pos_left hRatio hWidth
  simpa only [h3PathCanonicalIndexedTerminalWidth, mul_comm] using hMul

/-- A large spectral shortfall similarly yields the indexed lower bound
on square-root energy measured against the physical terminal width. -/
theorem h3PathCanonical_indexedWidth_lt_physicalSqrtEnergy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) (m : ℕ)
    (ht : t < T)
    (hShort : (m : ℝ) < h3PathCanonicalNonlinearDissipationShortfall u t) :
    h3PathCanonicalIndexedTerminalWidth T m t <
      (T - t) * (4422 *
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) := by
  have hRoot := h3PathCanonical_sqrtEnergy_gt_of_spectralShortfall
    u (m : ℝ) t hShort
  have hWidth : 0 < T - t := sub_pos.mpr ht
  have hMul := mul_lt_mul_of_pos_left hRoot hWidth
  simpa only [h3PathCanonicalIndexedTerminalWidth, mul_comm] using hMul

/-- A strictly positive compact width cluster converts the indexed lower
bounds into authentic physical-time inequalities on the same sequence. -/
theorem h3PathCanonical_positiveIndexedWidthCluster_physicalRateLower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T χ : ℝ} {τ : ℕ → ℝ} {m : ℕ → ℕ}
    (hχ : 0 < χ)
    (hWidth : Tendsto (fun n : ℕ =>
      h3PathCanonicalIndexedTerminalWidth T (m n) (τ n)) atTop (𝓝 χ))
    (hSlope : ∀ n : ℕ,
      h3PathCanonicalIndexedTerminalWidth T (m n) (τ n) <
        (T - τ n) * (deriv (velocityH3EnergyAt u) (τ n) /
          velocityH3EnergyAt u (τ n)))
    (hRoot : ∀ n : ℕ,
      h3PathCanonicalIndexedTerminalWidth T (m n) (τ n) <
        (T - τ n) * (4422 *
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u (τ n)))) :
    (∀ᶠ n : ℕ in atTop,
      χ / 2 < (T - τ n) * (deriv (velocityH3EnergyAt u) (τ n) /
        velocityH3EnergyAt u (τ n))) ∧
    (∀ᶠ n : ℕ in atTop,
      χ / 2 < (T - τ n) * (4422 *
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u (τ n)))) := by
  have hHalf : χ / 2 < χ := by linarith only [hχ]
  have hAbove : ∀ᶠ n : ℕ in atTop,
      χ / 2 < h3PathCanonicalIndexedTerminalWidth T (m n) (τ n) :=
    (tendsto_order.1 hWidth).1 _ hHalf
  constructor
  · filter_upwards [hAbove] with n hn
    exact lt_trans hn (hSlope n)
  · filter_upwards [hAbove] with n hn
    exact lt_trans hn (hRoot n)

/-- One further compact extraction classifies the indexed physical width
while preserving the exact direct-selected cancellation-share cluster,
its physical terminal clock and both divergent normalized excesses. -/
theorem h3PathCanonical_exists_direct_indexedWidthShare_cluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∃ σ : ℕ → ℝ, ∃ k j : ℕ → ℕ, ∃ θ χ : ℝ,
      StrictMono k ∧ StrictMono j ∧
      θ ∈ Set.Icc (0 : ℝ) 1 ∧ χ ∈ Set.Icc (0 : ℝ) 1 ∧
      Tendsto (fun n : ℕ => σ (k (j n))) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalCancellationBudgetShare u (σ (k (j n)))) atTop (𝓝 θ) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalIndexedTerminalWidth T (k (j n)) (σ (k (j n))))
        atTop (𝓝 χ) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalMarginExcessRate u 0 (σ (k (j n)))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalNonlinearDissipationShortfall u (σ (k (j n)))) atTop atTop ∧
      (∀ n : ℕ,
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ (k (j n))) =
            h3PathCanonicalKineticTransportCoefficient u (σ (k (j n))) ∧
        h3ExactAdaptiveSelectedAbsorbedCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ (k (j n))) = 0 ∧
        h3PathCanonicalIndexedTerminalWidth T (k (j n)) (σ (k (j n))) <
          (T - σ (k (j n))) *
            (deriv (velocityH3EnergyAt u) (σ (k (j n))) /
              velocityH3EnergyAt u (σ (k (j n)))) ∧
        h3PathCanonicalIndexedTerminalWidth T (k (j n)) (σ (k (j n))) <
          (T - σ (k (j n))) * (4422 *
            h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (σ (k (j n)))))) := by
  classical
  obtain ⟨σ, k, θ, hkMono, hθ, hSamples, hClock, hActualTop,
    hSpectralTop, hShareTop, _hGrowthTop⟩ :=
    h3PathCanonical_exists_direct_cancellationShare_cluster
      hH3 hNoExtension hClass hMass
  have hInInterval : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalIndexedTerminalWidth T (k n) (σ (k n)) ∈
        Set.Icc (0 : ℝ) 1 := by
    filter_upwards [] with n
    exact h3PathCanonical_indexedTerminalWidth_mem_Icc
      T (k n) (σ (k n)) (hSamples (k n)).2.1
  obtain ⟨χ, hχ, j, hjMono, hWidthTop⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).tendsto_subseq'
      hInInterval.frequently
  have hjTop : Tendsto j atTop atTop := hjMono.tendsto_atTop
  have hClockSub : Tendsto (fun n : ℕ => σ (k (j n))) atTop (𝓝 T) := by
    simpa only [Function.comp_def] using hClock.comp hjTop
  have hShareSub : Tendsto (fun n : ℕ =>
      h3PathCanonicalCancellationBudgetShare u (σ (k (j n)))) atTop (𝓝 θ) := by
    simpa only [Function.comp_def] using hShareTop.comp hjTop
  have hWidthSub : Tendsto (fun n : ℕ =>
      h3PathCanonicalIndexedTerminalWidth T (k (j n)) (σ (k (j n))))
      atTop (𝓝 χ) := by
    simpa only [Function.comp_def] using hWidthTop
  have hActualSub : Tendsto (fun n : ℕ =>
      h3PathCanonicalMarginExcessRate u 0 (σ (k (j n)))) atTop atTop := by
    simpa only [Function.comp_def] using hActualTop.comp hjTop
  have hSpectralSub : Tendsto (fun n : ℕ =>
      h3PathCanonicalNonlinearDissipationShortfall u (σ (k (j n))))
      atTop atTop := by
    simpa only [Function.comp_def] using hSpectralTop.comp hjTop
  refine ⟨σ, k, j, θ, χ, hkMono, hjMono, hθ, hχ, hClockSub,
    hShareSub, hWidthSub, hActualSub, hSpectralSub, ?_⟩
  intro n
  obtain ⟨ht, _hNear, hDirect, hAbsorbed, hActual, hSpectral,
    _hCancel⟩ := hSamples (k (j n))
  have hIndex : 0 ≤ ((k (j n) : ℕ) : ℝ) := by positivity
  have hSlope := h3PathCanonical_energyDerivative_gt_of_actualExcess
    hH3 hClass ht hIndex hActual
  have hPhysicalSlope := h3PathCanonical_indexedWidth_lt_physicalLogSlope
    u T (σ (k (j n))) (k (j n)) ht.2 hSlope
  have hPhysicalRoot := h3PathCanonical_indexedWidth_lt_physicalSqrtEnergy
    u T (σ (k (j n))) (k (j n)) ht.2 hSpectral
  exact ⟨hDirect, hAbsorbed, hPhysicalSlope, hPhysicalRoot⟩

/-- The witness can be chosen inside *any* prescribed physical
terminal width, independently of its normalized excess threshold.  Thus
one cannot infer inverse-time growth merely from indexed witness bounds. -/
theorem h3PathCanonical_direct_excess_in_arbitrary_terminal_width
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b δ : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hδ : 0 < δ) :
    ∃ t : ℝ, t ∈ Set.Ioo (T - δ) T ∧
      h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t =
          h3PathCanonicalKineticTransportCoefficient u t ∧
      h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t = 0 ∧
      M < h3PathCanonicalMarginExcessRate u 0 t ∧
      M < h3PathCanonicalNonlinearDissipationShortfall u t := by
  let m : ℝ := h3BKMKineticTailMidpoint a T
  have hm : m ∈ Set.Ioo a T :=
    h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2
  let d : ℝ := max m (T - δ)
  have hd : d ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hm.1 (le_max_left _ _),
      max_lt hm.2 (sub_lt_self T hδ)⟩
  obtain ⟨t, ht, hDirect, hAbsorbed, hActual, hSpectral⟩ :=
    h3PathCanonical_actualAndSpectralExcess_simultaneously_large_in_directRegime
      M hH3 hNoExtension hClass hMass hd
  exact ⟨t, ⟨lt_of_le_of_lt (le_max_right m (T - δ)) ht.1, ht.2⟩,
    hDirect, hAbsorbed, hActual, hSpectral⟩

/-- Neutral physical-time alternative: either continuation, or one common
physical terminal subsequence has a compact indexed clock-width cluster.
If that cluster is positive, a true inverse-time critical rate follows;
if it is zero, no physical-time exponent is inferred. -/
theorem h3PathCanonical_extension_or_direct_indexedWidth_physicalRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, 0 < velocityH3Energy0At u b →
      ∃ σ : ℕ → ℝ, ∃ k j : ℕ → ℕ, ∃ θ χ : ℝ,
        θ ∈ Set.Icc (0 : ℝ) 1 ∧ χ ∈ Set.Icc (0 : ℝ) 1 ∧
        Tendsto (fun n : ℕ => σ (k (j n))) atTop (𝓝 T) ∧
        Tendsto (fun n : ℕ =>
          h3PathCanonicalCancellationBudgetShare u (σ (k (j n))))
          atTop (𝓝 θ) ∧
        Tendsto (fun n : ℕ =>
          h3PathCanonicalIndexedTerminalWidth T (k (j n)) (σ (k (j n))))
          atTop (𝓝 χ) ∧
        (χ = 0 ∨
          (0 < χ ∧
            (∀ᶠ n : ℕ in atTop,
              χ / 2 < (T - σ (k (j n))) *
                (deriv (velocityH3EnergyAt u) (σ (k (j n))) /
                  velocityH3EnergyAt u (σ (k (j n))))) ∧
            (∀ᶠ n : ℕ in atTop,
              χ / 2 < (T - σ (k (j n))) * (4422 *
                h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
                Real.sqrt (velocityH3EnergyAt u (σ (k (j n)))))))) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro b hMass
    obtain ⟨σ, k, j, θ, χ, _hkMono, _hjMono, hθ, hχ,
      hClock, hShare, hWidth, _hActual, _hSpectral, hSamples⟩ :=
      h3PathCanonical_exists_direct_indexedWidthShare_cluster
        hH3 hExt hClass hMass
    refine ⟨σ, k, j, θ, χ, hθ, hχ, hClock, hShare, hWidth, ?_⟩
    by_cases hZero : χ = 0
    · exact Or.inl hZero
    · right
      have hPos : 0 < χ := lt_of_le_of_ne hχ.1 (Ne.symm hZero)
      have hRates := h3PathCanonical_positiveIndexedWidthCluster_physicalRateLower
        (u := u) hPos hWidth
        (fun n => (hSamples n).2.2.1)
        (fun n => (hSamples n).2.2.2)
      exact ⟨hPos, hRates.1, hRates.2⟩

end Euclidean
end Bridge
end PrimeTensor
