import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticEighthAnchor
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Super-eighth terminal profiles force genuinely superlinear minimal carriers

For any positive height profile M(n) growing faster than the eighth power
of the inner Fourier radius, the physical order-zero kinetic anchor rules
out a bounded ratio between minimal outer and inner Fourier radii. The
outcome is a genuine geometric frequency escape of the minimal first
crossings, not one produced by freely enlarging the outer cutoff.

This is proved on the same disjoint time windows which carry exact anchored
PDE clocks, summable dissipation charges and attained projected-source peaks.
The result remains compatible with a terminal H³ concentration mechanism:
it does not force the selected source norm or its transport action to diverge.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

/-- Scalar eighth-power kinetic rigidity. If a height profile dominates
every fixed multiple of the inner radius to the eighth power, and its
physical crossing is paid by a fixed kinetic ceiling E, then the outer
radius divided by the inner radius must tend to infinity. -/
theorem thirdFull_superEighthProfile_kineticCost_forces_outerEscape244
    (R Q M : ℕ → ℝ) (E : ℝ)
    (hR : ∀ k : ℕ, 1 ≤ R k)
    (hQ : ∀ k : ℕ, 0 ≤ Q k)
    (hE : 0 ≤ E)
    (hCost : ∀ᶠ k : ℕ in atTop,
      M k < 8 * (Q k + 1) ^ 8 * E)
    (hFast : Tendsto (fun k : ℕ => M k / R k ^ 8) atTop atTop) :
    Tendsto (fun k : ℕ => (Q k + 1) / R k) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro A
  let D : ℝ := max A 0
  have hAD : A ≤ D := le_max_left _ _
  have hD : 0 ≤ D := le_max_right _ _
  have hLarge : ∀ᶠ k : ℕ in atTop,
      8 * D ^ 8 * E < M k / R k ^ 8 :=
    hFast.eventually (eventually_gt_atTop _)
  filter_upwards [hLarge, hCost] with k hkLarge hkCost
  have hRpos : 0 < R k := lt_of_lt_of_le zero_lt_one (hR k)
  have hR8 : 0 < R k ^ 8 := pow_pos hRpos _
  by_contra hNot
  have hRatio : (Q k + 1) / R k < A := lt_of_not_ge hNot
  have hQR : Q k + 1 ≤ D * R k :=
    (div_le_iff₀ hRpos).mp ((le_of_lt hRatio).trans hAD)
  have hQpos : 0 ≤ Q k + 1 := by linarith only [hQ k]
  have hPower : (Q k + 1) ^ 8 ≤ (D * R k) ^ 8 :=
    pow_le_pow_left₀ hQpos hQR 8
  have hEightE : 0 ≤ 8 * E := by positivity
  have hScaled := mul_le_mul_of_nonneg_right hPower hEightE
  have hUpper : M k < (8 * D ^ 8 * E) * R k ^ 8 := by
    calc
      M k < 8 * (Q k + 1) ^ 8 * E := hkCost
      _ = (Q k + 1) ^ 8 * (8 * E) := by ring
      _ ≤ (D * R k) ^ 8 * (8 * E) := hScaled
      _ = (8 * D ^ 8 * E) * R k ^ 8 := by ring
  have hSmall : M k / R k ^ 8 < 8 * D ^ 8 * E :=
    (div_lt_iff₀ hR8).2 hUpper
  exact (lt_asymm hkLarge hSmall)

/-- On the SAME minimal-cutoff, attained-source, disjoint H³ windows,
any prescribed super-eighth height profile forces the outer Fourier
radius to escape relative to the inner radius. The genuine source-peak
alternative and the quintic/eighth physical-rate channels remain on
these unchanged witnesses. A strong terminal H³ trace is not asserted. -/
theorem thirdFullPhysical_noH3Trace_superEighthMinimalCarrierEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n)
    (hMTop : Tendsto M atTop atTop)
    (hSuperEighth : Tendsto
      (fun n : ℕ => M n / (((n : ℝ) + 1) ^ 8)) atTop atTop) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244
        hH3 M τ N K C δ (v k)) ∧
      Summable (fun k : ℕ => δ (v k) * (M (v k) / 4)) ∧
      (∀ᶠ k : ℕ in atTop,
        M (v k) < 8 * (((N (v k) : ℝ) + 2) ^ 8) *
          velocityH3Energy0At u b) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        (T - τ (v k)) * M (v k) < 4 ∨
        M (v k) ^ 2 < 384 * K (v k) * C (v k) *
            (((N (v k) : ℝ) + 2) ^ 5 + ((v k : ℝ) + 2) ^ 5) + 8 ∨
        M (v k) ^ 2 < 576 * C (v k) ^ 2 *
            (((N (v k) : ℝ) + 2) ^ 8 + ((v k : ℝ) + 2) ^ 8) + 8) ∧
      (∀ S : ℝ, 0 ≤ S → ∀ᶠ k : ℕ in atTop,
        (T - τ (v k)) * M (v k) < 4 ∨
        (∃ sSource : ℝ,
          sSource ∈ Set.Icc (τ (v k)) ((τ (v k) + T) / 2) ∧
          S < ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖) ∨
        M (v k) ^ 2 < 8 *
          (S * h3PathFiniteAnnulusPDELinearGain244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) +
           S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) + 1)) := by
  obtain ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparated,
    hWindows, hSummable, _hLast, _hAveraged, hRates, hSource⟩ :=
    thirdFullPhysical_noH3Trace_minimalCarrier_sourceClock_or_physicalRates244
      hH3 hClass b hb hNoTrace hDInt M hM hMTop
  have hAfter : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  have hCost : ∀ᶠ k : ℕ in atTop,
      M (v k) < 8 * (((N (v k) : ℝ) + 2) ^ 8) *
        velocityH3Energy0At u b := by
    filter_upwards [hAfter] with k hkAfter
    rcases (hWindows k).1.1 with
      ⟨hnN, _, _, hδ, _, hEnd, _, _, hCross, _, _, _, _⟩
    have ht : τ (v k) ∈ Set.Ioo b T :=
      ⟨hkAfter, by linarith only [hδ, hEnd]⟩
    exact thirdFullPhysical_profileAnnulus_kineticEighthAnchor244
      hH3 hClass b hb (τ (v k)) ht
      (v k) (N (v k)) hnN (M (v k)) hCross
  let R : ℕ → ℝ := fun k => (v k : ℝ) + 1
  let Q : ℕ → ℝ := fun k => (N (v k) : ℝ) + 1
  let H : ℕ → ℝ := fun k => M (v k)
  have hR (k : ℕ) : 1 ≤ R k := by
    dsimp only [R]
    have hCast : 0 ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hCast]
  have hQ (k : ℕ) : 0 ≤ Q k := by
    dsimp only [Q]
    positivity
  have hFast : Tendsto (fun k : ℕ => H k / R k ^ 8)
      atTop atTop := by
    change Tendsto
      ((fun n : ℕ => M n / (((n : ℝ) + 1) ^ 8)) ∘ v) atTop atTop
    exact hSuperEighth.comp hMono.tendsto_atTop
  have hCost' : ∀ᶠ k : ℕ in atTop,
      H k < 8 * (Q k + 1) ^ 8 * velocityH3Energy0At u b := by
    simpa only [H, Q, add_assoc,
      show (1 : ℝ) + 1 = 2 by norm_num] using hCost
  have hOuter := thirdFull_superEighthProfile_kineticCost_forces_outerEscape244
    R Q H (velocityH3Energy0At u b)
    hR hQ (velocityH3Energy0At_nonneg u b) hCost' hFast
  have hOuterFn :
      (fun k : ℕ => (Q k + 1) / R k) =
      (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) := by
    funext k
    dsimp only [Q, R]
    ring
  rw [hOuterFn] at hOuter
  exact ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparated,
    hWindows, hSummable, hCost, hOuter, hRates, hSource⟩

end
end PrimeTensor.FirstMonomialTriad
