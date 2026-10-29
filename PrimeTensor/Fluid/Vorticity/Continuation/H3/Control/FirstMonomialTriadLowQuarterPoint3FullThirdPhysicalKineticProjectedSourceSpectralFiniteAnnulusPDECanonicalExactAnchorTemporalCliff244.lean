import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorPhysicalExposure244
import Mathlib.Tactic

/-!
# Actual physical dissipation temporal cliffs at exact canonical H³ anchors

The complete physical dissipation integrals over the original canonical
nonoverlapping windows tend to zero. A window with a nontrivial anchor-height
charge therefore cannot sustain even a fixed fraction of its anchor
physical dissipation throughout the window.

This produces an unconditional, parameterized dichotomy on precisely those
windows: the anchor-height charge is small, or some actual time in the
window has much smaller full H³ dissipation than at its left endpoint.
If a fixed positive anchor-height charge persists, the second branch
holds eventually for every positive relative threshold. No temporal
regularity of the unbounded full dissipation functional is assumed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Small integral mass forces either a small anchor height-times-width
charge or an integral mass below any prescribed relative anchor mean. -/
theorem h3Path_scalar_smallPhysicalMass_peakChargeOrRelativeMean244
    (I δ H η θ : ℝ) (hθ : 0 < θ)
    (hSmall : I < θ * η) :
    δ * H ≤ η ∨ I < θ * H * δ := by
  by_cases hCharge : δ * H ≤ η
  · exact Or.inl hCharge
  · right
    have hLarge : η ≤ δ * H := le_of_lt (lt_of_not_ge hCharge)
    calc
      I < θ * η := hSmall
      _ ≤ θ * (δ * H) :=
        mul_le_mul_of_nonneg_left hLarge hθ.le
      _ = θ * H * δ := by ring

/-- When the integral over a positive physical interval is strictly
smaller than a constant multiple of its length, the actual integrand
must fall below that constant at some point of the interval. -/
theorem h3Path_physicalIntegral_small_forces_relativeDissipationDip244
    (f : ℝ → ℝ) (s δ H θ : ℝ)
    (hδ : 0 < δ)
    (hInt : IntervalIntegrable f volume s (s + δ))
    (hSmall : (∫ r in s..(s + δ), f r) < θ * H * δ) :
    ∃ r : ℝ, r ∈ Set.Icc s (s + δ) ∧ f r < θ * H := by
  classical
  by_contra hNo
  have hLower (r : ℝ) (hr : r ∈ Set.Icc s (s + δ)) :
      θ * H ≤ f r := by
    exact le_of_not_gt (fun hlt => hNo ⟨r, hr, hlt⟩)
  have hCompare :
      (∫ _r in s..(s + δ), θ * H) ≤
        ∫ r in s..(s + δ), f r :=
    intervalIntegral.integral_mono_on
      (le_add_of_nonneg_right hδ.le)
      intervalIntegrable_const hInt hLower
  have hConstant :
      (∫ _r in s..(s + δ), θ * H) = δ * (θ * H) := by
    simp <;> ring
  have hLowerIntegral : θ * H * δ ≤
      ∫ r in s..(s + δ), f r := by
    calc
      θ * H * δ = δ * (θ * H) := by ring
      _ = ∫ _r in s..(s + δ), θ * H := hConstant.symm
      _ ≤ ∫ r in s..(s + δ), f r := hCompare
  exact (not_lt_of_ge hLowerIntegral) hSmall

/-- On a sequence of genuine physical intervals with vanishing integral
masses, every positive anchor-charge threshold and every relative
dissipation fraction yield an eventual two-arm alternative. The second
arm is witnessed by an ACTUAL time, not just a mean-value bound. -/
theorem h3Path_physicalVanishingWindowMass_chargeOrTemporalDip244
    (f : ℝ → ℝ) (a T : ℝ) (τ δ : ℕ → ℝ)
    (haT : a ≤ T)
    (hInt : IntervalIntegrable f volume a T)
    (hStart : ∀ k, a ≤ τ k)
    (hWidth : ∀ k, 0 < δ k)
    (hEnd : ∀ k, τ k + δ k ≤ T)
    (hMass : Tendsto (fun k =>
      ∫ r in τ k..(τ k + δ k), f r) atTop (𝓝 (0 : ℝ)))
    (η θ : ℝ) (hη : 0 < η) (hθ : 0 < θ) :
    ∀ᶠ k : ℕ in atTop,
      δ k * f (τ k) ≤ η ∨
      ∃ r : ℝ, r ∈ Set.Icc (τ k) (τ k + δ k) ∧
        f r < θ * f (τ k) := by
  have hSmall : ∀ᶠ k : ℕ in atTop,
      (∫ r in τ k..(τ k + δ k), f r) < θ * η :=
    hMass.eventually (eventually_lt_nhds (mul_pos hθ hη))
  filter_upwards [hSmall] with k hk
  have hAlt := h3Path_scalar_smallPhysicalMass_peakChargeOrRelativeMean244
    (∫ r in τ k..(τ k + δ k), f r)
    (δ k) (f (τ k)) η θ hθ hk
  rcases hAlt with hCharge | hMean
  · exact Or.inl hCharge
  · right
    have hSubInt : IntervalIntegrable f volume (τ k) (τ k + δ k) := by
      apply hInt.mono_set
      rw [Set.uIcc_of_le (le_add_of_nonneg_right (hWidth k).le),
        Set.uIcc_of_le haT]
      exact Set.Icc_subset_Icc (hStart k) (hEnd k)
    exact h3Path_physicalIntegral_small_forces_relativeDissipationDip244
      f (τ k) (δ k) (f (τ k)) θ (hWidth k) hSubInt hMean

/-- An eventually nonvanishing actual peak-height charge rules out the
small-charge arm. Therefore on the SAME windows the physical dissipation
has a relative downward spike for every fixed positive threshold. -/
theorem h3Path_physicalPersistentAnchorCharge_forces_temporalCliff244
    (f : ℝ → ℝ) (a T : ℝ) (τ δ : ℕ → ℝ)
    (haT : a ≤ T)
    (hInt : IntervalIntegrable f volume a T)
    (hStart : ∀ k, a ≤ τ k)
    (hWidth : ∀ k, 0 < δ k)
    (hEnd : ∀ k, τ k + δ k ≤ T)
    (hMass : Tendsto (fun k =>
      ∫ r in τ k..(τ k + δ k), f r) atTop (𝓝 (0 : ℝ)))
    (η : ℝ) (hη : 0 < η)
    (hPersistent : ∀ᶠ k : ℕ in atTop,
      η ≤ δ k * f (τ k))
    (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ k : ℕ in atTop,
      ∃ r : ℝ, r ∈ Set.Icc (τ k) (τ k + δ k) ∧
        f r < θ * f (τ k) := by
  have hHalf : 0 < η / 2 := by linarith only [hη]
  have hAlt := h3Path_physicalVanishingWindowMass_chargeOrTemporalDip244
    f a T τ δ haT hInt hStart hWidth hEnd hMass
    (η / 2) θ hHalf hθ
  filter_upwards [hAlt, hPersistent] with k hk hCharge
  rcases hk with hSmall | hDip
  · exfalso
    linarith only [hSmall, hCharge, hη]
  · exact hDip

/-- On the ORIGINAL exact-anchor disjoint Navier–Stokes windows:
vanishing full H³ integral masses force either small physical anchor
height-times-width charges or genuinely lower physical dissipation at
some point in the SAME window. Persistent anchor-height charge forces
arbitrarily severe relative temporal dips. This statement does not
assert the persistent-charge hypothesis. -/
theorem h3Path_noL2Trace_exactAnchor_physicalTemporalCliffAlternative244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (_N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, K (v k) =
        ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        0 < δ (v k)) ∧
      (∀ k, 3 * (((v k : ℝ) + 1) ^ 3) / 4 <
        velocityH3DissipationAt u (τ (v k))) ∧
      Tendsto (fun k => velocityH3DissipationAt u (τ (v k))) atTop atTop ∧
      Summable (fun k =>
        ∫ r in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u r) ∧
      Tendsto (fun k =>
        ∫ r in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u r) atTop (𝓝 (0 : ℝ)) ∧
      (∀ η θ : ℝ, 0 < η → 0 < θ → ∀ᶠ k : ℕ in atTop,
        δ (v k) * velocityH3DissipationAt u (τ (v k)) ≤ η ∨
          ∃ r : ℝ, r ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) ∧
            velocityH3DissipationAt u r <
              θ * velocityH3DissipationAt u (τ (v k))) ∧
      (∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          η ≤ δ (v k) * velocityH3DissipationAt u (τ (v k))) →
        ∀ θ : ℝ, 0 < θ → ∀ᶠ k : ℕ in atTop,
          ∃ r : ℝ, r ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) ∧
            velocityH3DissipationAt u r <
              θ * velocityH3DissipationAt u (τ (v k))) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, hCanonical, hFloor, hDiverge, hSummable, hZero,
      _hExposure, _hCharge⟩ :=
    h3Path_noL2Trace_exactAnchor_actualPhysicalExposureCollapse244
      hH3 hClass hMass hNoTrace hDInt
  have hStart (k : ℕ) : a ≤ τ (v k) := (hTime (v k)).1.le
  have hWidth (k : ℕ) : 0 < δ (v k) := (hCanonical k).2.2
  have hEnd (k : ℕ) : τ (v k) + δ (v k) ≤ T := by
    exact le_of_lt ((hSeparate k (k + 1) (Nat.lt_succ_self k)).trans
      (hTime (v (k + 1))).2)
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, hCanonical, hFloor, hDiverge, hSummable, hZero,
    ?_, ?_⟩
  · intro η θ hη hθ
    exact h3Path_physicalVanishingWindowMass_chargeOrTemporalDip244
      (velocityH3DissipationAt u) a T
      (fun k => τ (v k)) (fun k => δ (v k))
      hClass.terminal_start.2.le hDInt hStart hWidth hEnd hZero
      η θ hη hθ
  · intro η hη hPersist θ hθ
    exact h3Path_physicalPersistentAnchorCharge_forces_temporalCliff244
      (velocityH3DissipationAt u) a T
      (fun k => τ (v k)) (fun k => δ (v k))
      hClass.terminal_start.2.le hDInt hStart hWidth hEnd hZero
      η hη hPersist θ hθ

end
end PrimeTensor.FirstMonomialTriad
