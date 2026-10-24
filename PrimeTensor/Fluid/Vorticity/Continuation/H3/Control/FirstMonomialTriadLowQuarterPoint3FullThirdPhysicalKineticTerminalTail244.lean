import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticSourceCostCorridor244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceCubicClockWithoutCanonicalData
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Physical kinetic terminal-tail dissipation budget

The preceding kinetic corridor bounds D0 on fixed positive-time intervals.
Independently, closed H3 energy derivatives and monotone convergence already
establish a finite terminal kinetic mass L for every strict H3 energy-class
tail. This file synchronizes the *exact* physical Hilbert kinetic budget
with that terminal mass.

For a < s <= t < T, exact kinetic balance and L <= E0(t) yield

   2 ∫_s^t D0 <= E0(s) - L.

The right-hand side tends to zero as s approaches T from the left. This is a
UNIFORM bound over every later t<T, not a pointwise dissipation ceiling.
The signed physical Hilbert source pairing equals -D0, so the same tail
expenditure is the signed source action. No terminal Hilbert-vector trace,
endpoint regularity, or high-order D3-integrability is inferred.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Genuine order-zero dissipation expenditure cannot exceed the kinetic
mass remaining above its canonical terminal infimum. -/
theorem h3Path_physicalDissipation0_tailBudget_le_remainingKinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) :
    2 * (∫ r in s..t, velocityH3Dissipation0At u r) ≤
      velocityH3Energy0At u s -
        h3PathCanonicalTerminalKineticEnergyAt u a T := by
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hBalance := h3Path_energy0_integratedDissipation0_positiveTimes244
    hH3 s t hsAbs htAbs hst
  have hInf := h3PathCanonical_terminalKineticEnergy_le_anchor
    (u := u) ht
  linarith only [hBalance, hInf]

/-- The exact dissipation spent from any fixed strict positive-time anchor
converges to E0(s)-L at the terminal time (the finite total kinetic loss). -/
theorem h3Path_physicalDissipation0_cumulative_tendsto_terminalLoss244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (s : ℝ) (hs : s ∈ Set.Ioo a T) :
    Tendsto
      (fun t : ℝ => 2 * (∫ r in s..t, velocityH3Dissipation0At u r))
      (𝓝[<] T)
      (𝓝 (velocityH3Energy0At u s -
        h3PathCanonicalTerminalKineticEnergyAt u a T)) := by
  have hLimit :=
    h3PathCanonical_terminalKineticEnergy_tendsto_noCanonicalData hH3 hClass
  have hSub : Tendsto
      (fun t : ℝ => velocityH3Energy0At u s - velocityH3Energy0At u t)
      (𝓝[<] T)
      (𝓝 (velocityH3Energy0At u s -
        h3PathCanonicalTerminalKineticEnergyAt u a T)) :=
    hLimit.const_sub _
  have hEventuallyLater : ∀ᶠ t : ℝ in 𝓝[<] T, s < t := by
    have hNhds : ∀ᶠ t : ℝ in 𝓝 T, s < t :=
      Ioi_mem_nhds hs.2
    exact hNhds.filter_mono nhdsWithin_le_nhds
  apply hSub.congr'
  filter_upwards [self_mem_nhdsWithin, hEventuallyLater] with t htT hst
  have ht : t ∈ Set.Ioo a T := ⟨lt_trans hs.1 hst, htT⟩
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hBudget := h3Path_energy0_integratedDissipation0_positiveTimes244
    hH3 s t hsAbs htAbs (le_of_lt hst)
  linarith only [hBudget]

/-- The terminal kinetic limit forces uniformly vanishing ORDER-ZERO
viscous spending across all later strict times. No control of D3 is claimed. -/
theorem h3Path_physicalDissipation0_uniformTerminalTailSmall244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in 𝓝[<] T,
      s ∈ Set.Ioo a T ∧
        ∀ t : ℝ, t ∈ Set.Ioo a T → s ≤ t →
          2 * (∫ r in s..t, velocityH3Dissipation0At u r) < ε := by
  let L : ℝ := h3PathCanonicalTerminalKineticEnergyAt u a T
  have hLimit : Tendsto (velocityH3Energy0At u) (𝓝[<] T) (𝓝 L) :=
    h3PathCanonical_terminalKineticEnergy_tendsto_noCanonicalData hH3 hClass
  have hSmall : ∀ᶠ s : ℝ in 𝓝[<] T,
      velocityH3Energy0At u s < L + ε :=
    (tendsto_order.1 hLimit).2 (L + ε) (by linarith only [hε])
  have hEventuallyAfterA : ∀ᶠ s : ℝ in 𝓝[<] T, a < s := by
    have hNhds : ∀ᶠ s : ℝ in 𝓝 T, a < s :=
      Ioi_mem_nhds hClass.terminal_start.2
    exact hNhds.filter_mono nhdsWithin_le_nhds
  filter_upwards [hSmall, self_mem_nhdsWithin, hEventuallyAfterA]
    with s hsSmall hsT haS
  have hs : s ∈ Set.Ioo a T := ⟨haS, hsT⟩
  refine ⟨hs, ?_⟩
  intro t ht hst
  have hBound := h3Path_physicalDissipation0_tailBudget_le_remainingKinetic244
    hH3 hClass s t hs ht hst
  dsimp only [L] at hsSmall
  linarith only [hBound, hsSmall]

/-- The time-integrated physical source/velocity Hilbert pairing is exactly
the negative order-zero dissipation expenditure on each strict interval. -/
theorem h3Path_physicalSourcePairing_integral_eq_negDissipation0_244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t) :
    (∫ r in s..t,
      inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 r)
        (h3PathActualProjectedMomentumSource244 hH3 r)) =
      -(∫ r in s..t, velocityH3Dissipation0At u r) := by
  calc
    (∫ r in s..t,
      inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 r)
        (h3PathActualProjectedMomentumSource244 hH3 r)) =
      ∫ r in s..t, -velocityH3Dissipation0At u r := by
        apply intervalIntegral.integral_congr_Ioo_of_le hst
        intro r hr
        exact h3Path_physicalHilbertPairing_eq_negDissipation0_positiveTime244
          hH3 r ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
    _ = -(∫ r in s..t, velocityH3Dissipation0At u r) :=
      intervalIntegral.integral_neg

/-- The physical signed source action has a finite limit set precisely by
the terminal kinetic loss; the high-order transport source has no such
conclusion from this identity. -/
theorem h3Path_physicalSourcePairing_cumulative_tendsto_terminalLoss244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (s : ℝ) (hs : s ∈ Set.Ioo a T) :
    Tendsto
      (fun t : ℝ => 2 * (∫ r in s..t,
        inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 r)
          (h3PathActualProjectedMomentumSource244 hH3 r)))
      (𝓝[<] T)
      (𝓝 (h3PathCanonicalTerminalKineticEnergyAt u a T -
        velocityH3Energy0At u s)) := by
  have hD := h3Path_physicalDissipation0_cumulative_tendsto_terminalLoss244
    hH3 hClass s hs
  have hNeg : Tendsto
      (fun t : ℝ => -(2 * (∫ r in s..t, velocityH3Dissipation0At u r)))
      (𝓝[<] T)
      (𝓝 (h3PathCanonicalTerminalKineticEnergyAt u a T -
        velocityH3Energy0At u s)) := by
    simpa only [neg_sub] using hD.neg
  have hEventuallyLater : ∀ᶠ t : ℝ in 𝓝[<] T, s < t := by
    have hNhds : ∀ᶠ t : ℝ in 𝓝 T, s < t :=
      Ioi_mem_nhds hs.2
    exact hNhds.filter_mono nhdsWithin_le_nhds
  apply hNeg.congr'
  filter_upwards [self_mem_nhdsWithin, hEventuallyLater] with t htT hst
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hsAbs.1 hst, htT⟩
  have hPair := h3Path_physicalSourcePairing_integral_eq_negDissipation0_244
    hH3 s t hsAbs htAbs (le_of_lt hst)
  rw [hPair]
  ring

end
end PrimeTensor.FirstMonomialTriad
