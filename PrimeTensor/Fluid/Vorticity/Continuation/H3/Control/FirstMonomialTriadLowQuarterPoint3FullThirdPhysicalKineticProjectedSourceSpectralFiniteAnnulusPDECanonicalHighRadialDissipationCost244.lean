import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalHighRadialTemporalMass244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostSum244
import Mathlib.Tactic

/-!
# Canonical high-radial source peaks: true viscous heights and persistence costs

The canonical physical projected-source maximizing times already exhibit
unbounded genuine weighted H³ Fourier mass outside EVERY fixed radial ball,
under the explicit critical-width clock conditions. The established exact
Fourier dissipation inequality turns that into unbounded ACTUAL high-radial
and full physical H³ viscous dissipation on exactly the same times.

There is no contradiction with finite time-integrated dissipation, because
these times can be isolated. The second half of the module quantifies the
missing requirement: IF additional intervals are disjoint and preserve a
high-radial spectral mass floor, their height-width costs are bounded by
the full dissipation integral. If those mass floors diverge, the widths must
converge to zero. No persistence of canonical source maxima is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeCanonicalHighRadialDissipationCost244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCanonicalHighRadialDissipationCost244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- At every actual strict-time physical slice, the high-radial weighted H³
square mass costs at least `ρ²` times that mass in FULL H³ dissipation.
This uses the true Fourier dissipation partition, not an H³ time derivative. -/
theorem h3Path_highRadialMass_le_fullDissipationAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ρ ^ 2 * h3PathActualSpectralHighRadialRemainder244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      velocityH3DissipationAt u t := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hHigh :
      ρ ^ 2 * h3PathActualSpectralHighRadialRemainder244 ρ G ≤
        h3PathActualHighRadialDissipation244 ρ G :=
    h3Path_actualHighRadialDissipation_ge_squareHighMass244
      hH3 hClass t ht ρ hρ
  have hLowNonneg : 0 ≤ h3PathActualLowRadialDissipation244 ρ G := by
    unfold h3PathActualLowRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg G ξ
  have hPartition :=
    h3Path_actualRadialDissipation_partition244 hH3 hClass t ht ρ
  dsimp only [G] at hHigh hLowNonneg hPartition ⊢
  linarith only [hHigh, hLowNonneg, hPartition]

/-- A single sequence of ACTUAL physical times with growing high-radial
H³ Fourier mass has simultaneously growing high-radial and full H³ viscous
heights at every fixed positive cutoff. No time-integral conclusion follows. -/
theorem h3Path_highRadialMassEscape_forces_dissipationPeaks244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (s : ℕ → ℝ) (hs : ∀ k, s k ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hMassEscape : Tendsto (fun k : ℕ =>
      h3PathActualSpectralHighRadialRemainder244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 (s k))) atTop atTop) :
    Tendsto (fun k : ℕ =>
      h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 (s k))) atTop atTop ∧
    Tendsto (fun k : ℕ => velocityH3DissipationAt u (s k))
      atTop atTop := by
  have hR : 0 < ρ ^ 2 := pow_pos hρ 2
  have hHighBound (k : ℕ) :=
    h3Path_actualHighRadialDissipation_ge_squareHighMass244
      hH3 hClass (s k) (hs k) ρ hρ.le
  have hFullBound (k : ℕ) :=
    h3Path_highRadialMass_le_fullDissipationAt244
      hH3 hClass (s k) (hs k) ρ hρ.le
  have hHighEscape : Tendsto (fun k : ℕ =>
      h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 (s k)))
      atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro M
    have hLate := hMassEscape.eventually
      (eventually_ge_atTop (M / ρ ^ 2))
    filter_upwards [hLate] with k hk
    have hScaled : M ≤ ρ ^ 2 *
        h3PathActualSpectralHighRadialRemainder244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 (s k)) := by
      have hDiv := (div_le_iff₀ hR).mp hk
      nlinarith only [hDiv]
    exact hScaled.trans (hHighBound k)
  have hFullEscape : Tendsto
      (fun k : ℕ => velocityH3DissipationAt u (s k))
      atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro M
    have hLate := hMassEscape.eventually
      (eventually_ge_atTop (M / ρ ^ 2))
    filter_upwards [hLate] with k hk
    have hScaled : M ≤ ρ ^ 2 *
        h3PathActualSpectralHighRadialRemainder244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 (s k)) := by
      have hDiv := (div_le_iff₀ hR).mp hk
      nlinarith only [hDiv]
    exact hScaled.trans (hFullBound k)
  exact ⟨hHighEscape, hFullEscape⟩

/-- An additional family of disjoint persistence intervals MUST pay its
high-radial H³ mass floor against the full physical H³ time integral.
The new intervals are *not* asserted to be the canonical half-terminal
source-maximizer windows, which generally overlap. -/
theorem h3Path_disjointHighRadialMassFloors_finiteDissipationCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (τ δ H : ℕ → ℝ)
    (hStart : ∀ k, a ≤ τ k)
    (hWidth : ∀ k, 0 ≤ δ k)
    (hEnd : ∀ k, τ k + δ k ≤ T)
    (hSeparate : ∀ k, τ k + δ k ≤ τ (k + 1))
    (hInside : ∀ k r, r ∈ Set.Icc (τ k) (τ k + δ k) →
      r ∈ Set.Ioo a T)
    (hFloor : ∀ k r, r ∈ Set.Icc (τ k) (τ k + δ k) →
      H k ≤ h3PathActualSpectralHighRadialRemainder244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 r)) :
    ∀ m : ℕ,
      (∑ k ∈ Finset.range m, δ k * (ρ ^ 2 * H k)) ≤
        ∫ r in a..T, velocityH3DissipationAt u r := by
  apply h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
    (velocityH3DissipationAt u) a T τ δ
    (fun k => ρ ^ 2 * H k)
    hClass.terminal_start.2.le
    (velocityH3DissipationAt_nonneg u)
    hDInt hStart hWidth hEnd hSeparate
  intro k r hr
  have hPhysical := h3Path_highRadialMass_le_fullDissipationAt244
    hH3 hClass r (hInside k r hr) ρ hρ
  have hScaled := mul_le_mul_of_nonneg_left
    (hFloor k r hr) (sq_nonneg ρ)
  exact hScaled.trans hPhysical

/-- Algebraic width-collapse principle. Bounded total height-width cost
and diverging nonnegative heights preclude a positive limiting width.
The coefficient `c` is the positive fixed-radius squared multiplier. -/
theorem h3Path_finiteHeightBudget_forces_widthCollapse244
    (δ H : ℕ → ℝ) (c B : ℝ)
    (hc : 0 < c) (_hB : 0 ≤ B)
    (hWidth : ∀ k, 0 ≤ δ k)
    (hHeight : ∀ k, 0 ≤ H k)
    (hCost : ∀ k, δ k * (c * H k) ≤ B)
    (hEscape : Tendsto H atTop atTop) :
    Tendsto δ atTop (𝓝 (0 : ℝ)) := by
  apply tendsto_order.2
  constructor
  · intro x hx
    exact Filter.Eventually.of_forall (fun k =>
      lt_of_lt_of_le hx (hWidth k))
  · intro ε hε
    have hLate : ∀ᶠ k : ℕ in atTop,
        (B + 1) / (c * ε) ≤ H k :=
      hEscape.eventually (eventually_ge_atTop ((B + 1) / (c * ε)))
    filter_upwards [hLate] with k hk
    by_contra hNot
    have hWide : ε ≤ δ k := le_of_not_gt hNot
    have hMass : B + 1 ≤ ε * (c * H k) := by
      calc
        B + 1 ≤ H k * (c * ε) :=
          (div_le_iff₀ (mul_pos hc hε)).mp hk
        _ = ε * (c * H k) := by ring
    have hFactor : 0 ≤ c * H k := mul_nonneg hc.le (hHeight k)
    have hCostLower : ε * (c * H k) ≤ δ k * (c * H k) :=
      mul_le_mul_of_nonneg_right hWide hFactor
    linarith only [hMass, hCostLower, hCost k]

/-- If an additional disjoint collection of actual physical intervals
persists with a divergent high-radial mass floor, their widths MUST shrink.
This is a necessary consequence of finite full H³ dissipation, not a
construction of persistence intervals around canonical source peaks. -/
theorem h3Path_disjointHighRadialMassEscape_forces_widthCollapse244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (τ δ H : ℕ → ℝ)
    (hStart : ∀ k, a ≤ τ k)
    (hWidth : ∀ k, 0 ≤ δ k)
    (hEnd : ∀ k, τ k + δ k ≤ T)
    (hSeparate : ∀ k, τ k + δ k ≤ τ (k + 1))
    (hInside : ∀ k r, r ∈ Set.Icc (τ k) (τ k + δ k) →
      r ∈ Set.Ioo a T)
    (hFloor : ∀ k r, r ∈ Set.Icc (τ k) (τ k + δ k) →
      H k ≤ h3PathActualSpectralHighRadialRemainder244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 r))
    (hHeight : ∀ k, 0 ≤ H k)
    (hEscape : Tendsto H atTop atTop) :
    Tendsto δ atTop (𝓝 (0 : ℝ)) := by
  let B : ℝ := ∫ r in a..T, velocityH3DissipationAt u r
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact intervalIntegral.integral_nonneg hClass.terminal_start.2.le
      (fun r _ => velocityH3DissipationAt_nonneg u r)
  have hCosts := h3Path_disjointHighRadialMassFloors_finiteDissipationCost244
    hH3 hClass hDInt ρ hρ.le τ δ H
    hStart hWidth hEnd hSeparate hInside hFloor
  have hEach (k : ℕ) : δ k * (ρ ^ 2 * H k) ≤ B := by
    have hSingle : δ k * (ρ ^ 2 * H k) ≤
        ∑ j ∈ Finset.range (k + 1), δ j * (ρ ^ 2 * H j) := by
      exact Finset.single_le_sum
        (fun j _ => mul_nonneg (hWidth j)
          (mul_nonneg (sq_nonneg ρ) (hHeight j)))
        (Finset.mem_range.mpr (Nat.lt_succ_self k))
    exact hSingle.trans (by simpa only [B] using hCosts (k + 1))
  exact h3Path_finiteHeightBudget_forces_widthCollapse244
    δ H (ρ ^ 2) B (pow_pos hρ 2) hB
    hWidth hHeight hEach hEscape

/-- SAME canonical source-maximizing times and SAME disjoint quadratic-sharp
anchor windows: in the explicit critical-width regime, genuine high-radial
and full H³ dissipation heights both diverge at source peaks for every fixed
positive Fourier radius. Nothing asserts persistence on the half-terminal
peak intervals or turns these pointwise heights into an integrated cost. -/
theorem h3Path_noL2Trace_canonicalWidth_highRadialDissipationPeaks244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTerminalMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ) (s : ℕ → ℝ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ k, s k ∈ Set.Icc (τ (v k))
          (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ = C (v k)) ∧
      (∀ η B D : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        ∀ ρ : ℝ, 0 < ρ →
          Tendsto (fun k : ℕ =>
            h3PathActualHighRadialDissipation244 ρ
              (h3AuditActualSpectralVelocityTotal hH3 (s k)))
            atTop atTop ∧
          Tendsto (fun k : ℕ => velocityH3DissipationAt u (s k))
            atTop atTop) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, _hRadial, hHigh⟩ :=
    h3Path_noL2Trace_canonicalWidth_highRadialPeaksAndTemporal244
      hH3 hClass hTerminalMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  have hsClass (k : ℕ) : s k ∈ Set.Ioo a T := by
    constructor
    · exact lt_of_lt_of_le (hTime (v k)).1 (hPeak k).1.1
    · have hMid : τ (v k) + (T - τ (v k)) / 2 < T := by
        have ht := (hTime (v k)).2
        linarith only [ht]
      exact lt_of_le_of_lt (hPeak k).1.2 hMid
  intro η B D hη hB hD hRegime ρ hρ
  have hMassEscape : Tendsto (fun k : ℕ =>
      h3PathActualSpectralHighRadialRemainder244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 (s k))) atTop atTop := by
    simpa only [h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244]
      using (hHigh η B D hη hB hD hRegime).1 ρ hρ.le
  exact h3Path_highRadialMassEscape_forces_dissipationPeaks244
    hH3 hClass s hsClass ρ hρ hMassEscape

end
end PrimeTensor.FirstMonomialTriad
