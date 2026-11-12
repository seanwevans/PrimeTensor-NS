import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularViscousCapDichotomy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileDisjointViscousCharge
import Mathlib.Tactic

/-!
# Actual annular kinetic deficit: disjoint viscous clock or a cap spike

The preceding result gives, at each strict physical time, either the full
H3 dissipation D(t) exceeds an arbitrary cap H or the actual annular kinetic
deficit is at most the physical highpass kinetic mass times an explicit
linear coefficient times D(t). The highpass kinetic mass is itself bounded
by the *earlier* physical kinetic energy, by sharp Plancherel and kinetic
energy antitonicity. Thus a positive deficit floor epsilon on a cap-bounded
window forces the physical height

    epsilon / max(1, E0(b)*rho^6*Slope(b,H)) <= D(t)

at EVERY time on that window.

This module synchronizes that precise floor with the existing general
finite disjoint physical viscous-clock summation theorem. For a countable
family of pairwise separated windows, if the actual kinetic-excess branch
and positive deficit floor persist across each window, then EITHER some
window contains a genuine cap-exceeding physical H3 dissipation time, OR
the complete series of the normalized height-times-width costs is
summable against one and the same actual finite H3 dissipation integral.

The persistence hypotheses are displayed, not inferred from a single-time
kinetic deficit. No uniform widths, no L2_t viscous estimate, and no
terminal continuation theorem follow from this disjunction alone.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeAnnularDisjointClock244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceAnnularDisjointClock244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The actual physical sharp highpass velocity cannot contain more
ordinary L2 kinetic square mass than the earlier kinetic anchor. -/
theorem thirdFullPhysical_actualSharpHighMass_le_kineticAnchor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (rho : ℝ) :
    thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho ≤
      velocityH3Energy0At u b := by
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 ht.1), ht.2⟩
  have hbAbs : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hb.1, hb.2⟩
  have hKin : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    (h3Audit_initialKineticEnergy_antitoneOn_positiveInterval hH3)
      hbAbs htAbs ht.1.le
  have hNorm : ‖U‖ ^ 2 = velocityH3Energy0At u t :=
    h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy hH3 t htAbs
  have hHigh := thirdFullPhysical_sharpVectorHighpass_norm_le244 rho U
  have hSq :
      ‖U - thirdFullPhysicalSharpLowCutoffHilbert244 rho U‖ ^ 2 ≤ ‖U‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hHigh
  change ‖U - thirdFullPhysicalSharpLowCutoffHilbert244 rho U‖ ^ 2 ≤ _
  calc
    ‖U - thirdFullPhysicalSharpLowCutoffHilbert244 rho U‖ ^ 2 ≤
        ‖U‖ ^ 2 := hSq
    _ = velocityH3Energy0At u t := hNorm
    _ ≤ velocityH3Energy0At u b := hKin

/-- Finite, positive normalizer for the cap-H physical viscous clock.
The `max 1` avoids division by zero even for vanishing highpass kinetic mass,
zero inner cutoff, or a zero kinetic anchor. -/
noncomputable def thirdFullPhysicalAnnularCapClockFactor244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b rho H : ℝ) : ℝ :=
  max 1 (velocityH3Energy0At u b * (rho ^ 2) ^ 3 *
    thirdFullPhysicalOuterViscousCapSlope244 u b H)

/-- The normalization used by every selected physical clock is positive. -/
theorem thirdFullPhysical_annularCapClockFactor_pos244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b rho H : ℝ) :
    0 < thirdFullPhysicalAnnularCapClockFactor244 u b rho H := by
  unfold thirdFullPhysicalAnnularCapClockFactor244
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- Genuine single-time normalized viscous height: a positive actual
kinetic-deficit floor on the cap branch forces a full-H3 dissipation floor.
It is *not* an assumption that the kinetic highpass mass has a positive
lower bound. The proof uses only its kinetic upper bound. -/
theorem thirdFullPhysical_annularDeficit_forces_normalizedViscousFloor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (rho sigma : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (H epsilon : ℝ) (hH : 0 ≤ H)
    (hCap : velocityH3DissipationAt u t ≤ H)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (hFloor : epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma) :
    epsilon / thirdFullPhysicalAnnularCapClockFactor244 u b rho H ≤
      velocityH3DissipationAt u t := by
  let E : ℝ := velocityH3Energy0At u b
  let M : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho
  let W : ℝ := (rho ^ 2) ^ 3
  let L : ℝ := thirdFullPhysicalOuterViscousCapSlope244 u b H
  let D : ℝ := velocityH3DissipationAt u t
  let C : ℝ := thirdFullPhysicalAnnularCapClockFactor244 u b rho H
  have hMass : M ≤ E :=
    thirdFullPhysical_actualSharpHighMass_le_kineticAnchor244
      hH3 hClass b hb t ht rho
  have hW : 0 ≤ W := pow_nonneg (sq_nonneg rho) 3
  have hE : 0 ≤ E := velocityH3Energy0At_nonneg u b
  have hL : 0 ≤ L := by
    have hE0 : 0 ≤ velocityH3Energy0At u b :=
      velocityH3Energy0At_nonneg u b
    have hB : 0 ≤ 1 + 6 * velocityH3Energy0At u b := by
      positivity
    dsimp only [L, thirdFullPhysicalOuterViscousCapSlope244]
    positivity
  have hD : 0 ≤ D := velocityH3DissipationAt_nonneg u t
  have hP : M * W * L ≤ E * W * L := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hMass hW) hL
  have hPC : E * W * L ≤ C := by
    exact le_max_right _ _
  have hPay :
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma ≤
        M * W * L * D := by
    simpa only [M, W, L, D] using
      (thirdFullPhysical_kineticDeficit_linearViscousChargeBelowCap244
        hH3 hClass b hb rho sigma hRho hOrder t ht H hCap hExcess)
  have hDom : epsilon ≤ C * D := by
    calc
      epsilon ≤ thirdFullPhysicalActualAnnularKineticDeficit244
          hH3 b t rho sigma := hFloor
      _ ≤ M * W * L * D := hPay
      _ ≤ C * D := mul_le_mul_of_nonneg_right (hP.trans hPC) hD
  have hC : 0 < C := thirdFullPhysical_annularCapClockFactor_pos244 u b rho H
  have hDom' : epsilon ≤ D * C := by
    simpa only [mul_comm C D] using hDom
  exact (div_le_iff₀ hC).2 hDom'

/-- Countably many pairwise disjoint PHYSICAL time windows satisfying an
actual annular kinetic-excess branch and a positive kinetic-deficit floor.

Either a selected window contains a genuine H3 dissipation cap spike,
or the entire normalized width-times-deficit-floor series is summable and
its partial sums are charged to ONE common finite physical viscous action.

Only the persistence of the two *kinetic* conditions across each selected
window is a premise: no cap-boundedness or persistence of viscosity is
postulated. That cap is discharged by the disjunction.
-/
theorem thirdFullPhysical_disjointAnnularDeficit_capSpikeOrSummableCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (p delta rho sigma H epsilon : ℕ → ℝ)
    (hRho : ∀ k, 0 ≤ rho k)
    (hOrder : ∀ k, rho k ≤ sigma k)
    (hH : ∀ k, 0 ≤ H k)
    (hEps : ∀ k, 0 < epsilon k)
    (hStart : ∀ k, a ≤ p k)
    (hWidth : ∀ k, 0 ≤ delta k)
    (hEnd : ∀ k, p k + delta k ≤ T)
    (hSeparate : ∀ k, p k + delta k ≤ p (k + 1))
    (hTimes : ∀ k s, s ∈ Set.Icc (p k) (p k + delta k) →
      s ∈ Set.Ioo b T)
    (hExcess : ∀ k s, s ∈ Set.Icc (p k) (p k + delta k) →
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          (rho k) (velocityH3Energy0At u b)) ≤
      ((rho k ^ 2 + sigma k ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (rho k))
    (hFloor : ∀ k s, s ∈ Set.Icc (p k) (p k + delta k) →
      epsilon k ≤
        thirdFullPhysicalActualAnnularKineticDeficit244
          hH3 b s (rho k) (sigma k)) :
    (∃ k : ℕ, ∃ s : ℝ,
      s ∈ Set.Icc (p k) (p k + delta k) ∧
        H k < velocityH3DissipationAt u s) ∨
    (Summable (fun k : ℕ =>
      delta k * (epsilon k /
        thirdFullPhysicalAnnularCapClockFactor244 u b (rho k) (H k))) ∧
     Tendsto (fun k : ℕ =>
      delta k * (epsilon k /
        thirdFullPhysicalAnnularCapClockFactor244 u b (rho k) (H k)))
       atTop (𝓝 (0 : ℝ)) ∧
     ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        delta k * (epsilon k /
          thirdFullPhysicalAnnularCapClockFactor244 u b (rho k) (H k))) ≤
        ∫ r in a..T, velocityH3DissipationAt u r) := by
  classical
  by_cases hSpike : ∃ k : ℕ, ∃ s : ℝ,
      s ∈ Set.Icc (p k) (p k + delta k) ∧
        H k < velocityH3DissipationAt u s
  · exact Or.inl hSpike
  · right
    let A : ℕ → ℝ := fun k =>
      epsilon k / thirdFullPhysicalAnnularCapClockFactor244 u b (rho k) (H k)
    have hCap (k : ℕ) (s : ℝ)
        (hs : s ∈ Set.Icc (p k) (p k + delta k)) :
        velocityH3DissipationAt u s ≤ H k := by
      apply le_of_not_gt
      intro hAbove
      exact hSpike ⟨k, s, hs, hAbove⟩
    have hPoint (k : ℕ) (s : ℝ)
        (hs : s ∈ Set.Icc (p k) (p k + delta k)) :
        A k ≤ velocityH3DissipationAt u s := by
      exact thirdFullPhysical_annularDeficit_forces_normalizedViscousFloor244
        hH3 hClass b hb (rho k) (sigma k) (hRho k) (hOrder k)
        s (hTimes k s hs) (H k) (epsilon k) (hH k)
        (hCap k s hs) (hExcess k s hs) (hFloor k s hs)
    have hBudget : ∀ m : ℕ,
        (∑ k ∈ Finset.range m, delta k * A k) ≤
          ∫ r in a..T, velocityH3DissipationAt u r :=
      h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
        (velocityH3DissipationAt u) a T p delta A
        hClass.terminal_start.2.le
        (fun r => velocityH3DissipationAt_nonneg u r)
        hDInt hStart hWidth hEnd hSeparate hPoint
    have hA (k : ℕ) : 0 ≤ A k := by
      exact div_nonneg (hEps k).le
        (thirdFullPhysical_annularCapClockFactor_pos244 u b (rho k) (H k)).le
    have hNonneg (k : ℕ) : 0 ≤ delta k * A k :=
      mul_nonneg (hWidth k) (hA k)
    have hSummable : Summable (fun k : ℕ => delta k * A k) :=
      summable_of_sum_range_le hNonneg hBudget
    have hZero : Tendsto (fun k : ℕ => delta k * A k)
        atTop (𝓝 (0 : ℝ)) := hSummable.tendsto_atTop_zero
    exact ⟨hSummable, hZero, hBudget⟩

end
end PrimeTensor.FirstMonomialTriad
