import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularDisjointClockCharge
import Mathlib.Tactic

/-!
# Annular kinetic deficits pay an unconditional truncated physical H³ clock

The disjoint annular clock theorem has a pointwise cap-spike alternative.
For a persistent annular kinetic-excess branch and positive deficit floor,
that alternative is unnecessary: a time with D₃(t) > H already pays H,
while a time with D₃(t) ≤ H pays epsilon / C(b,rho,H).

Thus EVERY physical time on a kinetic-persistent window pays the strictly
positive truncated height min(H,epsilon/C), provided H,epsilon > 0.
Disjoint window summation is unconditional; no L∞ cap on physical H³
dissipation is asserted or required. The persistence assumptions on the
actual annular nonlinear Young-gap deficit remain explicit.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeAnnularTruncatedClock244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceAnnularTruncatedClock244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Physical H³ dissipation height paid in BOTH branches of a positive cap.
The normalizer is built solely from the earlier physical kinetic anchor,
the inner annular radius, and the chosen cap. -/
noncomputable def thirdFullPhysicalAnnularTruncatedClockHeight244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b rho H epsilon : ℝ) : ℝ :=
  min H (epsilon / thirdFullPhysicalAnnularCapClockFactor244 u b rho H)

/-- Positive cap and positive actual deficit floor give positive truncated
height, even if the kinetic anchor or inner radius vanishes. -/
theorem thirdFullPhysical_annularTruncatedClockHeight_pos244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b rho H epsilon : ℝ) (hH : 0 < H) (hEpsilon : 0 < epsilon) :
    0 < thirdFullPhysicalAnnularTruncatedClockHeight244 u b rho H epsilon := by
  unfold thirdFullPhysicalAnnularTruncatedClockHeight244
  exact lt_min hH
    (div_pos hEpsilon
      (thirdFullPhysical_annularCapClockFactor_pos244 u b rho H))

/-- There is NO cap-spike escape from the pointwise viscous height bound:
if D₃(t) is above the cap, it pays H; if below, the previous physical
annular-deficit theorem forces epsilon/C. This is a physical-time bound,
not a surrogate or an assumed viscosity bound. -/
theorem thirdFullPhysical_annularDeficit_forces_truncatedClockHeight244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (rho sigma : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (H epsilon : ℝ) (hH : 0 ≤ H)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (hFloor : epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma) :
    thirdFullPhysicalAnnularTruncatedClockHeight244 u b rho H epsilon ≤
      velocityH3DissipationAt u t := by
  change min H
      (epsilon / thirdFullPhysicalAnnularCapClockFactor244 u b rho H) ≤
    velocityH3DissipationAt u t
  by_cases hCap : velocityH3DissipationAt u t ≤ H
  · exact (min_le_right H _).trans
      (thirdFullPhysical_annularDeficit_forces_normalizedViscousFloor244
        hH3 hClass b hb rho sigma hRho hOrder t ht H epsilon
        hH hCap hExcess hFloor)
  · exact (min_le_left H _).trans (le_of_lt (lt_of_not_ge hCap))

/-- A countable family of ACTUAL physical time windows with persistent
kinetic excess and annular deficit MUST pay summable disjoint H³ viscous
charges. In contrast with the previous dichotomy, there is no cap-spike
alternative or assumption of a cap on any part of any window.

For H_k,epsilon_k > 0, every truncated height is strictly positive.
The explicit cost is delta_k * min(H_k,epsilon_k/C_k(H_k)); all partial
sums are bounded by one common physical ∫_a^T D₃(t) dt. -/
theorem thirdFullPhysical_disjointAnnularDeficit_truncatedClockSummable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (p delta rho sigma H epsilon : ℕ → ℝ)
    (hRho : ∀ k, 0 ≤ rho k)
    (hOrder : ∀ k, rho k ≤ sigma k)
    (hH : ∀ k, 0 < H k)
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
    (Summable (fun k : ℕ =>
      delta k * thirdFullPhysicalAnnularTruncatedClockHeight244
        u b (rho k) (H k) (epsilon k)) ∧
     Tendsto (fun k : ℕ =>
      delta k * thirdFullPhysicalAnnularTruncatedClockHeight244
        u b (rho k) (H k) (epsilon k)) atTop (𝓝 (0 : ℝ)) ∧
     ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        delta k * thirdFullPhysicalAnnularTruncatedClockHeight244
          u b (rho k) (H k) (epsilon k)) ≤
        ∫ r in a..T, velocityH3DissipationAt u r) := by
  classical
  let A : ℕ → ℝ := fun k =>
    thirdFullPhysicalAnnularTruncatedClockHeight244
      u b (rho k) (H k) (epsilon k)
  have hPoint (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (p k) (p k + delta k)) :
      A k ≤ velocityH3DissipationAt u s := by
    exact thirdFullPhysical_annularDeficit_forces_truncatedClockHeight244
      hH3 hClass b hb (rho k) (sigma k) (hRho k) (hOrder k)
      s (hTimes k s hs) (H k) (epsilon k) (hH k).le
      (hExcess k s hs) (hFloor k s hs)
  have hBudget : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, delta k * A k) ≤
        ∫ r in a..T, velocityH3DissipationAt u r :=
    h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
      (velocityH3DissipationAt u) a T p delta A
      hClass.terminal_start.2.le
      (fun r => velocityH3DissipationAt_nonneg u r)
      hDInt hStart hWidth hEnd hSeparate hPoint
  have hPositive (k : ℕ) : 0 < A k :=
    thirdFullPhysical_annularTruncatedClockHeight_pos244
      u b (rho k) (H k) (epsilon k) (hH k) (hEps k)
  have hNonneg (k : ℕ) : 0 ≤ delta k * A k :=
    mul_nonneg (hWidth k) (hPositive k).le
  have hSummable : Summable (fun k : ℕ => delta k * A k) :=
    summable_of_sum_range_le hNonneg hBudget
  have hZero : Tendsto (fun k : ℕ => delta k * A k)
      atTop (𝓝 (0 : ℝ)) := hSummable.tendsto_atTop_zero
  exact ⟨hSummable, hZero, hBudget⟩

end
end PrimeTensor.FirstMonomialTriad
