import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxSurplusGlobalPacking
import Mathlib.Tactic

/-!
# Audit: the unanchored tenth-power viscous residual is automatic

The accepted tenth-power residual contains an existential earlier viscous
alternative with an arbitrarily small positive width.  Its condition is

  z = t or z = x,   0 < width,   z + width < y,
  width * physicalViscousHeight / 4 < epsilon.

On any strict gap x < y and for any epsilon > 0 this is automatically
satisfiable by choosing z = x and a sufficiently small width, *regardless*
of the physical energy, flux, dissipation or Fourier radius.  The width is
not anchored to a PDE persistence modulus and the cost has no lower floor.

Consequently the negation of the tenth-power residual is impossible.  Both
native adverse-gap activity and integrated-surplus packing activity used in
the recent inverse-eleventh-power ledgers are therefore empty under their
original hypotheses.  Their formal theorems remain valid, but they cannot
provide a nonvacuous frequency obstruction as presently formulated.

This audit introduces no axioms or additional Navier--Stokes hypotheses.
A repair must require an independently fixed, PDE-certified width or an
actual positive cost (with the correct inequality direction), rather than
an existential arbitrarily short interval.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology Classical
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- On any nonempty interval, an arbitrary FINITE real-valued rate admits a
short positive interval whose nominal linear cost is below any positive
budget. This is the exact mathematical defect in the residual's last arm. -/
theorem thirdFullKinetic_signedLowMax_arbitraryWidth_smallCost244
    (x y A epsilon : ℝ) (hxy : x < y) (hEpsilon : 0 < epsilon) :
    ∃ width : ℝ, 0 < width ∧ x + width < y ∧ width * A < epsilon := by
  let c : ℝ := |A| + 1
  let width : ℝ := min ((y - x) / 2) (epsilon / (2 * c))
  have hc : 0 < c := by
    dsimp only [c]
    have hAbs : 0 ≤ |A| := abs_nonneg A
    linarith only [hAbs]
  have hGap : 0 < (y - x) / 2 := by linarith only [hxy]
  have hBudget : 0 < epsilon / (2 * c) :=
    div_pos hEpsilon (mul_pos (by norm_num) hc)
  have hwPos : 0 < width := by
    dsimp only [width]
    exact lt_min hGap hBudget
  have hwGap : width ≤ (y - x) / 2 := min_le_left _ _
  have hwBudget : width ≤ epsilon / (2 * c) := min_le_right _ _
  have hwInside : x + width < y := by
    linarith only [hxy, hwGap]
  have hAC : A ≤ c := by
    dsimp only [c]
    have hAbs : A ≤ |A| := le_abs_self A
    linarith only [hAbs]
  have hRate : width * A ≤ width * c :=
    mul_le_mul_of_nonneg_left hAC hwPos.le
  have hCost : width * c ≤ epsilon / 2 := by
    calc
      width * c ≤ (epsilon / (2 * c)) * c :=
        mul_le_mul_of_nonneg_right hwBudget hc.le
      _ = epsilon / 2 := by
        have hc0 : c ≠ 0 := ne_of_gt hc
        field_simp [hc0] <;> ring
  have hHalf : epsilon / 2 < epsilon := by linarith only [hEpsilon]
  exact ⟨width, hwPos, hwInside, (hRate.trans hCost).trans_lt hHalf⟩

/-- The tenth-power residual is TRUE at every finite physical state on any
strict physical time gap, merely because its existential viscous width is
not anchored below.  No Navier--Stokes estimate is used in this proof. -/
theorem thirdFullKinetic_signedLowMax_tenthResidual_automatic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R J : ℕ) (E eta epsilon x y t : ℝ)
    (hxy : x < y) (hEpsilon : 0 < epsilon) :
    ThirdFullKineticSignedLowMaxTenthPowerResidual244
      hH3 R J E eta epsilon x y t := by
  let X : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let Y : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 x
  let A : ℝ := thirdFullKineticSignedLowMaxPhysicalViscousHeight244
    R X Y (thirdFullKineticSignedLowMaxPhysicalMargin244 eta / 2) / 4
  obtain ⟨width, hwPos, hwInside, hwSmall⟩ :=
    thirdFullKinetic_signedLowMax_arbitraryWidth_smallCost244
      x y A epsilon hxy hEpsilon
  unfold ThirdFullKineticSignedLowMaxTenthPowerResidual244
  right
  right
  refine ⟨x, width, Or.inr rfl, hwPos, Or.inl hwInside, ?_⟩
  simpa only [A, X, Y] using hwSmall

/-- The accepted native-adverse activity predicate requires the negation of
an automatically true residual, so it is empty on every genuine gap. -/
theorem thirdFullKinetic_signedLowMax_nativeAdverseGap_impossible244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (eta : ℝ) (J : ℕ) (E epsilon : ℝ)
    (tau delta : ℕ → ℝ) (v R : ℕ → ℕ) (t : ℕ → ℝ)
    (k : ℕ)
    (hGap : tau (v k) + delta (v k) < tau (v (k + 1)))
    (hEpsilon : 0 < epsilon) :
    ¬ ThirdFullKineticSignedLowMaxNativeAdverseGap244
      hH3 eta J E epsilon tau delta v R t k := by
  intro hActive
  dsimp only [ThirdFullKineticSignedLowMaxNativeAdverseGap244] at hActive
  obtain ⟨_ht, _hAdverse, hNoResidual, _hDensity⟩ := hActive
  exact hNoResidual
    (thirdFullKinetic_signedLowMax_tenthResidual_automatic244
      hH3 (R k) J E eta epsilon
        (tau (v k) + delta (v k)) (tau (v (k + 1))) (t k)
      hGap hEpsilon)

/-- Integrated-surplus activity is likewise impossible: the existing PDE
surplus lemma supplies an adverse time, and the residual is automatically
true at THAT same time.  This demonstrates why the latest global packing
hypothesis cannot select a nonempty set of physical indices. -/
theorem thirdFullPhysical_signedLowMax_surplusPackingActive_impossible244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (tau : ℕ → ℝ) (N : ℕ → ℕ)
    (delta : ℕ → ℝ) (v R : ℕ → ℕ)
    (hSeparated : ∀ k l : ℕ, k < l →
      tau (v k) + delta (v k) < tau (v l))
    (hWindows : ∀ k : ℕ,
      tau (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (tau (v k)) (v k) (N (v k))
        (M (v k)) (delta (v k)))
    (eta : ℝ) (hEta : 0 < eta) (J : ℕ)
    (E epsilon : ℝ) (hEpsilon : 0 < epsilon) (k : ℕ) :
    ¬ ThirdFullKineticSignedLowMaxSurplusPackingActive244
      hH3 eta J E epsilon tau delta v R k := by
  intro hk
  obtain ⟨z, hz, hAdverse⟩ :=
    thirdFullPhysical_signedLowMax_surplusPackingActive_adverseTime244
      hH3 hClass b hb M tau N delta v R hSeparated hWindows
      eta hEta J E epsilon k hk
  have hReject : ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
      hH3 (R k) J E eta epsilon
        (tau (v k) + delta (v k)) (tau (v (k + 1))) z := by
    have hActive := hk
    dsimp only [ThirdFullKineticSignedLowMaxSurplusPackingActive244]
      at hActive
    exact hActive.2.2.2 z hz hAdverse
  have hGap : tau (v k) + delta (v k) < tau (v (k + 1)) :=
    hSeparated k (k + 1) (Nat.lt_succ_self k)
  exact hReject
    (thirdFullKinetic_signedLowMax_tenthResidual_automatic244
      hH3 (R k) J E eta epsilon
        (tau (v k) + delta (v k)) (tau (v (k + 1))) z
      hGap hEpsilon)

end
end PrimeTensor.FirstMonomialTriad
