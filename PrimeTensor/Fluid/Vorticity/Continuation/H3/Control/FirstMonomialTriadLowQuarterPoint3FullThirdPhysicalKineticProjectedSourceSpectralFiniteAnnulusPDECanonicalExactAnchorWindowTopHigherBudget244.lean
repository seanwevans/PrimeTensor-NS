import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorWindowInnerHigherEscape244
import Mathlib.Tactic

/-!
# Canonical full-window top-order higher moments: conditional spacetime budget

The established canonical strict-time physical q^(4+m) moment floor is
uniform over each exact disjoint PDE window:

    ENNReal.ofReal ((R_k^2)^m * R_k^3/8) <= M_(4+m)(s).

This file identifies the ADDITIONAL analytic cost of an assumed *real-valued
nonnegative, time-integrable upper envelope* of the extended moments.
Under such an envelope f_m, all original windows are disjoint and therefore

    Summable (fun k => delta_k * ((R_k^2)^m * R_k^3/8)).

Equivalently delta_k * R_k^(2*m+3) tends to zero. The envelope is NOT
established by physical H^3 dissipation integrability when m > 0.
No additional regularity, moment finiteness, or continuation is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Nonnegative disjoint time windows are summably charged by any
interval-integrable nonnegative real function that dominates the respective
constant window floors. -/
theorem h3Path_scalar_disjointWindows_integrableMajorant_weightedCharge244
    (f : ℝ → ℝ) (a T : ℝ) (t δ A : ℕ → ℝ)
    (haT : a ≤ T)
    (hf : ∀ s : ℝ, 0 ≤ f s)
    (hfInt : IntervalIntegrable f volume a T)
    (ht : ∀ k, a ≤ t k)
    (hδ : ∀ k, 0 ≤ δ k)
    (hEnd : ∀ k, t k + δ k ≤ T)
    (hSep : ∀ k, t k + δ k ≤ t (k + 1))
    (hA : ∀ k, 0 ≤ A k)
    (hMajor : ∀ k s, s ∈ Set.Icc (t k) (t k + δ k) → A k ≤ f s) :
    Summable (fun k => δ k * A k) := by
  have hBound : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, δ k * A k) ≤
        ∫ s in a..T, f s :=
    h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
      f a T t δ A haT hf hfInt ht hδ hEnd hSep hMajor
  have hNonneg : ∀ k : ℕ, 0 ≤ δ k * A k := by
    intro k
    exact mul_nonneg (hδ k) (hA k)
  exact h3Path_nonnegativeBoundedRangeSums_summable244
    (fun k => δ k * A k) (∫ s in a..T, f s) hNonneg hBound

/-- A real upper envelope for the actual physical extended higher-radial
moment controls the exact nonnegative real lower bound on the same slice.
The comparison does not assume the extended moment is finite in general. -/
theorem h3Path_physicalTopHigherMoment_upperEnvelope_forces_realFloor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (m : ℕ) (F floor : ℝ)
    (hF : 0 ≤ F)
    (hMomentFloor : ENNReal.ofReal floor ≤
      h3TerminalPhysicalExtendedHigherRadialMomentAt hH3 hClass m s hs)
    (hMomentCeiling :
      h3TerminalPhysicalExtendedHigherRadialMomentAt hH3 hClass m s hs ≤
        ENNReal.ofReal F) :
    floor ≤ F := by
  exact (ENNReal.ofReal_le_ofReal_iff hF).1
    (hMomentFloor.trans hMomentCeiling)

/-- Finite accumulated weighted window charges force critical compression
at every specified polynomial radial order, with no limit interchange
involving the physical extended moments. -/
theorem h3Path_scalar_summable_higherCubicCharge_forces_widthCompression244
    (R δ : ℕ → ℝ) (m : ℕ)
    (hSum : Summable (fun k =>
      δ k * (((R k) ^ 2) ^ m * ((R k) ^ 3 / 8)))) :
    Tendsto (fun k => δ k * (R k) ^ (2 * m + 3))
      atTop (𝓝 (0 : ℝ)) := by
  have hZero : Tendsto (fun k =>
      8 * (δ k * (((R k) ^ 2) ^ m * ((R k) ^ 3 / 8))))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      hSum.tendsto_atTop_zero.const_mul (8 : ℝ)
  have hIdent : (fun k => δ k * (R k) ^ (2 * m + 3)) =
      (fun k => 8 * (δ k * (((R k) ^ 2) ^ m * ((R k) ^ 3 / 8)))) := by
    funext k
    rw [pow_add, pow_mul]
    ring
  rw [hIdent]
  exact hZero

/-- On the SAME exact canonical disjoint PDE windows, any physically
admissible nonnegative, time-integrable real upper envelope of the EXISTING
extended physical top-order moment forces a summable higher-frequency
window charge and a polynomial inverse-width compression. This is a
conditional implication, NOT an assumed higher-order spacetime estimate. -/
theorem h3Path_noL2Trace_exactAnchor_integrableTopHigherEnvelope_forces_widthCompression244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
    ∃ hτ : (∀ n, τ n ∈ Set.Ioo a T),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, K (v k) =
        ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        0 < δ (v k)) ∧
      (∀ m k : ℕ, ∀ s : ℝ,
        s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
        ∃ hs : s ∈ Set.Ioo a T,
          ENNReal.ofReal (((((v k : ℝ) + 1) ^ 2) ^ m) *
            (((v k : ℝ) + 1) ^ 3 / 8)) ≤
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass m s hs) ∧
      (∀ m : ℕ, ∀ F : ℝ → ℝ,
        (∀ s : ℝ, 0 ≤ F s) →
        IntervalIntegrable F volume a T →
        (∀ s : ℝ, ∀ hs : s ∈ Set.Ioo a T,
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass m s hs ≤ ENNReal.ofReal (F s)) →
        Summable (fun k => δ (v k) *
          (((((v k : ℝ) + 1) ^ 2) ^ m) *
            (((v k : ℝ) + 1) ^ 3 / 8))) ∧
        Tendsto (fun k => δ (v k) *
          (((v k : ℝ) + 1) ^ (2 * m + 3)))
          atTop (𝓝 (0 : ℝ))) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSep, hCanonical, hWindow, _hEscape⟩ :=
    h3Path_noL2Trace_exactAnchor_uniformWindowTopHigherEscape244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
    hSep, hCanonical, hWindow, ?_⟩
  intro m F hF hfInt hUpper
  let R : ℕ → ℝ := fun k => (v k : ℝ) + 1
  let A : ℕ → ℝ := fun k => ((R k) ^ 2) ^ m * ((R k) ^ 3 / 8)
  have hW (k : ℕ) : 0 ≤ δ (v k) := (hCanonical k).2.2.le
  have hEnd (k : ℕ) : τ (v k) + δ (v k) ≤ T := by
    have hNext := hSep k (k + 1) (Nat.lt_succ_self k)
    exact (lt_trans hNext (hτ (v (k + 1))).2).le
  have hR (k : ℕ) : 0 ≤ R k := by
    dsimp only [R]
    positivity
  have hA (k : ℕ) : 0 ≤ A k := by
    dsimp only [A]
    exact mul_nonneg (pow_nonneg (sq_nonneg (R k)) m)
      (div_nonneg (pow_nonneg (hR k) 3) (by norm_num))
  have hFloor (k : ℕ) (s : ℝ)
      (hsWindow : s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
      A k ≤ F s := by
    obtain ⟨hs, hMoment⟩ := hWindow m k s hsWindow
    have hCompare := h3Path_physicalTopHigherMoment_upperEnvelope_forces_realFloor244
      hH3 hClass hs m (F s) (A k) (hF s)
      (by simpa only [A, R] using hMoment) (hUpper s hs)
    exact hCompare
  have hSum : Summable (fun k => δ (v k) * A k) :=
    h3Path_scalar_disjointWindows_integrableMajorant_weightedCharge244
      F a T (fun k => τ (v k)) (fun k => δ (v k)) A
      hClass.terminal_start.2.le hF hfInt
      (fun k => (hτ (v k)).1.le) hW hEnd
      (fun k => (hSep k (k + 1) (Nat.lt_succ_self k)).le)
      hA hFloor
  have hCompress : Tendsto (fun k => δ (v k) *
      (R k) ^ (2 * m + 3)) atTop (𝓝 (0 : ℝ)) :=
    h3Path_scalar_summable_higherCubicCharge_forces_widthCompression244
      R (fun k => δ (v k)) m hSum
  constructor
  · simpa only [R, A] using hSum
  · simpa only [R] using hCompress

end
end PrimeTensor.FirstMonomialTriad
