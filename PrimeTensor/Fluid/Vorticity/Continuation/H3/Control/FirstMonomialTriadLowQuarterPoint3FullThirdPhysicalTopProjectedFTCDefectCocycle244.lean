import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopDenseFTCClosure244
import Mathlib.Tactic

/-!
# Additive physical projected FTC defects and gluing local weak evolution

The actual L² velocity and its continuous projected source produce an
interval-valued FTC defect, without presupposing its vanishing. This file
proves the exact interval cocycle, a quantitative defect triangle estimate,
and the scalar test-pairing identity against the continuous Bochner source.

Two local scalar solenoidal weak-FTC windows glue into the larger interval;
moreover each local window may have a different dense family of weak-test
sampling times.  These statements avoid requiring a global pointwise weak
FTC as an input to local constructions.  Crucially, neither the cocycle
nor gluing proves the local weak evolution identity by itself.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The actual Hilbert FTC defect is an additive interval 1-cocycle.
This is unconditional for strictly preterminal intervals because the
projected source is Bochner integrable on each of them. -/
theorem h3Path_projectedFTCDefect_cocycle244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b)
    (hbc : b < c) (hc : c < T) :
    h3PathActualProjectedMomentumFTCDefect244 hH3 a c =
      h3PathActualProjectedMomentumFTCDefect244 hH3 a b +
        h3PathActualProjectedMomentumFTCDefect244 hH3 b c := by
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hAB : IntervalIntegrable G volume a b :=
    h3Path_actualProjectedMomentumSource_intervalIntegrableStrict244
      hH3 ha hab (lt_trans hbc hc)
  have hBC : IntervalIntegrable G volume b c :=
    h3Path_actualProjectedMomentumSource_intervalIntegrableStrict244
      hH3 (lt_trans ha hab) hbc hc
  have hAdd :
      (∫ s in a..b, G s) + (∫ s in b..c, G s) =
        ∫ s in a..c, G s :=
    intervalIntegral.integral_add_adjacent_intervals hAB hBC
  change F c - F a - (∫ s in a..c, G s) =
    (F b - F a - (∫ s in a..b, G s)) +
      (F c - F b - (∫ s in b..c, G s))
  rw [← hAdd]
  abel

/-- Quantitative accumulation: the long-interval evolution defect is
bounded by the sum of the two actual short-interval defects. -/
theorem h3Path_projectedFTCDefect_norm_le_split244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b)
    (hbc : b < c) (hc : c < T) :
    ‖h3PathActualProjectedMomentumFTCDefect244 hH3 a c‖ ≤
      ‖h3PathActualProjectedMomentumFTCDefect244 hH3 a b‖ +
        ‖h3PathActualProjectedMomentumFTCDefect244 hH3 b c‖ := by
  rw [h3Path_projectedFTCDefect_cocycle244 hH3 ha hab hbc hc]
  exact norm_add_le _ _

/-- The scalar defect seen by a weak test is exactly the velocity-increment
pairing minus the interval integral of the (already integrable) projected
source pairing. This is the residual needed by a distributional proof. -/
theorem h3Path_projectedFTCDefect_solenoidalPairing_eq_residual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (φ : H3WeakTestVector) :
    inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PathActualProjectedMomentumFTCDefect244 hH3 a b) =
      inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3AuditInitialOldPhysicalHilbertTotal hH3 b -
          h3AuditInitialOldPhysicalHilbertTotal hH3 a) -
      ∫ s in a..b,
        inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PathActualProjectedMomentumSource244 hH3 s) := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ
  have hGInt : IntervalIntegrable G volume a b :=
    h3Path_actualProjectedMomentumSource_intervalIntegrableStrict244
      hH3 ha hab hb
  have hComm :
      inner ℝ ψ (∫ s in a..b, G s) =
        ∫ s in a..b, inner ℝ ψ (G s) := by
    change ((innerSL ℝ) ψ) (∫ s in a..b, G s) =
      ∫ s in a..b, ((innerSL ℝ) ψ) (G s)
    exact (((innerSL ℝ) ψ).intervalIntegral_comp_comm hGInt).symm
  change inner ℝ ψ
      (h3AuditInitialOldPhysicalHilbertTotal hH3 b -
        h3AuditInitialOldPhysicalHilbertTotal hH3 a -
        ∫ s in a..b, G s) =
    inner ℝ ψ
      (h3AuditInitialOldPhysicalHilbertTotal hH3 b -
        h3AuditInitialOldPhysicalHilbertTotal hH3 a) -
      ∫ s in a..b, inner ℝ ψ (G s)
  rw [inner_sub_right, hComm]

/-- The scalar weak residual inherits the exact additive cocycle, with no
assumption that either local scalar residual vanishes. -/
theorem h3Path_projectedFTCDefect_weakPairing_cocycle244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b)
    (hbc : b < c) (hc : c < T)
    (φ : H3WeakTestVector) :
    inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PathActualProjectedMomentumFTCDefect244 hH3 a c) =
    inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PathActualProjectedMomentumFTCDefect244 hH3 a b) +
    inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PathActualProjectedMomentumFTCDefect244 hH3 b c) := by
  rw [h3Path_projectedFTCDefect_cocycle244 hH3 ha hab hbc hc]
  simp only [inner_add_right]

/-- Two local solenoidal weak FTC identities glue exactly at their common
physical time. The actual physical velocity and projected source are shared
across both windows; no global weak FTC assumption is used. -/
theorem h3Path_solenoidalWeakFTC_glue_adjacent244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b)
    (hbc : b < c) (hc : c < T)
    (hAB : H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b)
    (hBC : H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) b c) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a c := by
  have hZeroAB :=
    (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
      hH3 ha hab (lt_trans hbc hc)).2 hAB
  have hZeroBC :=
    (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
      hH3 (lt_trans ha hab) hbc hc).2 hBC
  apply (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha (lt_trans hab hbc) hc).1
  intro r hr
  by_cases hrb : r ≤ b
  · exact hZeroAB r ⟨hr.1, hrb⟩
  · have hbr : b < r := lt_of_not_ge hrb
    have hAdd := h3Path_projectedFTCDefect_cocycle244
      hH3 ha hab hbr (lt_of_le_of_lt hr.2 hc)
    rw [hZeroAB b ⟨hab.le, le_rfl⟩,
        hZeroBC r ⟨hbr.le, hr.2⟩] at hAdd
    simpa using hAdd

/-- Weak identities may be sampled on DISTINCT dense temporal families on
two adjacent windows. Weak-determination and strong Hilbert continuity
close each window before the cocycle joins them. -/
theorem h3Path_solenoidalWeakFTC_glue_denseWeakPairings244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b)
    (hbc : b < c) (hc : c < T)
    {D₁ D₂ : Type*}
    (ι₁ : D₁ → Set.Icc a b)
    (ι₂ : D₂ → Set.Icc b c)
    (hDense₁ : DenseRange ι₁)
    (hDense₂ : DenseRange ι₂)
    (hPair₁ : ∀ d : D₁, ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PathActualProjectedMomentumFTCDefect244 hH3 a (ι₁ d : ℝ)) = 0)
    (hPair₂ : ∀ d : D₂, ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PathActualProjectedMomentumFTCDefect244 hH3 b (ι₂ d : ℝ)) = 0) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a c := by
  have hAB := h3Path_solenoidalWeakFTC_of_denseEndpointWeakPairings244
    hH3 ha hab (lt_trans hbc hc) ι₁ hDense₁ hPair₁
  have hBC := h3Path_solenoidalWeakFTC_of_denseEndpointWeakPairings244
    hH3 (lt_trans ha hab) hbc hc ι₂ hDense₂ hPair₂
  exact h3Path_solenoidalWeakFTC_glue_adjacent244
    hH3 ha hab hbc hc hAB hBC

end
end PrimeTensor.FirstMonomialTriad
