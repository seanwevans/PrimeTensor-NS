import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECriticalSourceCeilingTightness244
import Mathlib.Tactic

/-!
# Canonical projected physical source envelope on strict-time windows

The selected quadratic-sharp coefficient C is an arbitrary upper ceiling on
‖Δu - Leray(u·∇u)‖ over a compact interior time interval. Divergence of that
chosen C does NOT alone force growth of the physical source. Here we construct
the intrinsic least upper envelope as the supremum of actual source norms.
On every nonempty strict-time compact interval, physical L² continuity
makes that supremum a genuine attained maximum.

Under an *additional* ceiling-efficiency hypothesis, the source-ceiling
escape theorem transfers to this intrinsic envelope, and hence to actual
physical source observations somewhere in the chosen window. Efficiency is
not established here, and no source blowup at the anchor time is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Intrinsic least uniform L² norm ceiling for the *actual* projected
momentum source on [a,b]. Used only with a strictly interior a < b < T. -/
noncomputable def h3PathActualProjectedSourceWindowEnvelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℝ) : ℝ :=
  sSup ((fun t : ℝ =>
    ‖h3PathActualProjectedMomentumSource244 hH3 t‖) '' Set.Icc a b)

/-- The canonical norm envelope is attained on every physical strict-time
window: the source norm is continuous and the interval is compact. -/
theorem h3Path_actualSourceWindowEnvelope_attained244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    ∃ t : ℝ, t ∈ Set.Icc a b ∧
      (∀ s : ℝ, s ∈ Set.Icc a b →
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
          ‖h3PathActualProjectedMomentumSource244 hH3 t‖) ∧
      h3PathActualProjectedSourceWindowEnvelope244 hH3 a b =
        ‖h3PathActualProjectedMomentumSource244 hH3 t‖ := by
  let f : ℝ → ℝ := fun t =>
    ‖h3PathActualProjectedMomentumSource244 hH3 t‖
  have hf : ContinuousOn f (Set.Icc a b) := by
    dsimp only [f]
    exact (h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 ha hab hb).norm
  have hNonempty : (Set.Icc a b).Nonempty :=
    ⟨a, ⟨le_rfl, hab.le⟩⟩
  obtain ⟨t, ht, htMax⟩ :=
    isCompact_Icc.exists_isMaxOn hNonempty hf
  have hBound : ∀ s : ℝ, s ∈ Set.Icc a b → f s ≤ f t :=
    isMaxOn_iff.mp htMax
  have hImageNonempty : (f '' Set.Icc a b).Nonempty :=
    ⟨f t, ⟨t, ht, rfl⟩⟩
  have hUpper : sSup (f '' Set.Icc a b) ≤ f t := by
    apply csSup_le hImageNonempty
    intro x hx
    rcases hx with ⟨s, hs, rfl⟩
    exact hBound s hs
  have hBdd : BddAbove (f '' Set.Icc a b) :=
    isCompact_Icc.bddAbove_image hf
  have hLower : f t ≤ sSup (f '' Set.Icc a b) :=
    le_csSup hBdd ⟨t, ht, rfl⟩
  refine ⟨t, ht, ?_, ?_⟩
  · intro s hs
    exact hBound s hs
  · change sSup (f '' Set.Icc a b) = f t
    exact le_antisymm hUpper hLower

/-- The attained envelope dominates every pointwise physical source norm
on the chosen strict-time interval. -/
theorem h3Path_actualSourceWindowEnvelope_pointwise_le244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ≤
      h3PathActualProjectedSourceWindowEnvelope244 hH3 a b := by
  obtain ⟨r, hr, hMax, hEq⟩ :=
    h3Path_actualSourceWindowEnvelope_attained244 hH3 ha hab hb
  rw [hEq]
  exact hMax t ht

/-- The intrinsic envelope is no larger than ANY proposed physical source
ceiling on the whole window, including the existential ceilings used to
build quadratic-sharp PDE clocks. -/
theorem h3Path_actualSourceWindowEnvelope_le_anyCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (C : ℝ)
    (hCeiling : ∀ t : ℝ, t ∈ Set.Icc a b →
      ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ≤ C) :
    h3PathActualProjectedSourceWindowEnvelope244 hH3 a b ≤ C := by
  obtain ⟨t, ht, _hMax, hEq⟩ :=
    h3Path_actualSourceWindowEnvelope_attained244 hH3 ha hab hb
  rw [hEq]
  exact hCeiling t ht

/-- For each large threshold, envelope divergence produces a real physical
observation time where the L² projected-source norm reaches that threshold.
There is no assertion that the maximizing time equals the initial anchor. -/
theorem h3Path_sourceWindowEnvelopeEscape_forces_windowPeaks244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℕ → ℝ)
    (ha : ∀ k, 0 < a k) (hab : ∀ k, a k < b k)
    (hb : ∀ k, b k < T)
    (hEscape : Tendsto (fun k : ℕ =>
      h3PathActualProjectedSourceWindowEnvelope244 hH3 (a k) (b k))
      atTop atTop) (M : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∃ t : ℝ, t ∈ Set.Icc (a k) (b k) ∧
      M ≤ ‖h3PathActualProjectedMomentumSource244 hH3 t‖ := by
  have hLarge := hEscape.eventually (eventually_ge_atTop M)
  filter_upwards [hLarge] with k hk
  obtain ⟨t, ht, _hMax, hEq⟩ :=
    h3Path_actualSourceWindowEnvelope_attained244 hH3
      (ha k) (hab k) (hb k)
  refine ⟨t, ht, ?_⟩
  rw [hEq] at hk
  exact hk

/-- On the SAME physical disjoint PDE witnesses, a bound on the excess of
the chosen source ceiling above the intrinsic half-terminal-window envelope
transfers the *conditional* coefficient escape to real window maxima.
The additional ceiling-efficiency hypothesis is explicit, not inferred
from the mere existence of a compact-interval upper bound. -/
theorem h3Path_noL2Trace_widthCap_efficientCeiling_forces_windowSourcePeaks244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v m : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ m k ∧ m k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((m k : ℝ) + 1) ((m k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ η B D E : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        (∀ᶠ k : ℕ in atTop,
          |C (v k)| ≤
            h3PathActualProjectedSourceWindowEnvelope244 hH3
              (τ (v k)) ((τ (v k) + T) / 2) + E) →
        Tendsto (fun k : ℕ =>
          h3PathActualProjectedSourceWindowEnvelope244 hH3
            (τ (v k)) ((τ (v k) + T) / 2)) atTop atTop ∧
        (∀ M : ℝ, ∀ᶠ k : ℕ in atTop,
          ∃ t : ℝ, t ∈ Set.Icc (τ (v k)) ((τ (v k) + T) / 2) ∧
            M ≤ ‖h3PathActualProjectedMomentumSource244 hH3 t‖)) := by
  obtain ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime,
      hSeparate, hSummable, hSelected, hSquare⟩ :=
    h3Path_noL2Trace_finiteDissipation_widthCap_sourceSquareEscape244
      hH3 hClass hMass hNoTrace hDInt
  let b : ℕ → ℝ := fun k => (τ (v k) + T) / 2
  let envelope : ℕ → ℝ := fun k =>
    h3PathActualProjectedSourceWindowEnvelope244 hH3 (τ (v k)) (b k)
  have ha (k : ℕ) : 0 < τ (v k) :=
    lt_trans hClass.terminal_start.1 (hTime (v k)).1
  have hab (k : ℕ) : τ (v k) < b k := by
    dsimp only [b]
    have ht := (hTime (v k)).2
    linarith only [ht]
  have hb (k : ℕ) : b k < T := by
    dsimp only [b]
    have ht := (hTime (v k)).2
    linarith only [ht]
  refine ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime,
    hSeparate, hSummable, hSelected, ?_⟩
  intro η B D E hη hB hD hRegime hEff
  have hCoeffSquare : Tendsto (fun k : ℕ => C (v k) ^ 2)
      atTop atTop := hSquare η B D hη hB hD hRegime
  have hEff' : ∀ᶠ k : ℕ in atTop,
      |C (v k)| ≤ envelope k + E := by
    simpa only [envelope, b] using hEff
  have hEnvelope : Tendsto envelope atTop atTop :=
    h3Path_efficientSourceCeiling_forces_actualNormEscape244
      (fun k => C (v k)) envelope E hCoeffSquare hEff'
  constructor
  · simpa only [envelope, b] using hEnvelope
  · intro M
    have hPeaks := h3Path_sourceWindowEnvelopeEscape_forces_windowPeaks244
      hH3 (fun k => τ (v k)) b ha hab hb hEnvelope M
    simpa only [b] using hPeaks

end
end PrimeTensor.FirstMonomialTriad
