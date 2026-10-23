import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopSignedMomentumCorridor244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSolenoidalWeakFTCStrongDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.H3.Path.Admissible
import Mathlib.Tactic

/-!
# Uniform projected momentum source on strict H3 windows

The actual projected source is the Hilbert-space vector

  R(t) = Laplacian(u(t)) - LerayNonlinearity(u(t)).

The physical H3 path already makes this exact projected source continuous in
physical L2 on every closed interval strictly inside (0,T). Consequently its
norm is bounded there, and it is Bochner interval-integrable without any
spacetime joint-continuity hypothesis for the pointwise temporal derivative.

These statements do NOT identify the physical velocity increment with the
source integral. That missing weak-FTC identity is exposed explicitly as a
physical Hilbert evolution defect at the end of this module. In particular,
finite source bounds are not misused as pointwise temporal domination or as
an automatic proof of differentiation under the spatial integral.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Actual source in the physical three-component L2 Hilbert space, not a
pointwise representative of the old pressure gradient. -/
noncomputable def h3PathActualProjectedMomentumSource244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    ℝ → H3PhysicalRealFinVectorL2Hilbert :=
  fun s =>
    h3AuditInitialActualSpectralLaplacianTotal hH3 s -
      h3AuditInitialActualSpectralLerayTotal hH3 s

/-- Physical L2 source continuity on every compact positive-time window,
without a scalar weak-FTC or old temporal-derivative hypothesis. -/
theorem h3Path_actualProjectedMomentumSource_continuousOnStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    ContinuousOn (h3PathActualProjectedMomentumSource244 hH3)
      (Set.Icc a b) := by
  change ContinuousOn
    (fun s : ℝ =>
      h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s)
    (Set.Icc a b)
  exact h3Audit_initialActualProjectedRHS_continuousOn_strictInterval
    hH3 a b ha hab hb

/-- A genuine, unconditional uniform spatial L2 bound on the projected
momentum source over any closed strict-time interval. -/
theorem h3Path_actualProjectedMomentumSource_uniformL2OnStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ, s ∈ Set.Icc a b →
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C := by
  have hCont :=
    h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 ha hab hb
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).exists_bound_of_continuousOn
      hCont
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro s hs
  exact (hC s hs).trans (le_max_left C 0)

/-- Uniform control of every physical Hilbert weak-test source pairing,
including solenoidal Schwartz probes. The estimate is independent of the
probe apart from its L2 norm. -/
theorem h3Path_actualProjectedMomentumSource_uniformWeakPairingOnStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (ψ : H3PhysicalRealFinVectorL2Hilbert) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ, s ∈ Set.Icc a b →
        |((innerSL ℝ) (h3PathActualProjectedMomentumSource244 hH3 s)) ψ|
          ≤ C * ‖ψ‖ := by
  obtain ⟨C, hC0, hBound⟩ :=
    h3Path_actualProjectedMomentumSource_uniformL2OnStrict244
      hH3 ha hab hb
  refine ⟨C, hC0, ?_⟩
  intro s hs
  calc
    |((innerSL ℝ) (h3PathActualProjectedMomentumSource244 hH3 s)) ψ|
        = |inner ℝ (h3PathActualProjectedMomentumSource244 hH3 s) ψ| := rfl
    _ ≤ ‖h3PathActualProjectedMomentumSource244 hH3 s‖ * ‖ψ‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ C * ‖ψ‖ :=
      mul_le_mul_of_nonneg_right (hBound s hs) (norm_nonneg ψ)

/-- Unconditional Bochner integrability of the actual projected source over
strict physical intervals. This does not assert that the old velocity is its
primitive. -/
theorem h3Path_actualProjectedMomentumSource_intervalIntegrableStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    IntervalIntegrable (h3PathActualProjectedMomentumSource244 hH3)
      volume a b := by
  exact
    (h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 ha hab hb).intervalIntegrable_of_Icc hab.le

/-- On an arbitrary positive short window, the actual source has a single
L2 ceiling controlling every elapsed observation point. -/
theorem h3Path_actualProjectedMomentumSource_uniformL2OnElapsed244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ tau : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht₀ : 0 < t₀) (htau : 0 < tau) (hEnd : t₀ + tau < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) tau →
        ‖h3PathActualProjectedMomentumSource244 hH3 (t₀ + s)‖ ≤ C := by
  have hUpper : t₀ < t₀ + tau := by linarith
  obtain ⟨C, hC0, hC⟩ :=
    h3Path_actualProjectedMomentumSource_uniformL2OnStrict244
      hH3 ht₀ hUpper hEnd
  refine ⟨C, hC0, ?_⟩
  intro s hs
  apply hC (t₀ + s)
  constructor <;> linarith [hs.1, hs.2]

/-- The positive local canonical restart geometry from H3-path admissibility
always carries a time-uniform physical L2 projected momentum source. This is
an unconditional replacement for *source* boundedness, not for the stronger
pointwise-in-space temporal domination hypothesis. -/
theorem h3Path_exists_shortRestart_with_uniformProjectedL2Source244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∃ (t₀ S E C : ℝ),
      t₀ ∈ Set.Ioo (0 : ℝ) S ∧ S < T ∧ 1 ≤ E ∧
      CanonicalH3TailDataFrom u t₀ S E ∧
      0 < t - t₀ ∧
      t - t₀ < h3FinHeatLerayRestartRadius (1 : ℝ) E ∧
      t₀ + (t - t₀) = t ∧ t < S ∧ 0 ≤ C ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) (t - t₀) →
        ‖h3PathActualProjectedMomentumSource244 hH3 (t₀ + s)‖ ≤ C) := by
  obtain ⟨t₀, S, E, ht₀, hST, hE, hTail,
    hq, hqR, hTime, htS⟩ :=
    hH3.exists_localCanonicalRestartWindowAt ht
  have hEnd : t₀ + (t - t₀) < T := by
    rw [hTime]
    exact lt_trans htS hST
  obtain ⟨C, hC0, hBound⟩ :=
    h3Path_actualProjectedMomentumSource_uniformL2OnElapsed244
      hH3 ht₀.1 hq hEnd
  exact ⟨t₀, S, E, C, ht₀, hST, hE, hTail,
    hq, hqR, hTime, htS, hC0, hBound⟩

/-- Physical Hilbert FTC defect: the discrepancy between the actual
velocity increment and the Bochner integral of its continuous projected
source. Its vanishing is precisely the unresolved evolution identification,
not a consequence of source continuity alone. -/
noncomputable def h3PathActualProjectedMomentumFTCDefect244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  h3AuditInitialOldPhysicalHilbertTotal hH3 b -
    h3AuditInitialOldPhysicalHilbertTotal hH3 a -
    ∫ s in a..b, h3PathActualProjectedMomentumSource244 hH3 s

/-- Vanishing of the Hilbert evolution defect is exactly the physical FTC
identity. No claim of defect vanishing is made here. -/
theorem h3Path_actualProjectedMomentumFTCDefect_eq_zero_iff244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℝ) :
    h3PathActualProjectedMomentumFTCDefect244 hH3 a b = 0 ↔
      h3AuditInitialOldPhysicalHilbertTotal hH3 b -
        h3AuditInitialOldPhysicalHilbertTotal hH3 a =
        ∫ s in a..b, h3PathActualProjectedMomentumSource244 hH3 s := by
  simp only [h3PathActualProjectedMomentumFTCDefect244, sub_eq_zero]

end
end PrimeTensor.FirstMonomialTriad
