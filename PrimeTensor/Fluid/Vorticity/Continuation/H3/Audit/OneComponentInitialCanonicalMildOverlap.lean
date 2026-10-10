import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialRightSpectralTrace
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Restart.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Initial.State

/-!
# A concrete initial heat--Leray mild overlap supplies the physical H³ right trace

The previous audit proved that a selected actual physical velocity component's
one-sided weighted Fourier H³ trace at zero implies the complete time-L²
homogeneous H^(3/2) condition.  This file derives that right trace from an
explicit local initial-value mild-overlap interface.

The restart construction already supplies a continuous real-time Banach-selected
spectral H³ path and proves that its value at time zero is exactly the supplied
initial spectral state `U₀`.  The only remaining initial-value identification
is that, on one nonempty early physical interval, the canonical Fourier
encoding of the OLD Navier--Stokes velocity equals that selected mild path.
That equality is an explicit hypothesis, NOT silently deduced from pointwise
classical regularity or one finite H³ snapshot.

The resulting one-sided trace is specifically `U₀` in the selected velocity
coordinate, not an arbitrary abstract H³ limit.  The Banach ball also gives
an explicit early norm bound `2*A` independently of the trace argument.
The one-sided trace and the preceding endpoint criteria then give full-time
L² of the intrinsic physical H^(3/2) seminorm.

This is conditional local-strong-solution compatibility, not a proof of the
initial overlap, the external Liu--Zhang continuation theorem, or global
Navier--Stokes regularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-- The actual old physical velocity equals the canonical Banach-selected
unit-viscosity Fourier H³ mild solution on an initial positive-time overlap.

All mild-solution parameters are concrete: `U₀` is the actual proposed
spectral initial datum, `A` bounds it, and `b` is inside the canonical
Picard radius.  Establishing this old/selected equality from initial data
and PDE uniqueness remains a separate mathematical task. -/
def H3AuditInitialCanonicalMildOverlapAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ) : Prop :=
  0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    ∀ (p : H3TerminalCurlGradientPair)
      (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      t < b →
        h3TerminalComplementSpectralStateAt hH3 p t ht =
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ t)
          (h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair p))

/-- The concrete initial mild-overlap interface, with its spectral datum,
ceiling, and overlap width existentially packaged. -/
def H3AuditInitialCanonicalMildOverlap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (U₀ : H3SpectralVelocityState) (A : ℝ),
    ∃ (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ),
      H3AuditInitialCanonicalMildOverlapAt hH3 U₀ hA hU₀ b

/-- The overlap supplies a genuinely quantitative, common early H³ spectral
bound: every selected physical component is bounded by the Picard ball `2*A`.
The new interval may be shortened to precede any specified `a > 0`. -/
theorem h3Audit_initialCanonicalMildOverlapAt_earlySpectralBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A b a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A)
    (hOverlap : H3AuditInitialCanonicalMildOverlapAt hH3 U₀ hA hU₀ b)
    (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ c < a ∧
      ∀ p : H3TerminalCurlGradientPair,
        H3AuditInitialComplementSpectralBound hH3 p c (2 * A) := by
  rcases hOverlap with ⟨hb, hbT, _hbR, hMatches⟩
  let c : ℝ := min (b / 2) (a / 2)
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (by linarith) (by linarith)
  have hca : c < a := by
    dsimp [c]
    have h := min_le_right (b / 2) (a / 2)
    linarith
  refine ⟨c, hc, hca, ?_⟩
  intro p t ht htc
  have htb : t < b := by
    have h := min_le_left (b / 2) (a / 2)
    dsimp only [c] at htc
    linarith
  let W : ℝ → H3SpectralVelocityState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
  have hEq :
      h3TerminalComplementSpectralStateAt hH3 p t ht =
        (W t) (h3ClassicalizationFinOfAxis
          (h3TerminalComplementComponentAxisForPair p)) :=
    hMatches p t ht htb
  calc
    ‖h3TerminalComplementSpectralStateAt hH3 p t ht‖ =
        ‖(W t) (h3ClassicalizationFinOfAxis
          (h3TerminalComplementComponentAxisForPair p))‖ := by rw [hEq]
    _ ≤ ‖W t‖ := h3SpectralFinVector_coordinate_norm_le (W t) _
    _ ≤ 2 * A :=
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ t

/-- Strong continuity of the *constructed* mild solution at zero, its exact
initial-value identity, and actual/selected overlap give the actual
physical component the precise initial Fourier trace `U₀ j`. -/
theorem h3Audit_initialCanonicalMildOverlapAt_rightTrace_to_initialDatum
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A)
    (hOverlap : H3AuditInitialCanonicalMildOverlapAt hH3 U₀ hA hU₀ b)
    (p : H3TerminalCurlGradientPair) :
    Tendsto (h3AuditActualComplementSpectralStateTotal hH3 p)
      (𝓝[>] (0 : ℝ))
      (𝓝 (U₀ (h3ClassicalizationFinOfAxis
        (h3TerminalComplementComponentAxisForPair p)))) := by
  rcases hOverlap with ⟨hb, hbT, _hbR, hMatches⟩
  let W : ℝ → H3SpectralVelocityState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
  let j : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementComponentAxisForPair p)
  have hWContinuous : Continuous W :=
    continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
  have hCoordinateContinuous : ContinuousAt (fun s : ℝ => (W s) j) 0 :=
    ((continuous_apply j).comp hWContinuous).continuousAt
  have hZero : (W 0) j = U₀ j := by
    have h :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_zero
        (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
    exact congrArg (fun V : H3SpectralVelocityState => V j) h
  change Tendsto (h3AuditActualComplementSpectralStateTotal hH3 p)
    (𝓝[>] (0 : ℝ)) (𝓝 (U₀ j))
  rw [← hZero]
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hNear⟩ :=
    (Metric.continuousAt_iff.mp hCoordinateContinuous) ε hε
  refine ⟨min δ b, lt_min hδ hb, ?_⟩
  intro t htPos hDist
  have htSmall : t < min δ b := by
    have htPositive : 0 < t := htPos
    simpa only [Real.dist_eq, sub_zero, abs_of_pos htPositive] using hDist
  have htb : t < b := lt_of_lt_of_le htSmall (min_le_right δ b)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨htPos, lt_trans htb hbT⟩
  have hEq : h3AuditActualComplementSpectralStateTotal hH3 p t = (W t) j := by
    simp only [h3AuditActualComplementSpectralStateTotal, dif_pos ht]
    exact hMatches p t ht htb
  rw [hEq]
  exact hNear (lt_of_lt_of_le hDist (min_le_left δ b))

/-- An initial canonical Picard overlap establishes the previous physical
right-trace predicate for any selected complementary component. -/
theorem h3Audit_initialCanonicalMildOverlap_rightComplementTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOverlap : H3AuditInitialCanonicalMildOverlap hH3)
    (p : H3TerminalCurlGradientPair) :
    H3AuditInitialRightComplementH3SpectralTrace hH3 p := by
  obtain ⟨U₀, A, hA, hU₀, b, hAt⟩ := hOverlap
  let j : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementComponentAxisForPair p)
  exact ⟨U₀ j,
    h3Audit_initialCanonicalMildOverlapAt_rightTrace_to_initialDatum
      hH3 U₀ hA hU₀ hAt p⟩

/-- The explicit initial-data canonical mild-overlap contract and one physical
vorticity strong endpoint supply a full-time intrinsic physical one-component
homogeneous H^(3/2) criterion. This does not assert PDE continuation. -/
theorem h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialCanonicalMildOverlap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hOverlap : H3AuditInitialCanonicalMildOverlap hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact
    h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialRightTrace
      hH3 hClass i hPhysical
      (h3Audit_initialCanonicalMildOverlap_rightComplementTrace
        hH3 hOverlap (h3TerminalActualVorticityPositiveComplementPair i))

/-- The *same* initial canonical mild overlap supplies both transverse
physical velocity components with full-time intrinsic H^(3/2) time L². -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCanonicalMildOverlap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hOverlap : H3AuditInitialCanonicalMildOverlap hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact
    h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialRightTraces
      hH3 hClass i hPhysical
      (h3Audit_initialCanonicalMildOverlap_rightComplementTrace
        hH3 hOverlap (h3TerminalActualVorticityPositiveComplementPair i))
      (h3Audit_initialCanonicalMildOverlap_rightComplementTrace
        hH3 hOverlap (h3TerminalActualVorticityNegativeComplementPair i))

end
end Euclidean
end Bridge
end PrimeTensor
