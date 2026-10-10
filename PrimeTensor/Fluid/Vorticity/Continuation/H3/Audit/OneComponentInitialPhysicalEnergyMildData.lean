import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalMildNormalization
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Vorticity.Energy.Envelope

/-!
# Construct the initial physical Picard-ball bound from the old H³ energy

The preceding physical-time audit postulated all three of an old solution's
spectral representative, its mild equation, and the bound `‖P q‖ ≤ 2*A`.
Here the last assumption is replaced by the **actual old velocity's** H³
energy ceiling on a short initial interval, using the already proved exact
weighted Fourier encoder and `norm_velocityH3SpectralStateAt_le_sqrt_energy`.

The old spectral path is identified with the actual Fourier encoding at each
strict physical time, not with the Banach-selected path. The resulting
Picard-ball estimate and old/selected overlap follow by existing uniqueness.

The continuous physical path, its initial-value identity, the Fourier
identification, the physical energy ceiling, and the signed mild equation
remain EXPLICIT hypotheses. None is derived here from mere pointwise
Navier--Stokes admissibility or a single H³ initial snapshot.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-- All three components of the ACTUAL, physically encoded old velocity at
one strict preterminal time. Proof witnesses are obtained from the H³ path. -/
noncomputable def h3AuditActualSpectralVelocityAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    H3SpectralVelocityState := by
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht hInt
  exact velocityH3SpectralStateAt u t hInt hMeas hFourier

/-- The shared three-vector encoder recovers each previously audited
complementary physical velocity component definitionally. -/
theorem h3AuditActualSpectralVelocityAt_complement
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    (h3AuditActualSpectralVelocityAt hH3 t ht)
        (h3ClassicalizationFinOfAxis
          (h3TerminalComplementComponentAxisForPair p)) =
      h3TerminalComplementSpectralStateAt hH3 p t ht := by
  rfl

/-- The actual weighted Fourier state norm has the already established
physical-energy bound; no abstract velocity surrogate is introduced. -/
theorem h3AuditActualSpectralVelocityAt_norm_le_sqrt_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3AuditActualSpectralVelocityAt hH3 t ht‖ ≤
      Real.sqrt (velocityH3EnergyAt u t) := by
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht hInt
  change ‖velocityH3SpectralStateAt u t hInt hMeas hFourier‖ ≤
    Real.sqrt (velocityH3EnergyAt u t)
  exact norm_velocityH3SpectralStateAt_le_sqrt_energy hFourier

/-- A genuine physical-time mild H³ path identified with the actual old
velocity. The Picard `2*A` bound is NOT assumed: instead the physical H³
energy envelope is bounded by `2*A` on the positive restart interval.

The zero-time value is stated separately because the open-time H³ path
contains no velocity Fourier encoding at t=0. This is the explicit initial
spectral datum, not a consequence of the open-time path contract. -/
def H3AuditInitialPhysicalEnergyMildDataAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ) : Prop :=
  let R : ℝ := h3FinHeatLerayRestartRadius 1 A
  ∃ P : H3SpectralPhysicalVelocityPath R,
    0 < b ∧ b < T ∧ b ≤ R ∧ R < T ∧
    H3AuditInitialOldPhysicalMildEquation U₀ hA P ∧
    P (⟨0, le_refl (0 : ℝ), (h3FinHeatLerayRestartRadius_pos 1 hA).le⟩ :
      Set.Icc (0 : ℝ) R) = U₀ ∧
    (∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
      (htR : t ≤ R),
      P (⟨t, ht.1.le, htR⟩ : Set.Icc (0 : ℝ) R) =
        h3AuditActualSpectralVelocityAt hH3 t ht) ∧
    (∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      t ≤ R → Real.sqrt (velocityH3EnergyAt u t) ≤ 2 * A)

/-- The old physical H³ energy ceiling automatically places the old
continuous physical-time mild path inside the canonical `2*A` Picard ball.
Together with physical Fourier identification and the mild equation, this
establishes the previous physical-time mild-data contract. -/
theorem h3Audit_initialPhysicalEnergyMildDataAt_implies_physicalMildDataAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A)
    (hData : H3AuditInitialPhysicalEnergyMildDataAt hH3 U₀ hA hU₀ b) :
    H3AuditInitialOldPhysicalMildDataAt hH3 U₀ hA hU₀ b := by
  obtain ⟨P, hb, hbT, hbR, hRT, hMild, hZero, hPhysical, hEnergy⟩ := hData
  let R : ℝ := h3FinHeatLerayRestartRadius 1 A
  have hR : 0 < R := h3FinHeatLerayRestartRadius_pos 1 hA
  have hBound : ∀ q : Set.Icc (0 : ℝ) R, ‖P q‖ ≤ 2 * A := by
    intro q
    by_cases hq0 : (q : ℝ) = 0
    · have hqEq : q =
          (⟨0, le_refl (0 : ℝ), hR.le⟩ : Set.Icc (0 : ℝ) R) :=
        Subtype.ext hq0
      rw [hqEq, hZero]
      linarith
    · have hqPos : 0 < (q : ℝ) := by
        exact lt_of_le_of_ne q.property.1 (Ne.symm hq0)
      have ht : (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
        ⟨hqPos, lt_of_le_of_lt q.property.2 hRT⟩
      have hEq : P q = h3AuditActualSpectralVelocityAt hH3 (q : ℝ) ht := by
        have h := hPhysical (q : ℝ) ht q.property.2
        exact h
      rw [hEq]
      exact (h3AuditActualSpectralVelocityAt_norm_le_sqrt_energy
        hH3 (q : ℝ) ht).trans (hEnergy (q : ℝ) ht q.property.2)
  refine ⟨P, hb, hbT, hbR, hBound, hMild, ?_⟩
  intro p t ht htb
  have htR : t ≤ R := (le_of_lt htb).trans hbR
  let q : Set.Icc (0 : ℝ) R := ⟨t, ht.1.le, htR⟩
  refine ⟨q, rfl, ?_⟩
  calc
    h3TerminalComplementSpectralStateAt hH3 p t ht =
        (h3AuditActualSpectralVelocityAt hH3 t ht)
          (h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair p)) :=
      (h3AuditActualSpectralVelocityAt_complement hH3 p t ht).symm
    _ = (P q) (h3ClassicalizationFinOfAxis
          (h3TerminalComplementComponentAxisForPair p)) := by
        rw [hPhysical t ht htR]

/-- Existential packaging: one physical energy ceiling replaces the
abstract Banach-ball hypothesis in the old physical mild-data contract. -/
def H3AuditInitialPhysicalEnergyMildData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (U₀ : H3SpectralVelocityState) (A : ℝ),
    ∃ (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ),
      H3AuditInitialPhysicalEnergyMildDataAt hH3 U₀ hA hU₀ b

/-- The normalized Picard representation, actual physical H³ right trace,
and terminal-side analytic Sobolev criterion can all use the same physical
energy ceiling, without a separately supplied Picard-ball estimate. -/
theorem h3Audit_initialPhysicalEnergyMildData_implies_physicalMildData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildData hH3) :
    H3AuditInitialOldPhysicalMildData hH3 := by
  obtain ⟨U₀, A, hA, hU₀, b, hAt⟩ := hData
  exact ⟨U₀, A, hA, hU₀, b,
    h3Audit_initialPhysicalEnergyMildDataAt_implies_physicalMildDataAt
      hH3 U₀ hA hU₀ hAt⟩

/-- Actual initial H³ right Fourier trace follows from the physical energy
ceiling and the genuine initial mild equation by Picard uniqueness. -/
theorem h3Audit_initialPhysicalEnergyMildData_rightComplementTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildData hH3)
    (p : H3TerminalCurlGradientPair) :
    H3AuditInitialRightComplementH3SpectralTrace hH3 p := by
  exact h3Audit_initialOldPhysicalMildData_rightComplementTrace hH3
    (h3Audit_initialPhysicalEnergyMildData_implies_physicalMildData hH3 hData) p

/-- One transverse actual physical velocity component has full-time
homogeneous 3/2 Sobolev time-L², conditional on the initial physical mild
identity and an actual physical vorticity terminal endpoint. -/
theorem h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialPhysicalEnergyMildData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalEnergyMildData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialOldPhysicalMildData
    hH3 hClass i hPhysical
    (h3Audit_initialPhysicalEnergyMildData_implies_physicalMildData hH3 hData)

/-- Both transverse actual physical velocity components have full-time
homogeneous 3/2 Sobolev time-L² under the same single physical initial data
contract and the selected physical vorticity strong terminal endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalEnergyMildData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalEnergyMildData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialOldPhysicalMildData
    hH3 hClass i hPhysical
    (h3Audit_initialPhysicalEnergyMildData_implies_physicalMildData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
