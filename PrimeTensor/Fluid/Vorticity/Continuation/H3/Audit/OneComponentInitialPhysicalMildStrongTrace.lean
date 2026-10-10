import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialContinuityCore
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalEnergyMildData
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Overlap.Path

/-!
# Strong initial H³ trace directly from an actual physical spectral mild path

The continuity-only initial-value criterion from the previous audit requires
that the actual physical zeroth velocity L² jet and the canonical H³ energy be
continuous at the *specified* old velocity value at t=0. An open-time
Navier--Stokes solution does not identify that specified value.

There is another, logically distinct route already present in the repository:
`H3AuditInitialPhysicalEnergyMildDataAt` packages a continuous physical-time
spectral H³ path P on the initial restart interval. It identifies P with the
actual OLD weighted Fourier velocity for strictly positive times and fixes its
value at zero to U₀. This module extracts a **full three-component strong H³
right trace** directly from that identification.

The proof itself uses only continuity and actual/old identification; the
physical heat--Leray mild equation and Picard bound serve as independent ways
to *obtain* such a path. Thus the theorem does not assume the genuine old
value u(0) is equal to the trace datum U₀. Establishing that compatibility
requires a separate initial-value hypothesis, not open-time PDE regularity.

The physical energy right limit is consequently 1 + spectralSquareEnergy U₀.
This does NOT assert that the limit equals velocityH3EnergyAt u 0 unless an
initial-value compatibility condition is added. The terminal endpoint remains
an independent hypothesis in the full-time Sobolev consequences.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval

noncomputable section

/-- Physical-time initial mild data already includes a continuous real-time
spectral extension equal to the old velocity at each small positive time.
Neither an initial L² velocity trace nor initial H³ energy continuity is
needed to extract the resulting strong *spectral* right limit. -/
theorem h3Audit_initialPhysicalEnergyMildDataAt_fullStrongH3Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A)
    (hData : H3AuditInitialPhysicalEnergyMildDataAt hH3 U₀ hA hU₀ b) :
    Tendsto (h3AuditActualSpectralVelocityTotal hH3)
      (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  obtain ⟨P, hb, hbT, hbR, _hRT, _hMild, hZero,
    hPhysical, _hEnergy⟩ := hData
  let R : ℝ := h3FinHeatLerayRestartRadius 1 A
  have hR : 0 < R := h3FinHeatLerayRestartRadius_pos 1 hA
  let W : ℝ → H3SpectralVelocityState :=
    h3PathPhysicalRealExtension R
      (h3SpectralNormalizedPathOfPhysical hR.le P)
  have hWContinuous : Continuous W := by
    dsimp only [W]
    exact continuous_h3PathPhysicalRealExtension R
      (h3SpectralNormalizedPathOfPhysical hR.le P)
  have hWZero : W 0 = U₀ := by
    let q0 : Set.Icc (0 : ℝ) R := ⟨0, le_rfl, hR.le⟩
    have hRecover :=
      h3PathPhysicalRealExtension_normalizedPhysical_apply hR P q0
    have hPZero : P q0 = U₀ := hZero
    exact hRecover.trans hPZero
  have hWTrace : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
    rw [← hWZero]
    exact hWContinuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hPositive : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), 0 < t :=
    self_mem_nhdsWithin
  have hBeforeb : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), t < b :=
    nhdsWithin_le_nhds (Iio_mem_nhds hb)
  have hAgreement :
      W =ᶠ[𝓝[>] (0 : ℝ)]
        h3AuditActualSpectralVelocityTotal hH3 := by
    filter_upwards [hPositive, hBeforeb] with t ht0 htb
    have ht : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨ht0, lt_trans htb hbT⟩
    have htR : t ≤ R :=
      (le_of_lt htb).trans hbR
    let q : Set.Icc (0 : ℝ) R := ⟨t, ht0.le, htR⟩
    have hRecover : W t = P q := by
      exact h3PathPhysicalRealExtension_normalizedPhysical_apply hR P q
    have hOld : P q = h3AuditActualSpectralVelocityAt hH3 t ht :=
      hPhysical t ht htR
    rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t ht]
    exact hRecover.trans hOld
  exact hWTrace.congr' hAgreement

/-- The physical-time initial mild datum produces a genuine strong right H³
trace of the whole old three-component velocity, not only six separate
pair-indexed right component traces. -/
theorem h3Audit_initialPhysicalEnergyMildData_fullStrongH3Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildData hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  obtain ⟨U₀, A, hA, hU₀, b, hAt⟩ := hData
  exact ⟨U₀,
    h3Audit_initialPhysicalEnergyMildDataAt_fullStrongH3Trace
      hH3 U₀ hA hU₀ hAt⟩

/-- The full strong spectral trace fixes the initial right limit of the
ACTUAL positive-time physical H³ energy, independently of its specified
value at time zero. -/
theorem h3Audit_initialPhysicalEnergyMildDataAt_energyRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A)
    (hData : H3AuditInitialPhysicalEnergyMildDataAt hH3 U₀ hA hU₀ b) :
    Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 + h3SpectralVelocitySquareEnergy U₀)) := by
  have hTrace :=
    h3Audit_initialPhysicalEnergyMildDataAt_fullStrongH3Trace
      hH3 U₀ hA hU₀ hData
  have hSpectralEnergy :
      Tendsto
        (fun t : ℝ => h3SpectralVelocitySquareEnergy
          (h3AuditActualSpectralVelocityTotal hH3 t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (h3SpectralVelocitySquareEnergy U₀)) := by
    unfold h3SpectralVelocitySquareEnergy
    apply tendsto_finsetSum
    intro j _
    have hCoordinate :
        Tendsto
          (fun t : ℝ => (h3AuditActualSpectralVelocityTotal hH3 t) j)
          (𝓝[>] (0 : ℝ)) (𝓝 (U₀ j)) :=
      (continuous_apply j).continuousAt.tendsto.comp hTrace
    have hNorm :
        Tendsto
          (fun t : ℝ => ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖)
          (𝓝[>] (0 : ℝ)) (𝓝 ‖U₀ j‖) :=
      continuous_norm.continuousAt.tendsto.comp hCoordinate
    exact hNorm.pow 2
  have hPositive : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), 0 < t :=
    self_mem_nhdsWithin
  have hBeforeT : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), t < T := by
    have hT : 0 < T :=
      (Classical.choose_spec hH3.navier_stokes).positive_terminal
    exact nhdsWithin_le_nhds (Iio_mem_nhds hT)
  have hAgreement :
      (fun t : ℝ => 1 + h3SpectralVelocitySquareEnergy
        (h3AuditActualSpectralVelocityTotal hH3 t))
        =ᶠ[𝓝[>] (0 : ℝ)]
      velocityH3EnergyAt u := by
    filter_upwards [hPositive, hBeforeT] with t h0 hT
    exact h3AuditActualSpectralVelocityTotal_energy_exact
      hH3 t ⟨h0, hT⟩
  exact (hSpectralEnergy.const_add 1).congr' hAgreement

/-- An independently supplied equality of the initial physical energy with
the initial mild spectral energy is sufficient for physical energy right
continuity. This equality is not inferred from open-time NS admissibility. -/
theorem h3Audit_initialPhysicalEnergyMildDataAt_energyRightLimit_of_compatibleZero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A)
    (hData : H3AuditInitialPhysicalEnergyMildDataAt hH3 U₀ hA hU₀ b)
    (hCompatible : velocityH3EnergyAt u 0 =
      1 + h3SpectralVelocitySquareEnergy U₀) :
    Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3EnergyAt u 0)) := by
  rw [hCompatible]
  exact h3Audit_initialPhysicalEnergyMildDataAt_energyRightLimit
    hH3 U₀ hA hU₀ hData

end
end Euclidean
end Bridge
end PrimeTensor
