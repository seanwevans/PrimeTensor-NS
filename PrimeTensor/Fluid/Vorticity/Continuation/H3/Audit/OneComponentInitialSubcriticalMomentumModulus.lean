import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSubcriticalEnergyRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalHilbertGlobalFTC
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Quantitative initial physical L² momentum modulus from subcritical H³ growth

The earlier subcritical-energy result provides an integrable physical projected
Navier--Stokes source and an (unidentified) strong right-zero physical L² limit.
Here the already-proved global Hilbert momentum FTC makes that limit quantitative.

For 0 < s ≤ t < b and E₃(r) ≤ M r^(-α), 0 ≤ α < 1, we prove

  ‖u(t) - u(s)‖₂ ≤ (3 + C_L) M (t^(1-α) - s^(1-α))/(1-α).

Passing s to zero using the *previously proved* strong right limit yields

  ‖u(t) - L‖₂ ≤ (3 + C_L) M t^(1-α)/(1-α).

No equality between L and the stipulated physical zero-time velocity is used.
The old temporal joint-continuity and the subcritical energy bound are still
explicit hypotheses. This is not an unconditional Navier--Stokes assertion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Physical Hilbert momentum admits a quantitative two-time modulus, derived
from the genuine diffusion-minus-Leray source and the scalar H³ energy bound. -/
theorem h3Audit_initialSubcriticalEnergyRate_physicalMomentum_twoTimeModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (b α M : ℝ) (hb : 0 < b) (hbT : b < T)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hRate : ∀ r : ℝ, r ∈ Set.Ioc (0 : ℝ) b →
      velocityH3EnergyAt u r ≤ M * r ^ (-α))
    (s t : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) b)
    (ht : t ∈ Set.Ioo (0 : ℝ) b) (hst : s ≤ t) :
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
      h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ ≤
      ((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
        ((t ^ (-α + 1) - s ^ (-α + 1)) / (-α + 1)) := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert := fun r =>
    h3AuditInitialActualSpectralLaplacianTotal hH3 r -
      h3AuditInitialActualSpectralLerayTotal hH3 r
  let C : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  have hC : 0 ≤ C := by
    dsimp only [C]
    linarith only [h3AuditInitialLerayEnergyCoefficient_nonneg]
  have hExponent : -1 < -α := by linarith only [hα1]
  have hPowerInt : IntervalIntegrable (fun r : ℝ => r ^ (-α))
      volume s t := intervalIntegral.intervalIntegrable_rpow' hExponent
  have hMajorInt : IntervalIntegrable
      (fun r : ℝ => (C * M) * r ^ (-α)) volume s t :=
    hPowerInt.const_mul (C * M)
  have hsT : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hs.1, lt_trans hs.2 hbT⟩
  have htT : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht.1, lt_trans ht.2 hbT⟩
  have hInitialInt : IntervalIntegrable G volume 0 b :=
    (h3Audit_initialSubcriticalEnergyRate_projectedRHS_integrable_and_mass
      hH3 b α M hb hbT hα0 hα1 hM hRate).1
  have hSpan : Set.uIcc s t ⊆ Set.uIcc (0 : ℝ) b := by
    intro r hr
    have hrb := h3Audit_positiveUnorderedInterval_subset_initial
      b s t hs ht hr
    simpa only [Set.uIcc_of_le hb.le] using hrb
  have hGInt : IntervalIntegrable G volume s t :=
    hInitialInt.mono_set hSpan
  have hBound : ∀ r : ℝ, r ∈ Set.Icc s t →
      ‖G r‖ ≤ (C * M) * r ^ (-α) := by
    intro r hr
    have hr0 : r ∈ Set.Icc (0 : ℝ) b :=
      ⟨hs.1.le.trans hr.1, hr.2.trans ht.2.le⟩
    have hrPos : r ∈ Set.Ioc (0 : ℝ) b :=
      ⟨lt_of_lt_of_le hs.1 hr.1, hr0.2⟩
    have hD := h3Audit_initialActualSpectralLaplacian_norm_le_energy
      hH3 b hbT r hr0
    have hN := h3Audit_initialActualSpectralLeray_norm_le_energy
      hH3 b hbT r hr0
    calc
      ‖G r‖ ≤ 3 * velocityH3EnergyAt u r +
          h3AuditInitialLerayEnergyCoefficient * velocityH3EnergyAt u r := by
        dsimp only [G]
        exact (norm_sub_le _ _).trans (add_le_add hD hN)
      _ = C * velocityH3EnergyAt u r := by
        dsimp only [C]
        ring
      _ ≤ C * (M * r ^ (-α)) :=
        mul_le_mul_of_nonneg_left (hRate r hrPos) hC
      _ = (C * M) * r ^ (-α) := by ring
  have hFTC :
      h3AuditInitialOldPhysicalHilbertTotal hH3 t -
        h3AuditInitialOldPhysicalHilbertTotal hH3 s =
          ∫ r in s..t, G r :=
    h3Audit_initialOldJoint_implies_physicalHilbertFTC_between_positiveTimes
      hH3 hOldJoint s t hsT htT
  calc
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
        h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ =
        ‖∫ r in s..t, G r‖ := congrArg norm hFTC
    _ ≤ ∫ r in s..t, ‖G r‖ :=
      intervalIntegral.norm_integral_le_integral_norm hst
    _ ≤ ∫ r in s..t, (C * M) * r ^ (-α) :=
      intervalIntegral.integral_mono_on hst hGInt.norm hMajorInt hBound
    _ = (C * M) * ∫ r in s..t, r ^ (-α) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (C * M) *
        ((t ^ (-α + 1) - s ^ (-α + 1)) / (-α + 1)) := by
      rw [integral_rpow (Or.inl hExponent)]

/-- The right limit from the preceding theorem satisfies a *quantitative*
Hölder-type rate with exponent `1-α`. This makes no identification of the
limit with the separately supplied initial physical velocity jet. -/
theorem h3Audit_initialSubcriticalEnergyRate_physicalMomentum_rightLimitRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (b α M : ℝ) (hb : 0 < b) (hbT : b < T)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hRate : ∀ r : ℝ, r ∈ Set.Ioc (0 : ℝ) b →
      velocityH3EnergyAt u r ≤ M * r ^ (-α)) :
    ∃ L : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t - L‖ ≤
          ((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
            (t ^ (-α + 1) / (-α + 1)) := by
  obtain ⟨L, hL⟩ :=
    h3Audit_initialSubcriticalEnergyRate_physicalRightLimit
      hH3 hOldJoint b α M hb hbT hα0 hα1 hM hRate
  refine ⟨L, hL, ?_⟩
  intro t ht
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let K : ℝ := (3 + h3AuditInitialLerayEnergyCoefficient) * M
  let β : ℝ := -α + 1
  have hβ : 0 < β := by
    dsimp only [β]
    linarith only [hα1]
  have hLeft : Tendsto (fun s : ℝ => ‖F t - F s‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖F t - L‖) := by
    exact ((tendsto_const_nhds : Tendsto (fun _ : ℝ => F t)
      (𝓝[>] (0 : ℝ)) (𝓝 (F t))).sub hL).norm
  have hPower : Tendsto (fun s : ℝ => s ^ β)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hAmbient : Tendsto (fun s : ℝ => s ^ β)
        (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ β)) :=
      (Real.continuousAt_rpow_const (0 : ℝ) β
        (Or.inr hβ.le)).tendsto
    have hRestricted : Tendsto (fun s : ℝ => s ^ β)
        (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ β)) :=
      hAmbient.mono_left
        (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ))
    simpa only [Real.zero_rpow hβ.ne'] using hRestricted
  have hRight : Tendsto
      (fun s : ℝ => K * ((t ^ β - s ^ β) / β))
      (𝓝[>] (0 : ℝ)) (𝓝 (K * (t ^ β / β))) := by
    have hDiff : Tendsto (fun s : ℝ => t ^ β - s ^ β)
        (𝓝[>] (0 : ℝ)) (𝓝 (t ^ β - 0)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => t ^ β)
        (𝓝[>] (0 : ℝ)) (𝓝 (t ^ β))).sub hPower
    simpa only [sub_zero] using (hDiff.div_const β).const_mul K
  have hEventually : ∀ᶠ s : ℝ in (𝓝[>] (0 : ℝ)),
      ‖F t - F s‖ ≤ K * ((t ^ β - s ^ β) / β) := by
    have hSmall : ∀ᶠ s : ℝ in (𝓝[>] (0 : ℝ)),
        s ∈ Set.Ioo (0 : ℝ) t := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds ht.1)] with s hs0 hst
      exact ⟨hs0, hst⟩
    filter_upwards [hSmall] with s hs
    have hsB : s ∈ Set.Ioo (0 : ℝ) b :=
      ⟨hs.1, lt_trans hs.2 ht.2⟩
    simpa only [F, K, β] using
      h3Audit_initialSubcriticalEnergyRate_physicalMomentum_twoTimeModulus
        hH3 hOldJoint b α M hb hbT hα0 hα1 hM hRate
        s t hsB ht hs.2.le
  exact le_of_tendsto_of_tendsto hLeft hRight hEventually

end
end Euclidean
end Bridge
end PrimeTensor
