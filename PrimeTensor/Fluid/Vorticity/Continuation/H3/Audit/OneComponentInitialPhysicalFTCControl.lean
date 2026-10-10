import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalTimeModulus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Initial strong H³ trace from bounded physical temporal source terms

The preceding initial-data result assumed an `O(t)` bound for the actual
physical zero-jet displacement and an `O(t)` upper bound on H³ energy.
This file derives both estimates from genuine initial-time integral
identities: the physical L²-valued velocity FTC and the scalar H³ energy
FTC, with uniform bounds on their respective temporal source terms.

The FTC identities and source bounds are explicit analytic assumptions,
not consequences of an open-time NS path.  In particular, no initial
regularity, projected forcing bound, or temporal integrability is silently
inferred across the excluded t=0 endpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval

noncomputable section

/-- Physical initial-time evolution data for the actual velocity.

`V j s` is the physical L²-valued temporal source for the zeroth velocity
component; `g s` is the scalar H³-energy rate. The exact initial-time
integral equations are kept separate from their uniform bounds, so future
PDE estimates can discharge the two analytic obligations independently. -/
def H3AuditInitialPhysicalZeroJetFTCControlData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (V : Fin 3 → ℝ → H3ScalarL2)
    (g : ℝ → ℝ)
    (Cvelocity Cenergy : ℝ),
    0 ≤ Cvelocity ∧ 0 ≤ Cenergy ∧
    (∀ j : Fin 3, ∀ t : ℝ, ∀ ht : t ∈ Set.Ioo (0 : ℝ) T,
      IntervalIntegrable (V j) volume 0 t ∧
      h3AuditActualPhysicalZeroJetL2Total hH3 j t -
        velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j) =
          ∫ s in (0 : ℝ)..t, V j s ∧
      (∀ᵐ s : ℝ ∂volume,
        s ∈ Set.uIoc (0 : ℝ) t → ‖V j s‖ ≤ Cvelocity)) ∧
    (∀ t : ℝ, ∀ ht : t ∈ Set.Ioo (0 : ℝ) T,
      IntervalIntegrable g volume 0 t ∧
      velocityH3EnergyAt u t - velocityH3EnergyAt u 0 =
        ∫ s in (0 : ℝ)..t, g s ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t, g s ≤ Cenergy))

/-- The physical L² velocity FTC together with an almost-everywhere
uniform rate bound yields the actual initial-time `O(t)` distance estimate. -/
theorem h3Audit_initialPhysicalZeroJet_FTC_displacement_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (V : Fin 3 → ℝ → H3ScalarL2)
    (Cvelocity : ℝ)
    (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hFTC : h3AuditActualPhysicalZeroJetL2Total hH3 j t -
        velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j) =
          ∫ s in (0 : ℝ)..t, V j s)
    (hRate : ∀ᵐ s : ℝ ∂volume,
      s ∈ Set.uIoc (0 : ℝ) t → ‖V j s‖ ≤ Cvelocity) :
    dist (h3AuditActualPhysicalZeroJetL2Total hH3 j t)
      (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) ≤
        Cvelocity * t := by
  have hBound := intervalIntegral.norm_integral_le_of_norm_le_const_ae hRate
  have hBound' :
      ‖∫ s in (0 : ℝ)..t, V j s‖ ≤ Cvelocity * t := by
    simpa only [sub_zero, abs_of_nonneg ht.1.le] using hBound
  rw [dist_eq_norm, hFTC]
  exact hBound'

/-- The scalar H³ energy FTC plus a uniform upper rate bound produces
the one-sided initial `O(t)` energy growth estimate. -/
theorem h3Audit_initialPhysicalH3Energy_FTC_growth_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (g : ℝ → ℝ)
    (Cenergy : ℝ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : IntervalIntegrable g volume 0 t)
    (hFTC : velocityH3EnergyAt u t - velocityH3EnergyAt u 0 =
        ∫ s in (0 : ℝ)..t, g s)
    (hRate : ∀ s ∈ Set.Icc (0 : ℝ) t, g s ≤ Cenergy) :
    velocityH3EnergyAt u t ≤ velocityH3EnergyAt u 0 + Cenergy * t := by
  have hConstInt :
      IntervalIntegrable (fun _s : ℝ => Cenergy) volume 0 t :=
    continuousOn_const.intervalIntegrable_of_Icc ht.1.le
  have hIntegral :
      (∫ s in (0 : ℝ)..t, g s) ≤
        ∫ _s in (0 : ℝ)..t, Cenergy :=
    intervalIntegral.integral_mono_on ht.1.le hInt hConstInt hRate
  have hConst : (∫ _s in (0 : ℝ)..t, Cenergy) = Cenergy * t := by
    simp [mul_comm]
  rw [hConst] at hIntegral
  linarith

/-- Two physical temporal FTC estimates discharge the linear-time
criterion of the preceding module with rate `max Cvelocity Cenergy`. -/
theorem h3Audit_initialPhysicalFTCControl_implies_linearRateData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalZeroJetFTCControlData hH3) :
    H3AuditInitialPhysicalZeroJetLinearRateData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, V, g, Cv, Ce,
    hCv, hCe, hVelocity, hEnergy⟩ := hData
  let C : ℝ := max Cv Ce
  have hC : 0 ≤ C := hCv.trans (le_max_left Cv Ce)
  refine ⟨hInt0, hMeas0, hFourier0, C, hC, ?_, ?_⟩
  · intro t ht
    obtain ⟨hInt, hFTC, hRate⟩ := hEnergy t ht
    have hEnergyBound :=
      h3Audit_initialPhysicalH3Energy_FTC_growth_le
        g Ce t ht hInt hFTC hRate
    have hCeC : Ce * t ≤ C * t :=
      mul_le_mul_of_nonneg_right (le_max_right Cv Ce) ht.1.le
    linarith
  · intro j t ht
    obtain ⟨_hInt, hFTC, hRate⟩ := hVelocity j t ht
    have hVelocityBound :=
      h3Audit_initialPhysicalZeroJet_FTC_displacement_le
        hH3 hInt0 hMeas0 V Cv j t ht hFTC hRate
    exact hVelocityBound.trans
      (mul_le_mul_of_nonneg_right (le_max_left Cv Ce) ht.1.le)

/-- Actual Navier–Stokes strong initial H³ trace under physical initial-time
FTC identities and bounded physical temporal sources, with no separately
postulated velocity `L²` trace or energy modulus. -/
theorem h3Audit_initialPhysicalFTCControl_implies_strongH3Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialPhysicalZeroJetFTCControlData hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  exact h3Audit_initialPhysicalLinearRate_implies_strongH3Trace
    hH3 hT
    (h3Audit_initialPhysicalFTCControl_implies_linearRateData hH3 hData)

/-- Full-time two-component physical `L²_t Ḣ^(3/2)_x` estimate, conditional
on the independent strong terminal vorticity endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalFTC
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalZeroJetFTCControlData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  have hT : 0 < T :=
    lt_trans hClass.terminal_start.1 hClass.terminal_start.2
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalTimeModulus
    hH3 hClass i hPhysical
    (h3Audit_initialPhysicalLinearRate_implies_timeModulusData hH3
      (h3Audit_initialPhysicalFTCControl_implies_linearRateData hH3 hData))

end
end Euclidean
end Bridge
end PrimeTensor
