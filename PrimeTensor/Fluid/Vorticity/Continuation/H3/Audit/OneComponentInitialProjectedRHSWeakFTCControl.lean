import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSchwartzDualL1KineticControl
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Initial physical kinetic control from a projected momentum RHS

The preceding module requested independent scalar temporal sources for each
Schwartz test and a common `L¹` dual bound. Here both the scalar integrability
and its common bound follow from ONE physical `L²`-valued source `G`, provided
that the ACTUAL old physical velocity satisfies the weak two-time momentum
identity against Schwartz test vectors.

The only new quantitative hypothesis is `∫₀ᵇ ‖G(t)‖ dt ≤ M`. Cauchy--Schwarz
supplies `|⟪G(t), Φ⟫| ≤ ‖G(t)‖ ‖Φ‖` for every test. This is a concrete
PDE-facing bridge, but it does NOT yet prove the weak momentum identity or
initial integrability of the genuine Navier--Stokes projected RHS. A physical
source is existentially supplied here; identifying it with diffusion minus
Leray transport remains a genuine separate PDE task.

The epsilon-vanishing selected/old relative-energy comparison and terminal
actual-vorticity strong-H³ endpoint remain independent conditions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- Pairing an interval-integrable physical Hilbert-valued momentum source
with a fixed physical L² test produces an interval-integrable scalar source.
This uses the bounded real Hilbert functional `innerSL`, not an assumed
separate scalar measurability or scalar integrability premise. -/
theorem h3Audit_initialProjectedRHS_scalarPairing_intervalIntegrable
    (G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 ≤ b)
    (hG : IntervalIntegrable G volume 0 b)
    (ψ : H3PhysicalRealFinVectorL2Hilbert) :
    IntervalIntegrable
      (fun s : ℝ => ((innerSL ℝ) (G s)) ψ)
      volume 0 b := by
  have hGOn : IntegrableOn G (Set.Ioc (0 : ℝ) b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).1 hG
  have hPairOn :
      IntegrableOn
        (fun s : ℝ => ((innerSL ℝ) ψ) (G s))
        (Set.Ioc (0 : ℝ) b) volume :=
    ((innerSL ℝ) ψ).integrable_comp hGOn
  have hEq :
      (fun s : ℝ => ((innerSL ℝ) (G s)) ψ) =
        (fun s : ℝ => ((innerSL ℝ) ψ) (G s)) := by
    funext s
    simp only [innerSL_apply_apply]
    exact (real_inner_comm (G s) ψ).symm
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).2
  rw [hEq]
  exact hPairOn

/-- An L¹ bound for ONE projected Hilbert RHS dominates the total scalar
source mass against every Schwartz vector, with the SAME constant `M`.
The estimate is the physical Hilbert Cauchy--Schwarz inequality integrated
on the initial interval. -/
theorem h3Audit_initialProjectedRHS_scalarMass_le
    (G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b M : ℝ) (hb : 0 ≤ b)
    (hG : IntervalIntegrable G volume 0 b)
    (hMass : (∫ s in (0 : ℝ)..b, ‖G s‖) ≤ M)
    (ψ : H3PhysicalRealFinVectorL2Hilbert) :
    (∫ s in (0 : ℝ)..b, |((innerSL ℝ) (G s)) ψ|) ≤
      M * ‖ψ‖ := by
  have hPair : IntervalIntegrable
      (fun s : ℝ => ((innerSL ℝ) (G s)) ψ) volume 0 b :=
    h3Audit_initialProjectedRHS_scalarPairing_intervalIntegrable
      G b hb hG ψ
  have hPairAbs : IntervalIntegrable
      (fun s : ℝ => |((innerSL ℝ) (G s)) ψ|)
      volume 0 b := by
    simpa only [Real.norm_eq_abs] using hPair.norm
  have hMajor : IntervalIntegrable
      (fun s : ℝ => ‖ψ‖ * ‖G s‖) volume 0 b :=
    hG.norm.const_mul ‖ψ‖
  have hPointwise : ∀ s ∈ Set.Icc (0 : ℝ) b,
      |((innerSL ℝ) (G s)) ψ| ≤ ‖ψ‖ * ‖G s‖ := by
    intro s _
    calc
      |((innerSL ℝ) (G s)) ψ| = |inner ℝ (G s) ψ| := rfl
      _ ≤ ‖G s‖ * ‖ψ‖ := abs_real_inner_le_norm _ _
      _ = ‖ψ‖ * ‖G s‖ := mul_comm _ _
  have hIntegral :
      (∫ s in (0 : ℝ)..b, |((innerSL ℝ) (G s)) ψ|) ≤
        ∫ s in (0 : ℝ)..b, ‖ψ‖ * ‖G s‖ :=
    intervalIntegral.integral_mono_on hb hPairAbs hMajor hPointwise
  calc
    (∫ s in (0 : ℝ)..b, |((innerSL ℝ) (G s)) ψ|) ≤
        ∫ s in (0 : ℝ)..b, ‖ψ‖ * ‖G s‖ := hIntegral
    _ = ‖ψ‖ * (∫ s in (0 : ℝ)..b, ‖G s‖) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ‖ψ‖ * M :=
      mul_le_mul_of_nonneg_left hMass (norm_nonneg ψ)
    _ = M * ‖ψ‖ := mul_comm _ _

/-- Weak projected-RHS momentum evolution against every Schwartz test,
plus one physical L¹ RHS norm budget, discharges the prior uniform dual
Schwartz L¹ contract. No separate family of scalar sources is assumed. -/
theorem h3Audit_initialProjectedRHS_implies_schwartzDualL1
    (F G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b M : ℝ) (hb : 0 < b)
    (hG : IntervalIntegrable G volume 0 b)
    (hMass : (∫ s in (0 : ℝ)..b, ‖G s‖) ≤ M)
    (hWeakFTC : ∀ (Φ : H3PhysicalRealFinVectorSchwartz)
      (s t : ℝ),
        s ∈ Set.Ioo (0 : ℝ) b →
        t ∈ Set.Ioo (0 : ℝ) b →
          ((innerSL ℝ) (F t))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) -
            ((innerSL ℝ) (F s))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) =
            ∫ r in s..t,
              ((innerSL ℝ) (G r))
                (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) :
    H3AuditInitialSchwartzDualL1IncrementOn F b M := by
  intro Φ
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ
  refine ⟨(fun r : ℝ => ((innerSL ℝ) (G r)) ψ), ?_, ?_, ?_⟩
  · exact h3Audit_initialProjectedRHS_scalarPairing_intervalIntegrable
      G b hb.le hG ψ
  · exact h3Audit_initialProjectedRHS_scalarMass_le
      G b M hb.le hG hMass ψ
  · intro s t hs ht
    exact hWeakFTC Φ s t hs ht

/-- Initial-data interface whose temporal source is ONE physical L²
projected-RHS path, not a test-indexed family of scalar sources. The
positive-time weak momentum increment and the initial RHS L¹ norm budget
remain explicit analytic hypotheses. -/
def H3AuditInitialCanonicalProjectedRHSWeakFTCRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b : ℝ),
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    ∃ (G : ℝ → H3PhysicalRealFinVectorL2Hilbert) (M K : ℝ),
      0 ≤ M ∧
      IntervalIntegrable G volume 0 b ∧
      (∫ s in (0 : ℝ)..b, ‖G s‖) ≤ M ∧
      (∀ (Φ : H3PhysicalRealFinVectorSchwartz) (s t : ℝ),
        s ∈ Set.Ioo (0 : ℝ) b →
        t ∈ Set.Ioo (0 : ℝ) b →
          ((innerSL ℝ)
              (h3AuditInitialOldPhysicalHilbertTotal hH3 t))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) -
            ((innerSL ℝ)
              (h3AuditInitialOldPhysicalHilbertTotal hH3 s))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) =
            ∫ r in s..t,
              ((innerSL ℝ) (G r))
                (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
          IntervalIntegrable (fun s => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|))

/-- The single physical projected RHS and weak momentum evolution provide
exactly the independent scalar-source budget consumed by the previous
Schwartz-test initial comparison criterion. -/
theorem h3Audit_initialProjectedRHS_implies_schwartzDualL1Data
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalProjectedRHSWeakFTCRelativeEnergyData hH3) :
    H3AuditInitialCanonicalSchwartzDualL1RelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, G, M, K, hM, hG, hMass, hWeakFTC,
    hEpsilon⟩ := hData
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, M, K, hM,
    h3Audit_initialProjectedRHS_implies_schwartzDualL1
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      G b M hb hG hMass hWeakFTC,
    hEpsilon⟩

/-- Conditional compact weak-test initial uniqueness under a genuine
projected RHS L¹ bound and the still-separate vanishing comparison residual. -/
theorem h3Audit_initialProjectedRHS_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalProjectedRHSWeakFTCRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialSchwartzDualL1_implies_compactWeakComparisonData
    hH3 (h3Audit_initialProjectedRHS_implies_schwartzDualL1Data hH3 hData)

/-- The original physical initial L² and H³ upper trace conclusions follow
from the same conditional initial projected-RHS comparison. -/
theorem h3Audit_initialProjectedRHS_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalProjectedRHSWeakFTCRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialSchwartzDualL1_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialProjectedRHS_implies_schwartzDualL1Data hH3 hData)

/-- The terminal actual-vorticity strong H³ endpoint is still independent
of the initial momentum-source estimates. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialProjectedRHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalProjectedRHSWeakFTCRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialSchwartzDualL1
    hH3 hClass i hPhysical
    (h3Audit_initialProjectedRHS_implies_schwartzDualL1Data hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
