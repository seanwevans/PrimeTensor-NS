import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalEnergyMildData
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Weak.Norm

/-!
# Strong right H³ trace from weak pairings and norm convergence

The previous initial-value bridge used a physically encoded H³ old solution
satisfying a heat--Leray mild equation. This module gives an independent,
Hilbert-space route for the *actual* physical velocity component: convergence
of its real weak pairings against every weighted Fourier H³ test state,
together with convergence of its H³ norm, yields a strong H³ right trace.

This is the right-endpoint analogue of the repository's already proved
`continuous_of_weakRealPairings_of_norm` for interior time. The proof uses
the exact complex-Hilbert polarization identity and continuity of sqrt.
The initial weak and norm convergence remain hypotheses, not conclusions
of the preterminal PDE path or mere finite initial H³ data.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal InnerProductSpace

noncomputable section

/-- Weak real-pairing and norm convergence at the **initial right endpoint**
forces strong convergence of a weighted Fourier H³ scalar state. This is
one general Hilbert-space implication, not a Navier--Stokes assumption. -/
theorem h3Audit_tendstoRight_of_weakRealPairings_and_norm
    (F : ℝ → H3SpectralScalarState) (G₀ : H3SpectralScalarState)
    (hWeak : ∀ Φ : H3SpectralScalarState,
      Tendsto (fun t : ℝ => (inner ℂ (F t) Φ).re)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℂ G₀ Φ).re))
    (hNorm : Tendsto (fun t : ℝ => ‖F t‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖G₀‖)) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 G₀) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hSqFormula :
      (fun t : ℝ => ‖F t - G₀‖ ^ 2) =
      (fun t : ℝ =>
        ‖F t‖ ^ 2 - 2 * (inner ℂ (F t) G₀).re + ‖G₀‖ ^ 2) := by
    funext t
    exact norm_sub_sq (𝕜 := ℂ) (F t) G₀
  have hLimitZero :
      ‖G₀‖ ^ 2 - 2 * (inner ℂ G₀ G₀).re + ‖G₀‖ ^ 2 = 0 := by
    have h := norm_sub_sq (𝕜 := ℂ) G₀ G₀
    simpa using h.symm
  have hSqAux :
      Tendsto
        (fun t : ℝ =>
          ‖F t‖ ^ 2 - 2 * (inner ℂ (F t) G₀).re + ‖G₀‖ ^ 2)
        (𝓝[>] (0 : ℝ))
        (𝓝 (‖G₀‖ ^ 2 - 2 * (inner ℂ G₀ G₀).re + ‖G₀‖ ^ 2)) := by
    exact ((hNorm.pow 2).sub
      (tendsto_const_nhds.mul (hWeak G₀))).add tendsto_const_nhds
  have hSq :
      Tendsto (fun t : ℝ => ‖F t - G₀‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [hSqFormula]
    simpa only [hLimitZero] using hSqAux
  have hSqrt :
      Tendsto (fun t : ℝ => Real.sqrt (‖F t - G₀‖ ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hSq
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg, norm_nonneg,
    Real.sqrt_zero] using hSqrt

/-- A physical initial trace is obtained by testing the ACTUAL weighted
Fourier component against all H³ states and separately controlling its
H³ norm in the initial right limit. Neither part asks for a selected
Banach-mild solution nor postulates strong convergence itself. -/
def H3AuditInitialRightComplementWeakNormTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) : Prop :=
  ∃ G₀ : H3SpectralScalarState,
    (∀ Φ : H3SpectralScalarState,
      Tendsto
        (fun t : ℝ =>
          (inner ℂ (h3AuditActualComplementSpectralStateTotal hH3 p t) Φ).re)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℂ G₀ Φ).re)) ∧
    Tendsto
      (fun t : ℝ => ‖h3AuditActualComplementSpectralStateTotal hH3 p t‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖G₀‖)

/-- Close the strong *actual physical* one-sided H³ Fourier trace from
its weak-real-pairing and norm limits. -/
theorem h3Audit_initialRightWeakNorm_implies_rightComplementTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (hData : H3AuditInitialRightComplementWeakNormTrace hH3 p) :
    H3AuditInitialRightComplementH3SpectralTrace hH3 p := by
  obtain ⟨G₀, hWeak, hNorm⟩ := hData
  exact ⟨G₀,
    h3Audit_tendstoRight_of_weakRealPairings_and_norm
      (h3AuditActualComplementSpectralStateTotal hH3 p) G₀ hWeak hNorm⟩

/-- A weak-pairing/norm right trace and the previously established late-time
homogeneous square-density integral give the selected physical full-time
intrinsic Ḣ^(3/2) time-L² criterion. -/
theorem h3Audit_intrinsicThreeHalves_fullTime_of_initialRightWeakNorm_and_terminal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (ha : 0 < a) (hac : a < c) (hcT : c < T)
    (hInitial : H3AuditInitialRightComplementWeakNormTrace hH3 p)
    (hTerminal : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo c T)) :
    MemLp (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p)
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_intrinsicThreeHalves_fullTime_of_initialRightTrace_and_terminal
    hH3 p ha hac hcT
    (h3Audit_initialRightWeakNorm_implies_rightComplementTrace hH3 p hInitial)
    hTerminal

/-- The same physical endpoint with weak-real-pairing and norm right limits
for both transverse components supplies their full-time Sobolev criterion.
This remains conditional on that terminal endpoint, not an unconditional
regularity assertion. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialRightWeakNorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hPositive : H3AuditInitialRightComplementWeakNormTrace hH3
      (h3TerminalActualVorticityPositiveComplementPair i))
    (hNegative : H3AuditInitialRightComplementWeakNormTrace hH3
      (h3TerminalActualVorticityNegativeComplementPair i)) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialRightTraces
    hH3 hClass i hPhysical
    (h3Audit_initialRightWeakNorm_implies_rightComplementTrace hH3
      (h3TerminalActualVorticityPositiveComplementPair i) hPositive)
    (h3Audit_initialRightWeakNorm_implies_rightComplementTrace hH3
      (h3TerminalActualVorticityNegativeComplementPair i) hNegative)

end
end Euclidean
end Bridge
end PrimeTensor
