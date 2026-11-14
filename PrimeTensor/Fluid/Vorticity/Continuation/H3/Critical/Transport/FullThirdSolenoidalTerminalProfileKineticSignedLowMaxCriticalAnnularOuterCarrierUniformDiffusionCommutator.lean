import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierQuadraticLerayPayment
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialActualPhysicalSourceMeasurability
import Mathlib.Tactic

/-!
# Cutoff-uniform temporal Laplacian commutator and quadratic Leray threshold

For any real-Hilbert contractive continuous-linear projection Q, the
commutator between Q of an integrated source and frozen Q at the initial
snapshot is bounded by the time interval times the source oscillation.
The bound is uniform over ALL contractive Q, including moving radii.

The actual sharp highpass physical cutoff is separately identified in the
physical transport theorem via an explicit continuous-linear realization
certificate. This interface is not an additional PDE regularity assumption:
it records the missing real-linear-operator bridge in the imported Lean API.
We do not claim to have proved that bridge in this module.

Positive-time continuity gives a local little-o modulus. This must not be
confused with a uniform modulus for x approaching the terminal time T.
The quadratic viscous/Leray corrections are retained in full.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Exact Bochner commutator identity for any real continuous linear map.
Neither positivity nor an orthogonal projector structure is needed. -/
theorem thirdFullKinetic_linearSourceCommutator_exact244
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (Q : H →L[ℝ] H) (L : ℝ → H) (x s : ℝ) :
    Q (∫ r in x..s, L r) - (s - x) • Q (L x) =
      Q ((∫ r in x..s, L r) - (s - x) • L x) := by
  rw [map_sub, map_smul]

/-- A cutoff-independent Bochner integral oscillation estimate. It holds
for any Banach-valued interval-integrable physical source. -/
theorem thirdFullKinetic_BochnerFrozenOscillation_bound244
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (L : ℝ → H) (x s eta : ℝ)
    (hxs : x ≤ s) (heta : 0 ≤ eta)
    (hInt : IntervalIntegrable L volume x s)
    (hOsc : ∀ r : ℝ, r ∈ Set.Ioc x s → ‖L r - L x‖ ≤ eta) :
    ‖(∫ r in x..s, L r) - (s - x) • L x‖ ≤
      (s - x) * eta := by
  have hConstant : IntervalIntegrable (fun _ : ℝ => L x) volume x s :=
    intervalIntegrable_const
  have hIntegral :
      (∫ r in x..s, L r) - (s - x) • L x =
        ∫ r in x..s, (L r - L x) := by
    rw [intervalIntegral.integral_sub hInt hConstant]
    simp only [intervalIntegral.integral_const]
  have hEstimate :
      ‖∫ r in x..s, (L r - L x)‖ ≤ eta * |s - x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro r hr
    have hrIoc : r ∈ Set.Ioc x s := by
      simpa only [Set.uIoc_of_le hxs] using hr
    exact hOsc r hrIoc
  rw [hIntegral]
  simpa only [abs_of_nonneg (sub_nonneg.mpr hxs), mul_comm] using hEstimate

/-- No cutoff-frequency factor in the temporal commutator: its norm is
bounded solely by the oscillation of the genuine physical source. -/
theorem thirdFullKinetic_contractiveCutoff_frozenOscillation244
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (Q : H →L[ℝ] H) (hQ : ∀ Z : H, ‖Q Z‖ ≤ ‖Z‖)
    (L : ℝ → H) (x s eta : ℝ)
    (hxs : x ≤ s) (heta : 0 ≤ eta)
    (hInt : IntervalIntegrable L volume x s)
    (hOsc : ∀ r : ℝ, r ∈ Set.Ioc x s → ‖L r - L x‖ ≤ eta) :
    ‖Q (∫ r in x..s, L r) - (s - x) • Q (L x)‖ ≤
      (s - x) * eta := by
  rw [thirdFullKinetic_linearSourceCommutator_exact244]
  exact (hQ _).trans
    (thirdFullKinetic_BochnerFrozenOscillation_bound244
      L x s eta hxs heta hInt hOsc)

/-- A single time radius works SIMULTANEOUSLY for every contractive
continuous-linear cutoff. This is local at an interior positive time; it
is not claimed uniform in the center x as x approaches T. -/
theorem thirdFullKinetic_contractiveCutoff_uniformLocalModulus244
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (L : ℝ → H) (x eta delta : ℝ)
    (heta : 0 ≤ eta) (hdelta : 0 < delta)
    (hLocal : ∀ r : ℝ, dist r x < delta → ‖L r - L x‖ ≤ eta) :
    ∀ s : ℝ, x ≤ s → s - x < delta →
      IntervalIntegrable L volume x s →
      ∀ Q : H →L[ℝ] H, (∀ Z : H, ‖Q Z‖ ≤ ‖Z‖) →
        ‖Q (∫ r in x..s, L r) - (s - x) • Q (L x)‖ ≤
          (s - x) * eta := by
  intro s hxs hs hInt Q hQ
  apply thirdFullKinetic_contractiveCutoff_frozenOscillation244
    Q hQ L x s eta hxs heta hInt
  intro r hr
  have hrAbove : 0 ≤ r - x := sub_nonneg.mpr hr.1.le
  have hrBelow : r - x < delta := lt_of_le_of_lt
    (sub_le_sub_right hr.2 x) hs
  apply hLocal r
  simpa only [Real.dist_eq, abs_of_nonneg hrAbove] using hrBelow

/-- The actual decoded physical Laplacian is norm-continuous at every
strictly positive preterminal time. This follows from the native H³
spectral path continuity and bounded linear spectral Laplacian decode. -/
theorem thirdFullPhysical_actualLaplacian_continuousAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousAt (h3AuditInitialActualSpectralLaplacianTotal hH3) x := by
  have hU := h3Audit_initialActualSpectralVelocity_continuousOn hH3
  have hCompose :=
    continuous_h3AuditSpectralPhysicalLaplacian.comp_continuousOn hU
  have hL : ContinuousOn
      (h3AuditInitialActualSpectralLaplacianTotal hH3)
      (Set.Ioo (0 : ℝ) T) := by
    apply hCompose.congr
    intro r hr
    simp only [h3AuditInitialActualSpectralLaplacianTotal,
      dite_eq_left hr, Function.comp_apply]
  exact hL.continuousAt (isOpen_Ioo.mem_nhds hx)

/-- At each strict physical time the ACTUAL physical Laplacian has an
L² oscillation radius independent of the Fourier cutoff. No H³ ceiling
on a terminal tail is asserted. -/
theorem thirdFullPhysical_actualLaplacian_localOscillation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x eta : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ r : ℝ, dist r x < delta →
        ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r -
          h3AuditInitialActualSpectralLaplacianTotal hH3 x‖ ≤ eta := by
  have hCont := thirdFullPhysical_actualLaplacian_continuousAt244 hH3 x hx
  obtain ⟨delta, hdelta, hNear⟩ :=
    (Metric.continuousAt_iff.mp hCont) eta heta
  refine ⟨delta, hdelta, ?_⟩
  intro r hr
  have hBound := hNear hr
  simpa only [dist_eq_norm] using le_of_lt hBound

/-- The exact physical highpass commutator inherits the uniform radius-free
modulus from a genuine continuous-linear realization of the sharp cutoff.
The realization is an EXPLICIT structural certificate, not an assumed
source-regularity bound. -/
theorem thirdFullPhysical_outerDiffusionCommutator_of_linearSharpCutoff244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho eta : ℝ) (hxs : x ≤ s) (heta : 0 ≤ eta)
    (Q : H3PhysicalRealFinVectorL2Hilbert →L[ℝ]
      H3PhysicalRealFinVectorL2Hilbert)
    (hQ : ∀ Z : H3PhysicalRealFinVectorL2Hilbert,
      Q Z = Z - thirdFullPhysicalSharpLowCutoffHilbert244 rho Z)
    (hContract : ∀ Z : H3PhysicalRealFinVectorL2Hilbert,
      ‖Q Z‖ ≤ ‖Z‖)
    (hInt : IntervalIntegrable
      (h3AuditInitialActualSpectralLaplacianTotal hH3) volume x s)
    (hOsc : ∀ r : ℝ, r ∈ Set.Ioc x s →
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r -
        h3AuditInitialActualSpectralLaplacianTotal hH3 x‖ ≤ eta) :
    ‖thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho‖ ≤
      (s - x) * eta := by
  change ‖((∫ r in x..s,
      h3AuditInitialActualSpectralLaplacianTotal hH3 r) -
      thirdFullPhysicalSharpLowCutoffHilbert244 rho
        (∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r)) -
    (s - x) •
      (h3AuditInitialActualSpectralLaplacianTotal hH3 x -
        thirdFullPhysicalSharpLowCutoffHilbert244 rho
          (h3AuditInitialActualSpectralLaplacianTotal hH3 x))‖ ≤ _
  rw [← hQ (∫ r in x..s,
        h3AuditInitialActualSpectralLaplacianTotal hH3 r),
      ← hQ (h3AuditInitialActualSpectralLaplacianTotal hH3 x)]
  exact thirdFullKinetic_contractiveCutoff_frozenOscillation244 Q hContract
    (h3AuditInitialActualSpectralLaplacianTotal hH3) x s eta hxs heta hInt hOsc

/-- The fully quadratic nonlinear payment uses the smaller frequency-free
commutator budget (s-x)*eta, rather than the earlier coarse two-term
Laplacian action. The viscous and nonlinear squares both survive. -/
theorem thirdFullKinetic_frozenModulus_fullQuadraticLeray244
    (H A D C B : H3PhysicalRealFinVectorL2Hilbert)
    (tau K epsilon eta : ℝ) (hC : C = A - tau • D)
    (hK : 0 < K) (hTau : 0 ≤ tau)
    (hForced : epsilon < K *
      (‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2))
    (hOsc : ‖C‖ ≤ tau * eta) :
    epsilon - K * (2 * tau * (-inner ℝ H D) +
      2 * ‖H‖ * (tau * eta)) +
      K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
        2 * K * inner ℝ (H + A) B := by
  have hGap := thirdFullKinetic_frozenBudget_fullQuadraticLerayGap244
    H A D C B tau K epsilon hC hK hForced
  have hComm : 2 * ‖H‖ * ‖C‖ ≤
      2 * ‖H‖ * (tau * eta) :=
    mul_le_mul_of_nonneg_left hOsc (by positivity)
  have hKComm := mul_le_mul_of_nonneg_left hComm hK.le
  nlinarith only [hGap, hKComm]

/-- If frozen diffusion and a cutoff-independent temporal modulus are
insufficient, the nonlinear Leray payment must dominate BOTH quadratic
costs. -/
theorem thirdFullKinetic_frozenModulus_forcesQuadraticLeray244
    (H A D C B : H3PhysicalRealFinVectorL2Hilbert)
    (tau K epsilon eta : ℝ) (hC : C = A - tau • D)
    (hK : 0 < K) (hTau : 0 ≤ tau)
    (hForced : epsilon < K *
      (‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2))
    (hOsc : ‖C‖ ≤ tau * eta)
    (hInsufficient : K * (2 * tau * (-inner ℝ H D) +
      2 * ‖H‖ * (tau * eta)) ≤ epsilon) :
    K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
      2 * K * inner ℝ (H + A) B := by
  have hGap := thirdFullKinetic_frozenModulus_fullQuadraticLeray244
    H A D C B tau K epsilon eta hC hK hTau hForced hOsc
  linarith only [hGap, hInsufficient]

/-- Fixed-interior-time uniformity of the ACTUAL highpass temporal
Laplacian commutator, provided the real-linear sharp-cutoff CLM realization.
A SINGLE delta works for ALL rho. This theorem DOES NOT provide a delta
uniform as x approaches the terminal time. -/
theorem thirdFullPhysical_outerDiffusionCommutator_uniformAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x eta : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (heta : 0 < eta)
    (hLinearSharp : ∀ rho : ℝ,
      ∃ Q : H3PhysicalRealFinVectorL2Hilbert →L[ℝ]
          H3PhysicalRealFinVectorL2Hilbert,
        (∀ Z : H3PhysicalRealFinVectorL2Hilbert,
          Q Z = Z - thirdFullPhysicalSharpLowCutoffHilbert244 rho Z) ∧
        (∀ Z : H3PhysicalRealFinVectorL2Hilbert, ‖Q Z‖ ≤ ‖Z‖)) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T → x ≤ s → s - x < delta →
        ∀ rho : ℝ,
          ‖thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho‖ ≤
            (s - x) * eta := by
  obtain ⟨delta, hdelta, hNear⟩ :=
    thirdFullPhysical_actualLaplacian_localOscillation244 hH3 x eta hx heta
  refine ⟨delta, hdelta, ?_⟩
  intro s hs hxs hsd rho
  obtain ⟨Q, hQ, hContract⟩ := hLinearSharp rho
  have hU := h3Audit_initialActualSpectralVelocity_continuousOn hH3
  have hCompose :=
    continuous_h3AuditSpectralPhysicalLaplacian.comp_continuousOn hU
  have hL : ContinuousOn
      (h3AuditInitialActualSpectralLaplacianTotal hH3)
      (Set.Ioo (0 : ℝ) T) := by
    apply hCompose.congr
    intro r hr
    simp only [h3AuditInitialActualSpectralLaplacianTotal,
      dite_eq_left hr, Function.comp_apply]
  have hSubset : Set.Icc x s ⊆ Set.Ioo (0 : ℝ) T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hx.1 hr.1, lt_of_le_of_lt hr.2 hs.2⟩
  have hInt : IntervalIntegrable
      (h3AuditInitialActualSpectralLaplacianTotal hH3) volume x s :=
    (hL.mono hSubset).intervalIntegrable_of_Icc hxs
  apply thirdFullPhysical_outerDiffusionCommutator_of_linearSharpCutoff244
    hH3 x s rho eta hxs heta.le Q hQ hContract hInt
  intro r hr
  apply hNear r
  have hPos : 0 ≤ r - x := sub_nonneg.mpr hr.1.le
  have hSmaller : r - x < delta :=
    lt_of_le_of_lt (sub_le_sub_right hr.2 x) hsd
  simpa only [Real.dist_eq, abs_of_nonneg hPos] using hSmaller

/-- The physical Navier--Stokes ledger now has an explicit *time-length*
commutator payment, conditional solely on the linear sharp-cutoff interface
and an actual source oscillation bound. No terminal-uniform eta is assumed. -/
theorem thirdFullPhysical_outerFrozenModulus_fullQuadraticLeray244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho K epsilon eta : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s) (hK : 0 < K) (heta : 0 ≤ eta)
    (Q : H3PhysicalRealFinVectorL2Hilbert →L[ℝ]
      H3PhysicalRealFinVectorL2Hilbert)
    (hQ : ∀ Z : H3PhysicalRealFinVectorL2Hilbert,
      Q Z = Z - thirdFullPhysicalSharpLowCutoffHilbert244 rho Z)
    (hContract : ∀ Z : H3PhysicalRealFinVectorL2Hilbert,
      ‖Q Z‖ ≤ ‖Z‖)
    (hInt : IntervalIntegrable
      (h3AuditInitialActualSpectralLaplacianTotal hH3) volume x s)
    (hOsc : ∀ r : ℝ, r ∈ Set.Ioc x s →
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r -
        h3AuditInitialActualSpectralLaplacianTotal hH3 x‖ ≤ eta)
    (hForced : epsilon < K *
      (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho)) :
    let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
    let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
    let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
    let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
    epsilon - K * (2 * (s - x) * (-inner ℝ H D) +
      2 * ‖H‖ * ((s - x) * eta)) +
      K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
        2 * K * inner ℝ (H + A) B := by
  let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
  let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
  let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
  let C := thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho
  let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
  have hC : C = A - (s - x) • D := rfl
  have hComm := thirdFullPhysical_outerDiffusionCommutator_of_linearSharpCutoff244
    hH3 x s rho eta hxs heta Q hQ hContract hInt hOsc
  have hFrom := thirdFullPhysical_outerTwoStepViscousLeray_energyExact244
    hH3 x s rho hx hs hxs
  change thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
    thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho =
      ‖H‖ ^ 2 - ‖H + A‖ ^ 2 + 2 * inner ℝ (H + A) B - ‖B‖ ^ 2 at hFrom
  have hForced' : epsilon < K *
      (‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2) := by
    rw [hFrom] at hForced
    have hTwo := thirdFullKinetic_twoStepViscousLeray_massLoss244 H A B
    rw [hTwo]
    exact hForced
  dsimp only
  exact thirdFullKinetic_frozenModulus_fullQuadraticLeray244
    H A D C B (s - x) K epsilon eta hC hK (sub_nonneg.mpr hxs)
    hForced' hComm

end
end PrimeTensor.FirstMonomialTriad
