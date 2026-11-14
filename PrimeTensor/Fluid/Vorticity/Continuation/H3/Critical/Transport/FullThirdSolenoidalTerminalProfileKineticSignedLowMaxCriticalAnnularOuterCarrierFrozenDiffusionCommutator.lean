import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierTwoStepLerayTransfer
import Mathlib.Tactic

/-!
# Frozen physical diffusion and temporal Laplacian commutator in the selected outer carrier

The previous two-step identity uses the integral of the actual (time-dependent)
physical Laplacian, and therefore cannot identify that integral with a heat
semigroup applied at the left endpoint. Here the exact algebraic discrepancy
is retained as a temporal commutator:

  A_D(x,s) = (s-x) D(x) + C_D(x,s),
  C_D = P_high int_x^s Delta u(r) dr - (s-x) P_high Delta u(x).

The viscous-only energy loss is exactly

  2(s-x) [-<H(x),D(x)>] - 2<H(x),C_D> - ||A_D||^2.

The last term is NEGATIVE, while the commutator is genuinely signed. Combining
this formula with the actual Leray two-stage physical Bochner FTC yields an
explicit three-channel forced-drain alternative. No time regularity estimate
on the commutator and no dissipativity of the frozen Laplacian are assumed.
Both are deliberately exposed as analytical obligations for the next step.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Actual sharp highpass physical velocity at an arbitrary real time. -/
noncomputable def thirdFullPhysical_outerFrozenHighpassVelocity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x rho : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  let V := h3AuditInitialOldPhysicalHilbertTotal hH3 x
  V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V

/-- Frozen LEFT-endpoint actual physical Laplacian, on the same highpass. -/
noncomputable def thirdFullPhysical_outerFrozenHighpassDiffusion244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x rho : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  let D := h3AuditInitialActualSpectralLaplacianTotal hH3 x
  D - thirdFullPhysicalSharpLowCutoffHilbert244 rho D

/-- The time-integrated ACTUAL Laplacian projected to the highpass. -/
noncomputable def thirdFullPhysical_outerIntegratedHighpassDiffusion244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  let JD : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r
  JD - thirdFullPhysicalSharpLowCutoffHilbert244 rho JD

/-- The time-integrated ACTUAL nonlinear Leray forcing highpass. -/
noncomputable def thirdFullPhysical_outerIntegratedHighpassLeray244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  let JN : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3AuditInitialActualSpectralLerayTotal hH3 r
  JN - thirdFullPhysicalSharpLowCutoffHilbert244 rho JN

/-- Exact defect between integrated diffusion on the actual evolving path
and frozen initial diffusion, both projected on the same physical highpass. -/
noncomputable def thirdFullPhysical_outerDiffusionTemporalCommutator244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho -
    (s - x) • thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho

/-- Frozen diffusion + exact temporal commutator: full equality, not a
postulated smallness estimate. In particular the square of the integrated
Laplacian produces a favorable negative correction in the energy drain. -/
theorem thirdFullKinetic_frozenDiffusionCommutator_energyExact244
    (H A D C : H3PhysicalRealFinVectorL2Hilbert) (tau : ℝ)
    (hC : C = A - tau • D) :
    ‖H‖ ^ 2 - ‖H + A‖ ^ 2 =
      2 * tau * (-inner ℝ H D) -
        2 * inner ℝ H C - ‖A‖ ^ 2 := by
  have hA : A = tau • D + C := by
    rw [hC]
    abel
  have hPair : inner ℝ H A =
      tau * inner ℝ H D + inner ℝ H C := by
    rw [hA, inner_add_right, real_inner_smul_right]
  rw [norm_add_sq_real, hPair]
  ring

/-- Cauchy--Schwarz bounds only the genuine temporal commutator. The
negative quadratic viscous increment is discarded in the favorable direction. -/
theorem thirdFullKinetic_frozenDiffusionCommutator_viscousUpper244
    (H A D C : H3PhysicalRealFinVectorL2Hilbert) (tau : ℝ)
    (hC : C = A - tau • D) :
    ‖H‖ ^ 2 - ‖H + A‖ ^ 2 ≤
      2 * tau * (-inner ℝ H D) + 2 * ‖H‖ * ‖C‖ := by
  have hExact := thirdFullKinetic_frozenDiffusionCommutator_energyExact244
    H A D C tau hC
  have hCauchy : -(inner ℝ H C) ≤ ‖H‖ * ‖C‖ := by
    have h := (abs_le.mp (abs_real_inner_le_norm H C)).1
    linarith only [h]
  have hSquare : 0 ≤ ‖A‖ ^ 2 := sq_nonneg _
  linarith only [hExact, hCauchy, hSquare]

/-- Exact three-channel energy ledger at a Hilbert-space level: frozen
Laplacian work, temporal Laplacian commutator, nonlinear Leray pairing.
The two quadratic corrections have favorable negative signs. -/
theorem thirdFullKinetic_frozenDiffusionLeray_threeChannelExact244
    (H A D C B : H3PhysicalRealFinVectorL2Hilbert) (tau : ℝ)
    (hC : C = A - tau • D) :
    ‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2 =
      2 * tau * (-inner ℝ H D) - 2 * inner ℝ H C - ‖A‖ ^ 2 +
        2 * inner ℝ (H + A) B - ‖B‖ ^ 2 := by
  rw [thirdFullKinetic_twoStepViscousLeray_massLoss244]
  rw [thirdFullKinetic_frozenDiffusionCommutator_energyExact244
    H A D C tau hC]

/-- Quantitative SIGNED Leray payment in excess of frozen diffusion and
commutator upper budget. Keeps the quadratic nonlinear increment. -/
theorem thirdFullKinetic_frozenBudget_quantitativeLerayGap244
    (H A D C B : H3PhysicalRealFinVectorL2Hilbert)
    (tau K epsilon : ℝ) (hC : C = A - tau • D)
    (hK : 0 < K)
    (hForced : epsilon < K *
      (‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2)) :
    epsilon - K *
      (2 * tau * (-inner ℝ H D) + 2 * ‖H‖ * ‖C‖) +
        K * ‖B‖ ^ 2 < 2 * K * inner ℝ (H + A) B := by
  have hUpper := thirdFullKinetic_frozenDiffusionCommutator_viscousUpper244
    H A D C tau hC
  have hKUpper := mul_le_mul_of_nonneg_left hUpper hK.le
  have hIdentity := thirdFullKinetic_twoStepViscousLeray_massLoss244 H A B
  rw [hIdentity] at hForced
  nlinarith only [hForced, hKUpper]

/-- If neither frozen diffusion nor the temporal mismatch pays a forced
physical carrier drain, the actual Leray work is strictly positive. -/
theorem thirdFullKinetic_frozenBudget_forcesPositiveLeray244
    (H A D C B : H3PhysicalRealFinVectorL2Hilbert)
    (tau K epsilon : ℝ) (hC : C = A - tau • D)
    (hK : 0 < K)
    (hForced : epsilon < K *
      (‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2))
    (hFrozenComm : K *
      (2 * tau * (-inner ℝ H D) + 2 * ‖H‖ * ‖C‖) ≤ epsilon) :
    0 < inner ℝ (H + A) B := by
  have hGap := thirdFullKinetic_frozenBudget_quantitativeLerayGap244
    H A D C B tau K epsilon hC hK hForced
  have hB : 0 ≤ K * ‖B‖ ^ 2 :=
    mul_nonneg hK.le (sq_nonneg _)
  have hPositive : 0 < 2 * K * inner ℝ (H + A) B := by
    linarith only [hGap, hFrozenComm, hB]
  by_contra hn
  have hNonpos : inner ℝ (H + A) B ≤ 0 := le_of_not_gt hn
  have hNonposK : 2 * K * inner ℝ (H + A) B ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · positivity
    · exact hNonpos
  linarith only [hNonposK, hPositive]

/-- The precise three-channel FORCED DRAIN trichotomy. In the middle branch
there is a genuinely large temporal commutator; the last branch is a
positively aligned Leray transfer. No signed viscous work is suppressed. -/
theorem thirdFullKinetic_frozenBudget_threeChannelAlternative244
    (H A D C B : H3PhysicalRealFinVectorL2Hilbert)
    (tau K epsilon : ℝ) (hC : C = A - tau • D)
    (hK : 0 < K)
    (hForced : epsilon < K *
      (‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2)) :
    epsilon / 2 < K * (2 * tau * (-inner ℝ H D)) ∨
    epsilon / 2 < K * (2 * ‖H‖ * ‖C‖) ∨
      0 < inner ℝ (H + A) B := by
  by_cases hFrozen : epsilon / 2 < K *
      (2 * tau * (-inner ℝ H D))
  · exact Or.inl hFrozen
  · by_cases hComm : epsilon / 2 < K * (2 * ‖H‖ * ‖C‖)
    · exact Or.inr (Or.inl hComm)
    · have hBudget : K *
          (2 * tau * (-inner ℝ H D) + 2 * ‖H‖ * ‖C‖) ≤ epsilon := by
        have hFrozenLe := le_of_not_gt hFrozen
        have hCommLe := le_of_not_gt hComm
        nlinarith only [hFrozenLe, hCommLe]
      exact Or.inr (Or.inr
        (thirdFullKinetic_frozenBudget_forcesPositiveLeray244
          H A D C B tau K epsilon hC hK hForced hBudget))

/-- The actual physical viscous-only energy identity at arbitrary strict
physical times. No physical heat-flow identification is imposed. -/
theorem thirdFullPhysical_outerFrozenViscousEnergy_exact244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ) :
    let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
    let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
    let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
    let C := thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho
    ‖H‖ ^ 2 - ‖H + A‖ ^ 2 =
      2 * (s - x) * (-inner ℝ H D) -
        2 * inner ℝ H C - ‖A‖ ^ 2 := by
  dsimp only
  exact thirdFullKinetic_frozenDiffusionCommutator_energyExact244
    _ _ _ _ (s - x) rfl

/-- Actual two-step Navier--Stokes energy ledger with explicitly frozen
left-endpoint diffusion and its exact temporal discrepancy. -/
theorem thirdFullPhysical_outerFrozenDiffusionLeray_exact244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s) :
    let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
    let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
    let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
    let C := thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho
    let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
    thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho =
      2 * (s - x) * (-inner ℝ H D) - 2 * inner ℝ H C - ‖A‖ ^ 2 +
        2 * inner ℝ (H + A) B - ‖B‖ ^ 2 := by
  let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
  let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
  let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
  let C := thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho
  let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
  have hExact := thirdFullPhysical_outerTwoStepViscousLeray_energyExact244
    hH3 x s rho hx hs hxs
  change thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho =
        (‖H‖ ^ 2 - ‖H + A‖ ^ 2) +
          2 * inner ℝ (H + A) B - ‖B‖ ^ 2 at hExact
  have hDiff := thirdFullKinetic_frozenDiffusionCommutator_energyExact244
    H A D C (s - x) rfl
  dsimp only
  rw [hExact, hDiff]

/-- The actual frozen diffusion/commutator budget forces a SIGNED nonlinear
Leray pairing, retaining the quantitative positive gap and its quadratic
nonlinear correction. -/
theorem thirdFullPhysical_outerFrozenBudget_quantitativeLerayGap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho K epsilon : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s) (hK : 0 < K)
    (hForced : epsilon < K *
      (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho)) :
    let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
    let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
    let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
    let C := thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho
    let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
    epsilon - K *
      (2 * (s - x) * (-inner ℝ H D) + 2 * ‖H‖ * ‖C‖) +
        K * ‖B‖ ^ 2 < 2 * K * inner ℝ (H + A) B := by
  let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
  let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
  let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
  let C := thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho
  let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
  have hExact := thirdFullPhysical_outerTwoStepViscousLeray_energyExact244
    hH3 x s rho hx hs hxs
  change thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho =
        (‖H‖ ^ 2 - ‖H + A‖ ^ 2) +
          2 * inner ℝ (H + A) B - ‖B‖ ^ 2 at hExact
  have hUpper := thirdFullKinetic_frozenDiffusionCommutator_viscousUpper244
    H A D C (s - x) rfl
  have hKUpper := mul_le_mul_of_nonneg_left hUpper hK.le
  have hForced' := hForced
  rw [hExact] at hForced'
  dsimp only
  nlinarith only [hForced', hKUpper]

/-- The exact physical three-way obstruction: frozen viscous work, temporal
Laplacian mismatch, or a positively aligned nonlinear Leray increment. -/
theorem thirdFullPhysical_outerFrozenBudget_threeChannelAlternative244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho K epsilon : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s) (hK : 0 < K)
    (hForced : epsilon < K *
      (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho)) :
    let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
    let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
    let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
    let C := thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho
    let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
    epsilon / 2 < K * (2 * (s - x) * (-inner ℝ H D)) ∨
      epsilon / 2 < K * (2 * ‖H‖ * ‖C‖) ∨
        0 < inner ℝ (H + A) B := by
  let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
  let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
  let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
  let C := thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho
  let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
  have hExact := thirdFullPhysical_outerTwoStepViscousLeray_energyExact244
    hH3 x s rho hx hs hxs
  have hParent :
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho =
      (‖H‖ ^ 2 - ‖H + A‖ ^ 2) +
        2 * inner ℝ (H + A) B - ‖B‖ ^ 2 := by
    change thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho =
        (‖H‖ ^ 2 - ‖H + A‖ ^ 2) +
          2 * inner ℝ (H + A) B - ‖B‖ ^ 2 at hExact
    exact hExact
  have hMass :
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho =
          ‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2 := by
    calc
      _ = (‖H‖ ^ 2 - ‖H + A‖ ^ 2) +
        2 * inner ℝ (H + A) B - ‖B‖ ^ 2 := hParent
      _ = ‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2 :=
        (thirdFullKinetic_twoStepViscousLeray_massLoss244 H A B).symm
  have hForced' : epsilon < K *
      (‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2) := by
    rw [← hMass]
    exact hForced
  have hAlternative :=
    thirdFullKinetic_frozenBudget_threeChannelAlternative244
      H A D C B (s - x) K epsilon rfl hK hForced'
  change epsilon / 2 < K * (2 * (s - x) * (-inner ℝ H D)) ∨
    epsilon / 2 < K * (2 * ‖H‖ * ‖C‖) ∨
      0 < inner ℝ (H + A) B
  exact hAlternative

/-- Coupled to the already established ACTUAL annular deficit peak and
no-growth alternative: a selected strictly positive highpass drain has to
produce positive frozen viscous work, a nonzero temporal diffusion mismatch,
or positive nonlinear Leray alignment. No new temporal envelope is imposed. -/
theorem thirdFullPhysical_outerNoYoungGrowth_frozenThreeChannel244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x s rho sigma margin epsilon : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < margin) (hEps : 0 < epsilon)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : 2 * epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma)
    (hDrop : epsilon <
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma)
    (hNoGrowth :
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma ≤
        thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma) :
    let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
    let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
    let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
    let C := thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho
    let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
    0 < (s - x) * (-inner ℝ H D) ∨
      0 < ‖H‖ * ‖C‖ ∨
        0 < inner ℝ (H + A) B := by
  let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
  let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
  let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
  let C := thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho
  let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
  have hDrain := thirdFullPhysical_outerNoYoungGrowth_forcesStrictHighpassDrain244
    hH3 b x s rho sigma margin epsilon hRho hAspect
    hMargin hEps hExcess hPeak hDrop hNoGrowth
  have hForced : (0 : ℝ) < 1 *
      (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho) := by
    simp only [one_mul]
    linarith only [hDrain]
  have hAlternative := thirdFullPhysical_outerFrozenBudget_threeChannelAlternative244
    hH3 x s rho 1 0 hx hs hxs (by norm_num) hForced
  change (0 : ℝ) / 2 < 1 * (2 * (s - x) * (-inner ℝ H D)) ∨
    (0 : ℝ) / 2 < 1 * (2 * ‖H‖ * ‖C‖) ∨
      0 < inner ℝ (H + A) B at hAlternative
  change 0 < (s - x) * (-inner ℝ H D) ∨
    0 < ‖H‖ * ‖C‖ ∨
      0 < inner ℝ (H + A) B
  rcases hAlternative with hFrozen | hRest
  · left
    norm_num at hFrozen
    nlinarith only [hFrozen]
  · rcases hRest with hComm | hLeray
    · right
      left
      norm_num at hComm
      nlinarith only [hComm]
    · exact Or.inr (Or.inr hLeray)

end
end PrimeTensor.FirstMonomialTriad
