import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierFrozenFourierDiffusionSign
import Mathlib.Tactic

/-!
# Quadratic Leray payment behind selected outer physical highpass drain

The actual frozen diffusion has a proved nonnegative Fourier dissipation sign.
A selected kinetic drain is governed by the exact three-part identity

  M(x)-M(s) = 2*tau*d - 2*<H,C> - ||A||^2
                         + 2*<H+A,B> - ||B||^2,

where A is the integrated highpass physical Laplacian, C its frozen-time
commutator, and B the integrated highpass nonlinear Leray forcing.

Earlier forced-transfer bounds discarded ||A||^2. Here BOTH negative squares
are retained: if frozen diffusion and the commutator cannot pay the selected
drain, the nonlinear Leray pairing must dominate ||A||^2 + ||B||^2.
This forces nontrivial direction and amplitude of the physical Leray action.

We additionally obtain an unconditional cutoff-independent but coarse bound
on the physical Laplacian commutator. It does not supply a terminal-uniform
modulus and is not presented as a continuation result.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The forced highpass mass drain pays BOTH squared source increments.
No quadratic terms are thrown away. -/
theorem thirdFullKinetic_frozenBudget_fullQuadraticLerayGap244
    (H A D C B : H3PhysicalRealFinVectorL2Hilbert)
    (tau K epsilon : ℝ) (hC : C = A - tau • D)
    (hK : 0 < K)
    (hForced : epsilon < K *
      (‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2)) :
    epsilon - K * (2 * tau * (-inner ℝ H D) +
      2 * ‖H‖ * ‖C‖) + K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
      2 * K * inner ℝ (H + A) B := by
  have hExact := thirdFullKinetic_frozenDiffusionLeray_threeChannelExact244
    H A D C B tau hC
  rw [hExact] at hForced
  have hCauchy : -(inner ℝ H C) ≤ ‖H‖ * ‖C‖ := by
    have hLower := (abs_le.mp (abs_real_inner_le_norm H C)).1
    linarith only [hLower]
  have hWeighted := mul_le_mul_of_nonneg_left hCauchy hK.le
  nlinarith only [hForced, hWeighted]

/-- If both viscous channels fail to pay the forced drain, the nonlinear
Leray pairing pays the two quadratic increments together. -/
theorem thirdFullKinetic_frozenBudget_forcesQuadraticLeray244
    (H A D C B : H3PhysicalRealFinVectorL2Hilbert)
    (tau K epsilon : ℝ) (hC : C = A - tau • D)
    (hK : 0 < K)
    (hForced : epsilon < K *
      (‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2))
    (hInsufficient : K *
      (2 * tau * (-inner ℝ H D) + 2 * ‖H‖ * ‖C‖) ≤ epsilon) :
    K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
      2 * K * inner ℝ (H + A) B := by
  have hGap := thirdFullKinetic_frozenBudget_fullQuadraticLerayGap244
    H A D C B tau K epsilon hC hK hForced
  linarith only [hGap, hInsufficient]

/-- A sharper three-channel obstruction: the Leray branch pays the SUM
of both quadratic losses, not merely a positive signed pairing. -/
theorem thirdFullKinetic_frozenBudget_quadraticThreeChannel244
    (H A D C B : H3PhysicalRealFinVectorL2Hilbert)
    (tau K epsilon : ℝ) (hC : C = A - tau • D)
    (hK : 0 < K)
    (hForced : epsilon < K *
      (‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2)) :
    epsilon / 2 < K * (2 * tau * (-inner ℝ H D)) ∨
    epsilon / 2 < K * (2 * ‖H‖ * ‖C‖) ∨
    K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
      2 * K * inner ℝ (H + A) B := by
  by_cases hFrozen : epsilon / 2 < K * (2 * tau * (-inner ℝ H D))
  · exact Or.inl hFrozen
  · by_cases hComm : epsilon / 2 < K * (2 * ‖H‖ * ‖C‖)
    · exact Or.inr (Or.inl hComm)
    · have hBudget : K *
          (2 * tau * (-inner ℝ H D) + 2 * ‖H‖ * ‖C‖) ≤ epsilon := by
        have hFrozenLe := le_of_not_gt hFrozen
        have hCommLe := le_of_not_gt hComm
        nlinarith only [hFrozenLe, hCommLe]
      exact Or.inr (Or.inr
        (thirdFullKinetic_frozenBudget_forcesQuadraticLeray244
          H A D C B tau K epsilon hC hK hForced hBudget))

/-- The two quadratic increments demand a strict amount of Leray action,
measured against the INTERMEDIATE viscous state rather than the old one. -/
theorem thirdFullKinetic_quadraticLeray_forcesAmplitude244
    (H A B : H3PhysicalRealFinVectorL2Hilbert)
    (K : ℝ) (hK : 0 < K)
    (hPayment : K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
      2 * K * inner ℝ (H + A) B) :
    ‖A‖ ^ 2 < 2 * ‖H + A‖ * ‖B‖ := by
  have hCancel : ‖A‖ ^ 2 + ‖B‖ ^ 2 <
      2 * inner ℝ (H + A) B := by
    have hWeighted :
        K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
          K * (2 * inner ℝ (H + A) B) := by
      calc
        K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
            2 * K * inner ℝ (H + A) B := hPayment
        _ = K * (2 * inner ℝ (H + A) B) := by ring
    by_contra hNot
    have hReverse :
        2 * inner ℝ (H + A) B ≤ ‖A‖ ^ 2 + ‖B‖ ^ 2 :=
      le_of_not_gt hNot
    have hReverseWeighted :=
      mul_le_mul_of_nonneg_left hReverse hK.le
    exact (not_le_of_gt hWeighted) hReverseWeighted
  have hCauchy := (abs_le.mp (abs_real_inner_le_norm (H + A) B)).2
  have hBsq : 0 ≤ ‖B‖ ^ 2 := sq_nonneg _
  nlinarith only [hCancel, hCauchy, hBsq]

/-- The intermediate viscous state cannot vanish (or be smaller than the
viscous displacement) if Leray transfer pays both squared increments. -/
theorem thirdFullKinetic_quadraticLeray_forcesViscousGeometry244
    (H A B : H3PhysicalRealFinVectorL2Hilbert)
    (K : ℝ) (hK : 0 < K)
    (hPayment : K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
      2 * K * inner ℝ (H + A) B) :
    ‖A‖ ^ 2 < ‖H + A‖ ^ 2 := by
  have hCancel : ‖A‖ ^ 2 + ‖B‖ ^ 2 <
      2 * inner ℝ (H + A) B := by
    have hWeighted :
        K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
          K * (2 * inner ℝ (H + A) B) := by
      calc
        K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
            2 * K * inner ℝ (H + A) B := hPayment
        _ = K * (2 * inner ℝ (H + A) B) := by ring
    by_contra hNot
    have hReverse :
        2 * inner ℝ (H + A) B ≤ ‖A‖ ^ 2 + ‖B‖ ^ 2 :=
      le_of_not_gt hNot
    have hReverseWeighted :=
      mul_le_mul_of_nonneg_left hReverse hK.le
    exact (not_le_of_gt hWeighted) hReverseWeighted
  have hIdentity : ‖H + A - B‖ ^ 2 =
      ‖H + A‖ ^ 2 - 2 * inner ℝ (H + A) B + ‖B‖ ^ 2 := by
    calc
      ‖H + A - B‖ ^ 2 = ‖(H + A) + (-B)‖ ^ 2 := by
        rw [sub_eq_add_neg]
      _ = ‖H + A‖ ^ 2 +
          2 * inner ℝ (H + A) (-B) + ‖-B‖ ^ 2 :=
        norm_add_sq_real (H + A) (-B)
      _ = ‖H + A‖ ^ 2 -
          2 * inner ℝ (H + A) B + ‖B‖ ^ 2 := by
        simp only [inner_neg_right, norm_neg]
        ring
  have hNonneg : 0 ≤ ‖H + A - B‖ ^ 2 := sq_nonneg _
  linarith only [hCancel, hIdentity, hNonneg]

/-- A complete quantitative threshold: if the two viscous channels are
insufficient, Leray transfer must be large enough to pay the displacement. -/
theorem thirdFullKinetic_frozenBudget_forcesLerayAction244
    (H A D C B : H3PhysicalRealFinVectorL2Hilbert)
    (tau K epsilon : ℝ) (hC : C = A - tau • D)
    (hK : 0 < K)
    (hForced : epsilon < K *
      (‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2))
    (hInsufficient : K *
      (2 * tau * (-inner ℝ H D) + 2 * ‖H‖ * ‖C‖) ≤ epsilon) :
    ‖A‖ ^ 2 < 2 * ‖H + A‖ * ‖B‖ ∧
    ‖A‖ ^ 2 < ‖H + A‖ ^ 2 := by
  have hPayment := thirdFullKinetic_frozenBudget_forcesQuadraticLeray244
    H A D C B tau K epsilon hC hK hForced hInsufficient
  exact ⟨thirdFullKinetic_quadraticLeray_forcesAmplitude244
      H A B K hK hPayment,
    thirdFullKinetic_quadraticLeray_forcesViscousGeometry244
      H A B K hK hPayment⟩

/-- Coarse but unconditional sharp-highpass temporal commutator control.
The constant is independent of the cutoff; this is NOT a little-o time
modulus and must not be used as such on cofinal terminal windows. -/
theorem thirdFullPhysical_outerDiffusionCommutator_coarseBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ) (hxs : x ≤ s) :
    ‖thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho‖ ≤
      ‖∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r‖ +
        (s - x) * ‖h3AuditInitialActualSpectralLaplacianTotal hH3 x‖ := by
  let J : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r
  let L : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialActualSpectralLaplacianTotal hH3 x
  let Q : H3PhysicalRealFinVectorL2Hilbert → H3PhysicalRealFinVectorL2Hilbert :=
    fun Z => Z - thirdFullPhysicalSharpLowCutoffHilbert244 rho Z
  have hJ : ‖Q J‖ ≤ ‖J‖ :=
    thirdFullPhysical_sharpVectorHighpass_norm_le244 rho J
  have hL : ‖Q L‖ ≤ ‖L‖ :=
    thirdFullPhysical_sharpVectorHighpass_norm_le244 rho L
  have hTau : 0 ≤ s - x := sub_nonneg.mpr hxs
  change ‖Q J - (s - x) • Q L‖ ≤ ‖J‖ + (s - x) * ‖L‖
  calc
    ‖Q J - (s - x) • Q L‖ ≤ ‖Q J‖ + ‖(s - x) • Q L‖ :=
      norm_sub_le _ _
    _ = ‖Q J‖ + (s - x) * ‖Q L‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hTau]
    _ ≤ ‖J‖ + (s - x) * ‖L‖ :=
      add_le_add hJ (mul_le_mul_of_nonneg_left hL hTau)

/-- Exact full-quadratic signed nonlinear Leray payment for the ACTUAL
selected physical highpass carrier. Both viscous and nonlinear squared
increments survive the passage from Hilbert algebra to physical PDE data. -/
theorem thirdFullPhysical_outerFrozenBudget_fullQuadraticLerayGap244
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
    epsilon - K * (2 * (s - x) * (-inner ℝ H D) +
      2 * ‖H‖ * ‖C‖) + K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
      2 * K * inner ℝ (H + A) B := by
  let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
  let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
  let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
  let C := thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho
  let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
  have hEnergy := thirdFullPhysical_outerFrozenDiffusionLeray_exact244
    hH3 x s rho hx hs hxs
  change thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho =
      2 * (s - x) * (-inner ℝ H D) - 2 * inner ℝ H C - ‖A‖ ^ 2 +
      2 * inner ℝ (H + A) B - ‖B‖ ^ 2 at hEnergy
  have hForced' := hForced
  rw [hEnergy] at hForced'
  have hCauchy : -(inner ℝ H C) ≤ ‖H‖ * ‖C‖ := by
    have hLower := (abs_le.mp (abs_real_inner_le_norm H C)).1
    linarith only [hLower]
  have hWeighted := mul_le_mul_of_nonneg_left hCauchy hK.le
  dsimp only
  nlinarith only [hForced', hWeighted]

/-- Physical selected outer three-way alternative with the FULL quadratic
viscous/Leray correction, strengthened by genuine Fourier diffusion sign. -/
theorem thirdFullPhysical_outerFrozenQuadraticThreeChannel244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho K epsilon : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s) (hK : 0 < K)
    (hForced : epsilon < K *
      (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho)) :
    0 ≤ -inner ℝ
      (thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho)
      (thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho) ∧
    (epsilon / 2 < K * (2 * (s - x) *
      (-inner ℝ
        (thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho)
        (thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho))) ∨
     epsilon / 2 < K * (2 *
      ‖thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho‖ *
      ‖thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho‖) ∨
     let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
     let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
     let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
     K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
       2 * K * inner ℝ (H + A) B) := by
  constructor
  · exact thirdFullPhysical_outerFrozenDiffusionWork_nonneg244 hH3 x rho hx
  · let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
    let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
    let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
    let C := thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho
    let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
    by_cases hFrozen : epsilon / 2 < K *
        (2 * (s - x) * (-inner ℝ H D))
    · exact Or.inl hFrozen
    · by_cases hComm : epsilon / 2 < K * (2 * ‖H‖ * ‖C‖)
      · exact Or.inr (Or.inl hComm)
      · have hBudget : K * (2 * (s - x) * (-inner ℝ H D) +
            2 * ‖H‖ * ‖C‖) ≤ epsilon := by
          have hFrozenLe := le_of_not_gt hFrozen
          have hCommLe := le_of_not_gt hComm
          nlinarith only [hFrozenLe, hCommLe]
        have hGap := thirdFullPhysical_outerFrozenBudget_fullQuadraticLerayGap244
          hH3 x s rho K epsilon hx hs hxs hK hForced
        change epsilon - K * (2 * (s - x) * (-inner ℝ H D) +
          2 * ‖H‖ * ‖C‖) + K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
            2 * K * inner ℝ (H + A) B at hGap
        apply Or.inr (Or.inr ?_)
        dsimp only
        linarith only [hGap, hBudget]

end
end PrimeTensor.FirstMonomialTriad
