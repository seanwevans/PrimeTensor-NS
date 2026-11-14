import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierUniformDiffusionCommutator
import Mathlib.Tactic

/-!
# Genuine real continuous-linear sharp highpass and automatic commutator

The actual selected outer Fourier highpass was already an orthogonal
contraction on three-component real physical L², but its real-linear
continuous-linear map structure had not been assembled. We construct that
map from the genuine scalar Plancherel bridge and the sharp Fourier cutoff.

This discharges the structural certificate in the preceding cutoff-uniform
commutator theorem. At each fixed strict interior time, ONE temporal radius
works for every real cutoff, including a moving family of radii.

The fully quadratic signed Leray cost is also inherited without inserting
any independent linearity, cutoff, or source-regularity hypothesis.

This does NOT yield a temporal modulus uniform as the anchor approaches the
terminal time. It does not assert a Navier--Stokes continuation theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Additivity of the REAL physical sharp Fourier lowpass follows from
Plancherel injectivity and complex-linear Fourier cutoff additivity. -/
theorem thirdFullPhysical_scalarSharpLow_add244
    (rho : ℝ) (f g : H3ScalarL2) :
    h3CriticalPhysicalSharpLowCutoffApply rho (f + g) =
      h3CriticalPhysicalSharpLowCutoffApply rho f +
        h3CriticalPhysicalSharpLowCutoffApply rho g := by
  apply h3ScalarFourierL2_injective_zeroWeak
  rw [h3Critical_scalarFourier_physicalSharpLowCutoff_eq,
      h3ScalarFourierL2_add, map_add,
      h3ScalarFourierL2_add,
      h3Critical_scalarFourier_physicalSharpLowCutoff_eq,
      h3Critical_scalarFourier_physicalSharpLowCutoff_eq]

/-- Real homogeneity of the genuine physical sharp Fourier lowpass.
Complex homogeneity of the Fourier multiplier restricts to real scalars. -/
theorem thirdFullPhysical_scalarSharpLow_smul244
    (rho c : ℝ) (f : H3ScalarL2) :
    h3CriticalPhysicalSharpLowCutoffApply rho (c • f) =
      c • h3CriticalPhysicalSharpLowCutoffApply rho f := by
  apply h3ScalarFourierL2_injective_zeroWeak
  rw [h3Critical_scalarFourier_physicalSharpLowCutoff_eq,
      h3ScalarFourierL2_smul_real,
      h3ScalarFourierL2_smul_real,
      h3Critical_scalarFourier_physicalSharpLowCutoff_eq]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c (h3ScalarFourierL2 f),
      RCLike.real_smul_eq_coe_smul (K := ℂ) c
        (h3CriticalFourierSharpLowCutoffCLM rho (h3ScalarFourierL2 f))]
  exact map_smul (h3CriticalFourierSharpLowCutoffCLM rho)
    (c : ℂ) (h3ScalarFourierL2 f)

/-- Additivity of the genuine three-coordinate physical sharp lowpass. -/
theorem thirdFullPhysical_sharpVectorLow_add244
    (rho : ℝ) (V W : H3PhysicalRealFinVectorL2Hilbert) :
    thirdFullPhysicalSharpLowCutoffHilbert244 rho (V + W) =
      thirdFullPhysicalSharpLowCutoffHilbert244 rho V +
        thirdFullPhysicalSharpLowCutoffHilbert244 rho W := by
  apply PiLp.ext
  intro j
  simpa only [thirdFullPhysicalSharpLowCutoffHilbert244,
    PiLp.toLp_apply, PiLp.add_apply] using
    thirdFullPhysical_scalarSharpLow_add244 rho (V.ofLp j) (W.ofLp j)

/-- Real homogeneity of the genuine three-coordinate physical lowpass. -/
theorem thirdFullPhysical_sharpVectorLow_smul244
    (rho c : ℝ) (V : H3PhysicalRealFinVectorL2Hilbert) :
    thirdFullPhysicalSharpLowCutoffHilbert244 rho (c • V) =
      c • thirdFullPhysicalSharpLowCutoffHilbert244 rho V := by
  apply PiLp.ext
  intro j
  simpa only [thirdFullPhysicalSharpLowCutoffHilbert244,
    PiLp.toLp_apply, PiLp.smul_apply] using
    thirdFullPhysical_scalarSharpLow_smul244 rho c (V.ofLp j)

/-- The ACTUAL highpass is real-linear, not merely a norm-contractive
set-theoretic projection. -/
noncomputable def thirdFullPhysical_outerSharpHighpassLinear244
    (rho : ℝ) :
    H3PhysicalRealFinVectorL2Hilbert →ₗ[ℝ]
      H3PhysicalRealFinVectorL2Hilbert where
  toFun := fun V => V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V
  map_add' := by
    intro V W
    change (V + W) - thirdFullPhysicalSharpLowCutoffHilbert244 rho (V + W) =
      (V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V) +
        (W - thirdFullPhysicalSharpLowCutoffHilbert244 rho W)
    rw [thirdFullPhysical_sharpVectorLow_add244]
    abel
  map_smul' := by
    intro c V
    change (c • V) - thirdFullPhysicalSharpLowCutoffHilbert244 rho (c • V) =
      c • (V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V)
    rw [thirdFullPhysical_sharpVectorLow_smul244]
    simp only [smul_sub]

/-- A norm-one real continuous-linear realization of the actual sharp
physical highpass. The old Plancherel Pythagoras proves contractivity. -/
noncomputable def thirdFullPhysical_outerSharpHighpassCLM244
    (rho : ℝ) :
    H3PhysicalRealFinVectorL2Hilbert →L[ℝ]
      H3PhysicalRealFinVectorL2Hilbert :=
  (thirdFullPhysical_outerSharpHighpassLinear244 rho).mkContinuous 1
    (fun V => by
      change ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V‖ ≤
        1 * ‖V‖
      simpa only [one_mul] using
        (thirdFullPhysical_sharpVectorHighpass_norm_le244 rho V))

@[simp]
theorem thirdFullPhysical_outerSharpHighpassCLM_apply244
    (rho : ℝ) (V : H3PhysicalRealFinVectorL2Hilbert) :
    thirdFullPhysical_outerSharpHighpassCLM244 rho V =
      V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V := rfl

/-- The new CLM retains the exact highpass contraction, uniformly in rho. -/
theorem thirdFullPhysical_outerSharpHighpassCLM_norm_le244
    (rho : ℝ) (V : H3PhysicalRealFinVectorL2Hilbert) :
    ‖thirdFullPhysical_outerSharpHighpassCLM244 rho V‖ ≤ ‖V‖ := by
  rw [thirdFullPhysical_outerSharpHighpassCLM_apply244]
  exact thirdFullPhysical_sharpVectorHighpass_norm_le244 rho V

/-- The formerly conditional sharp-cutoff realization certificate is now
proved automatically for EVERY real cutoff. -/
theorem thirdFullPhysical_outerSharpHighpass_linearCertificate244 :
    ∀ rho : ℝ,
      ∃ Q : H3PhysicalRealFinVectorL2Hilbert →L[ℝ]
          H3PhysicalRealFinVectorL2Hilbert,
        (∀ V : H3PhysicalRealFinVectorL2Hilbert,
          Q V = V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V) ∧
        (∀ V : H3PhysicalRealFinVectorL2Hilbert, ‖Q V‖ ≤ ‖V‖) := by
  intro rho
  refine ⟨thirdFullPhysical_outerSharpHighpassCLM244 rho, ?_, ?_⟩
  · intro V
    exact thirdFullPhysical_outerSharpHighpassCLM_apply244 rho V
  · intro V
    exact thirdFullPhysical_outerSharpHighpassCLM_norm_le244 rho V

/-- The actual physical sharp outer Laplacian commutator is small on ONE
interior-time interval simultaneously for ALL frequency cutoffs. No extra
real-linear sharp-cutoff hypothesis remains. -/
theorem thirdFullPhysical_outerDiffusionCommutator_uniformActual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x eta : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T → x ≤ s → s - x < delta →
        ∀ rho : ℝ,
          ‖thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho‖ ≤
            (s - x) * eta := by
  exact thirdFullPhysical_outerDiffusionCommutator_uniformAt244
    hH3 x eta hx heta thirdFullPhysical_outerSharpHighpass_linearCertificate244

/-- The QUADRATIC outer nonlinear Leray payment, now with the unconditional
actual sharp-cutoff temporal modulus. Both positive squared costs survive. -/
theorem thirdFullPhysical_outerFrozenFullQuadratic_uniformActual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x eta : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T → x ≤ s → s - x < delta →
        ∀ rho K epsilon : ℝ, 0 < K →
        epsilon < K *
          (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho) →
        let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
        let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
        let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
        let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
        epsilon - K * (2 * (s - x) * (-inner ℝ H D) +
            2 * ‖H‖ * ((s - x) * eta)) +
          K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
            2 * K * inner ℝ (H + A) B := by
  obtain ⟨delta, hdelta, hNear⟩ :=
    thirdFullPhysical_outerDiffusionCommutator_uniformActual244
      hH3 x eta hx heta
  refine ⟨delta, hdelta, ?_⟩
  intro s hs hxs hsDelta rho K epsilon hK hForced
  let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
  let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
  let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
  let C := thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho
  let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
  have hComm : ‖C‖ ≤ (s - x) * eta := hNear s hs hxs hsDelta rho
  have hGap := thirdFullPhysical_outerFrozenBudget_fullQuadraticLerayGap244
    hH3 x s rho K epsilon hx hs hxs hK hForced
  change epsilon - K * (2 * (s - x) * (-inner ℝ H D) +
    2 * ‖H‖ * ‖C‖) + K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
      2 * K * inner ℝ (H + A) B at hGap
  have hWeighted : K * (2 * ‖H‖ * ‖C‖) ≤
      K * (2 * ‖H‖ * ((s - x) * eta)) := by
    have hNonneg : 0 ≤ 2 * ‖H‖ := by positivity
    have hInner := mul_le_mul_of_nonneg_left hComm hNonneg
    have hLeft := mul_le_mul_of_nonneg_left hInner hK.le
    nlinarith only [hLeft]
  dsimp only
  nlinarith only [hGap, hWeighted]


/-- If Leray transfer pays both quadratic increments, it must align with
THE ORIGINAL highpass velocity, not merely the viscous intermediate state.
The alignment strictly exceeds the entire squared net highpass displacement. -/
theorem thirdFullKinetic_quadraticLeray_initialCarrierAlignment244
    (H A B : H3PhysicalRealFinVectorL2Hilbert)
    (K : ℝ) (hK : 0 < K)
    (hPayment : K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
      2 * K * inner ℝ (H + A) B) :
    ‖A - B‖ ^ 2 < 2 * inner ℝ H B := by
  have hCancel : ‖A‖ ^ 2 + ‖B‖ ^ 2 <
      2 * inner ℝ (H + A) B := by
    have hWeighted : K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
        K * (2 * inner ℝ (H + A) B) := by
      calc
        K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
            2 * K * inner ℝ (H + A) B := hPayment
        _ = K * (2 * inner ℝ (H + A) B) := by ring
    by_contra hNot
    have hReverse : 2 * inner ℝ (H + A) B ≤
        ‖A‖ ^ 2 + ‖B‖ ^ 2 := le_of_not_gt hNot
    have hReverseWeighted := mul_le_mul_of_nonneg_left hReverse hK.le
    exact (not_le_of_gt hWeighted) hReverseWeighted
  have hDifference : ‖A - B‖ ^ 2 =
      ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * inner ℝ A B := by
    calc
      ‖A - B‖ ^ 2 = ‖A + (-B)‖ ^ 2 := by rw [sub_eq_add_neg]
      _ = ‖A‖ ^ 2 + 2 * inner ℝ A (-B) + ‖-B‖ ^ 2 :=
        norm_add_sq_real A (-B)
      _ = ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * inner ℝ A B := by
        simp only [inner_neg_right, norm_neg]
        ring
  rw [inner_add_left] at hCancel
  linarith only [hCancel, hDifference]

/-- Selected physical highpass nonlinear forcing must have a strict signed
alignment with its ORIGINAL velocity whenever the frozen diffusion plus
its cutoff-uniform temporal commutator are inadequate to pay the loss.
This is local in the initial time x, with one delta for ALL real radii. -/
theorem thirdFullPhysical_outerFrozenForcesInitialAlignment_uniformActual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x eta : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T → x ≤ s → s - x < delta →
        ∀ rho K epsilon : ℝ, 0 < K →
        epsilon < K *
          (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho) →
        let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
        let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
        let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
        let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
        K * (2 * (s - x) * (-inner ℝ H D) +
          2 * ‖H‖ * ((s - x) * eta)) ≤ epsilon →
          ‖A - B‖ ^ 2 < 2 * inner ℝ H B := by
  obtain ⟨delta, hdelta, hNear⟩ :=
    thirdFullPhysical_outerFrozenFullQuadratic_uniformActual244
      hH3 x eta hx heta
  refine ⟨delta, hdelta, ?_⟩
  intro s hs hxs hsDelta rho K epsilon hK hForced
  -- Introduce the four let-bound physical states before the hypothesis.
  intro H D A B hInsufficient
  have hGap := hNear s hs hxs hsDelta rho K epsilon hK hForced
  change epsilon - K * (2 * (s - x) * (-inner ℝ H D) +
      2 * ‖H‖ * ((s - x) * eta)) +
      K * (‖A‖ ^ 2 + ‖B‖ ^ 2) < 2 * K * inner ℝ (H + A) B at hGap
  have hBudget : K * (2 * (s - x) * (-inner ℝ H D) +
      2 * ‖H‖ * ((s - x) * eta)) ≤ epsilon := hInsufficient
  have hPayment : K * (‖A‖ ^ 2 + ‖B‖ ^ 2) <
      2 * K * inner ℝ (H + A) B := by
    linarith only [hGap, hBudget]
  exact thirdFullKinetic_quadraticLeray_initialCarrierAlignment244
    H A B K hK hPayment


end
end PrimeTensor.FirstMonomialTriad
