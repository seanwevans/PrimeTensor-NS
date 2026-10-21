import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalViscousCeiling244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Majorant
import Mathlib.Tactic

/-!
# Connect global normalized Fourier variance to the terminal absolute Leray transfer

At strict times, the global zero-cutoff fourth-radial Leray contribution is
exactly the negative of the signed full-space transfer. The terminal radial
compactness program independently proved a finite, cutoff-independent absolute
transfer profile G(t) = 2 sum_j integral q^4 |Re <u_j,F_j(U,U)>|.

This module connects those formerly separate PDE channels:

    -Leray_global(t) <= G(t),
    Leray_normalized(t) <= G(t)/D3(t).

The second inequality uses the true spectral Cauchy bound E2^2 <= E0 D3,
not an assumed forcing estimate. Combining it with the closed kinetic/fifth
viscous ceiling and the 36 h(t) order-two commutator allowance gives

    normalized_signed_excess <= viscous_ceiling + 36 h + G/D3.

A near-Young secant thus forces G/D3 to reach the residual concentration
rate at an interior time. No time-integrability, terminal uniform bound, or
zero-frequency interchange is assumed. The result is a bridge to the earlier
explicit full-space absolute-transfer continuation obstruction, not a proof of
unconditional regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeGlobalAbsoluteLerayBridge244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The already-constructed full-space absolute nonlinear transfer, normalized
by actual top dissipation at a strict physical time. -/
noncomputable def h3PathTopFourierGlobalAbsoluteTransferNormalizedRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) : ℝ :=
  h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
      hH3 hClass ht /
    h3TerminalPhysicalTopDissipation3Path hClass t

/-- The full absolute Leray transfer is nonnegative by construction. -/
theorem h3Path_globalAbsoluteLerayTransfer_nonneg244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    0 ≤ h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
      hH3 hClass ht := by
  unfold h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferCoordinateAt
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg (by norm_num)
  apply integral_nonneg
  intro ξ
  exact abs_nonneg _

/-- Reverse-signed global fourth-radial Leray transfer is bounded by the
same full absolute transfer which already dominates *every* sharp radial tail.
This is the orientation required by normalized Fourier concentration. -/
theorem h3Path_neg_globalLerayRate_le_fullAbsoluteTransfer244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    -h3PathTopFourierGlobalLerayRate244 hH3 t
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ ≤
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
      hH3 hClass ht := by
  let f : Fin 3 → H3FourierPoint3 → ℝ := fun j =>
    h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
      hH3 hClass ht j
  have hEach : ∀ j : Fin 3,
      -((-2 : ℝ) * ∫ ξ : H3FourierPoint3, f j ξ) ≤
        2 * ∫ ξ : H3FourierPoint3, |f j ξ| := by
    intro j
    have hInt : Integrable (f j) (volume : Measure H3FourierPoint3) :=
      integrable_h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt'
        hH3 hClass ht j
    have hAbsInt : Integrable
        (fun ξ : H3FourierPoint3 => |f j ξ|)
        (volume : Measure H3FourierPoint3) := by
      simpa only [Real.norm_eq_abs] using hInt.norm
    have hIntegral :
        (∫ ξ : H3FourierPoint3, f j ξ) ≤
          ∫ ξ : H3FourierPoint3, |f j ξ| := by
      exact integral_mono_ae hInt hAbsInt
        (Filter.Eventually.of_forall (fun ξ => le_abs_self (f j ξ)))
    linarith only [hIntegral]
  unfold h3PathTopFourierGlobalLerayRate244
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferCoordinateAt
  dsimp only
  change
    -(∑ j : Fin 3,
        (-2 : ℝ) * ∫ ξ : H3FourierPoint3, f j ξ) ≤
      ∑ j : Fin 3,
        2 * ∫ ξ : H3FourierPoint3, |f j ξ|
  calc
    -(∑ j : Fin 3,
        (-2 : ℝ) * ∫ ξ : H3FourierPoint3, f j ξ) =
        ∑ j : Fin 3,
          -((-2 : ℝ) * ∫ ξ : H3FourierPoint3, f j ξ) := by
          simp only [Finset.sum_neg_distrib]
    _ ≤ ∑ j : Fin 3,
        2 * ∫ ξ : H3FourierPoint3, |f j ξ| := by
          apply Finset.sum_le_sum
          intro j hj
          exact hEach j

/-- Scalar Cauchy-weighting: the normalized signed Leray contribution is
bounded by the absolute transfer divided by D3, with no kinetic loss. -/
theorem h3_globalLeray_scalar_le_absoluteTransferOverDissipation244
    (E0 E2 D L G : ℝ)
    (hE0 : 0 < E0) (hD : 0 < D)
    (hCauchy : E2 ^ 2 ≤ E0 * D)
    (hTransfer : -L ≤ G) (hG : 0 ≤ G) :
    -(E2 ^ 2 * E0 * L) / (E0 * D) ^ 2 ≤ G / D := by
  have hFirst : E2 ^ 2 * (-L) ≤ E2 ^ 2 * G :=
    mul_le_mul_of_nonneg_left hTransfer (sq_nonneg E2)
  have hSecond : E2 ^ 2 * G ≤ (E0 * D) * G :=
    mul_le_mul_of_nonneg_right hCauchy hG
  have hScaled : E2 ^ 2 * (-L) * E0 ≤ (E0 * D) * G * E0 :=
    mul_le_mul_of_nonneg_right (hFirst.trans hSecond) hE0.le
  have hEq : (G / D) * (E0 * D) ^ 2 = (E0 * D) * G * E0 := by
    field_simp [ne_of_gt hD]
    <;> ring
  have hNumer : -(E2 ^ 2 * E0 * L) ≤ (G / D) * (E0 * D) ^ 2 := by
    calc
      -(E2 ^ 2 * E0 * L) = E2 ^ 2 * (-L) * E0 := by ring
      _ ≤ (E0 * D) * G * E0 := hScaled
      _ = (G / D) * (E0 * D) ^ 2 := hEq.symm
  exact (div_le_iff₀ (pow_pos (mul_pos hE0 hD) 2)).2 hNumer

/-- Actual normalized global Leray source is bounded by the already-closed
full-space absolute nonlinear transfer divided by fourth-radial dissipation. -/
theorem h3Path_globalLerayNormalizedRate_le_fullAbsoluteOverDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t) :
    h3PathTopFourierGlobalLerayNormalizedRate244 hH3 hClass t ht ≤
      h3PathTopFourierGlobalAbsoluteTransferNormalizedRate244 hH3 hClass t ht := by
  have hTop := h3TerminalPhysicalTopDissipation3Path_eq hClass ht
  have hTopPos : 0 < h3TerminalPhysicalTopDissipation3Path hClass t := by
    rw [hTop]
    exact hD
  have hMoment := (h3Path_topFourier_normalizedMoment_strictRange244
    hH3 hClass ht hMass hD).2.2
  have hCauchy : velocityH3Energy2At u t ^ 2 ≤
      velocityH3Energy0At u t *
        h3TerminalPhysicalTopDissipation3Path hClass t := by
    unfold h3PathTopFourierNormalizedMiddleMoment244 at hMoment
    have hBound := le_of_lt hMoment
    have hDenOld : 0 < velocityH3Energy0At u t *
        velocityH3Dissipation3At u t := mul_pos hMass hD
    have hBound' := (div_le_iff₀ hDenOld).mp hBound
    rw [hTop]
    simpa only [one_mul] using hBound'
  have hTransfer := h3Path_neg_globalLerayRate_le_fullAbsoluteTransfer244
    hH3 hClass ht
  have hAbsolute := h3Path_globalAbsoluteLerayTransfer_nonneg244
    hH3 hClass ht
  unfold h3PathTopFourierGlobalLerayNormalizedRate244
    h3PathTopFourierGlobalAbsoluteTransferNormalizedRate244
  exact h3_globalLeray_scalar_le_absoluteTransferOverDissipation244
    (velocityH3Energy0At u t)
    (velocityH3Energy2At u t)
    (h3TerminalPhysicalTopDissipation3Path hClass t)
    (h3PathTopFourierGlobalLerayRate244 hH3 t
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
    (h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
      hH3 hClass ht)
    hMass hTopPos hCauchy hTransfer hAbsolute

/-- A fully explicit instantaneous upper bound for normalized spectral
concentration, using only the already-proved physical viscous ceiling,
commutator envelope, and absolute-transfer Fourier profile. -/
theorem h3Path_normalizedExcessRate_le_viscous_gradient_absoluteTransfer244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t) :
    h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass t ≤
      h3PathTopFourierGlobalViscousCeiling244 hH3 hClass t ht +
      36 * h3PathCanonicalSqrtEnergyGradientEnvelope u t +
      h3PathTopFourierGlobalAbsoluteTransferNormalizedRate244
        hH3 hClass t ht := by
  have hOld := h3Path_normalizedExcessRate_le_viscous_gradient_add_Leray244
    hH3 hClass ht hMass hD
  have hLeray := h3Path_globalLerayNormalizedRate_le_fullAbsoluteOverDissipation244
    hH3 hClass ht hMass hD
  linarith only [hOld, hLeray]

/-- Near sharp Young absorption, the *existing cutoff-uniform absolute transfer
profile* must reach the residual global spectral concentration secant at a
strict interior time. Neither terminal integrability nor a fifth-moment
uniform estimate is assumed. -/
theorem h3Path_nearYoung_forces_fullAbsoluteTransfer_after_viscousGradientBudgets244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    ∃ r : ℝ, ∃ hr : r ∈ Set.Ioo s t,
      (h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t)) /
          (t - s) -
        36 * h3PathCanonicalSqrtEnergyGradientEnvelope u r -
        h3PathTopFourierGlobalViscousCeiling244 hH3 hClass r
          ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩ ≤
      h3PathTopFourierGlobalAbsoluteTransferNormalizedRate244
        hH3 hClass r
          ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩ := by
  obtain ⟨r, hr, hLeray⟩ :=
    h3Path_nearYoung_forces_globalLeray_after_viscousGradientBudgets244
      hH3 hClass hs ht hst hMass hD hK hNear
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hrClosed : r ∈ Set.Icc s t := ⟨hr.1.le, hr.2.le⟩
  have hAbsolute :=
    h3Path_globalLerayNormalizedRate_le_fullAbsoluteOverDissipation244
      hH3 hClass hrClass (hMass r hrClosed) (hD r hrClosed)
  refine ⟨r, hr, ?_⟩
  exact hLeray.trans hAbsolute

end
end PrimeTensor.FirstMonomialTriad
