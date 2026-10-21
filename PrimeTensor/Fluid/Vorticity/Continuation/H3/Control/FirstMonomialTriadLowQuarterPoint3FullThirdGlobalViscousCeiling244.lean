import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalLerayTransportBudget244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Dissipation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Sign.Closure
import Mathlib.Tactic

/-!
# Physical viscous ceiling for normalized spectral concentration

The global zero-cutoff theorem decomposes physical normalized radial variance
production into diffusion/moment, order-two transport, and global Leray.
Previously the order-two term was bounded above by 36 h(t).

Here the *actual* diffusion/moment production is bounded above without an
assumed envelope.  The order-two diffusion pairing is nonpositive, the
zeroth-order diffusion and global fifth-moment heat rate are nonpositive,
and physical Fourier Cauchy gives E2² <= E0 D3.  These produce the concrete
viscous ceiling

  B_normalized <= -(L0 D3 + E0 Heat5) / (E0 D3).

Consequently, near-Young concentration requires a genuine fourth-radial
Leray production rate at an interior time after deducting only the *proved*
36 h gradient budget and this explicit viscous ceiling. The fifth-frequency
moment is not controlled uniformly near a hypothetical terminal time.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1200000

/-- Scalar estimate for the signed heat/moment term.  No spurious sign is
assigned to the normalized heat contribution itself. -/
theorem h3_normalizedDiffusion_scalar_le_viscousCeiling244
    (E2 L2 A P : ℝ)
    (hE2 : 0 ≤ E2)
    (hL2 : L2 ≤ 0)
    (hA : 0 < A)
    (hCauchy : E2 ^ 2 ≤ A)
    (hP : P ≤ 0) :
    (2 * E2 * L2 * A - E2 ^ 2 * P) / A ^ 2 ≤ -P / A := by
  have hFirst : 2 * E2 * L2 * A ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num) hE2) hL2
    · exact hA.le
  have hSecond : E2 ^ 2 * (-P) ≤ A * (-P) :=
    mul_le_mul_of_nonneg_right hCauchy (neg_nonneg.mpr hP)
  have hNumer :
      2 * E2 * L2 * A - E2 ^ 2 * P ≤ (-P) * A := by
    nlinarith only [hFirst, hSecond]
  have hCancel : (-P / A) * A ^ 2 = (-P) * A := by
    field_simp [ne_of_gt hA]
  apply (div_le_iff₀ (pow_pos hA 2)).2
  calc
    2 * E2 * L2 * A - E2 ^ 2 * P ≤ (-P) * A := hNumer
    _ = (-P / A) * A ^ 2 := hCancel.symm

/-- The *unconditional* viscous ceiling for normalized diffusion production:
the zeroth-order physical diffusion loss plus fifth-order Fourier heat loss,
scaled by the actual kinetic/top-dissipation product. -/
noncomputable def h3PathTopFourierGlobalViscousCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) : ℝ :=
  (-(velocityH3DiffusionDerivative0At u t *
        h3TerminalPhysicalTopDissipation3Path hClass t +
      velocityH3Energy0At u t *
        h3PathTopFourierGlobalHeatRate244 hH3 t
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)) /
    (velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t)

/-- Physical heat/moment production is at most its explicit kinetic-plus-fifth
viscous ceiling.  All sign and Cauchy hypotheses come from the H³ class. -/
theorem h3Path_globalDiffusionNormalizedRate_le_viscousCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t) :
    h3PathTopFourierGlobalDiffusionNormalizedRate244 hH3 hClass t ht ≤
      h3PathTopFourierGlobalViscousCeiling244 hH3 hClass t ht := by
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hIBP : H3DiffusionIntegrationByPartsAt u t :=
    h3PathEnergyClassProducesDiffusionIntegrationByParts_closed
      u T hH3 a hClass t ht
  have hL0 : velocityH3DiffusionDerivative0At u t ≤ 0 := by
    rw [velocityH3DiffusionDerivative0At_eq_neg_two_mul_dissipation0 hIBP]
    have h := velocityH3Dissipation0At_nonneg u t
    linarith only [h]
  have hL2 : velocityH3DiffusionDerivative2At u t ≤ 0 := by
    rw [velocityH3DiffusionDerivative2At_eq_neg_two_mul_dissipation2 hIBP]
    have h := velocityH3Dissipation2At_nonneg u t
    linarith only [h]
  have hHeat : h3PathTopFourierGlobalHeatRate244 hH3 t htAbs ≤ 0 :=
    h3Path_globalHeatRate_nonpos244 hH3 t htAbs
  have hTop := h3TerminalPhysicalTopDissipation3Path_eq hClass ht
  have hTopPos : 0 < h3TerminalPhysicalTopDissipation3Path hClass t := by
    rw [hTop]
    exact hD
  have hA : 0 < velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t :=
    mul_pos hMass hTopPos
  have hE2 : 0 ≤ velocityH3Energy2At u t :=
    velocityH3Energy2At_nonneg u t
  have hMoment :=
    (h3Path_topFourier_normalizedMoment_strictRange244
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
  have hP : velocityH3DiffusionDerivative0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t +
      velocityH3Energy0At u t *
        h3PathTopFourierGlobalHeatRate244 hH3 t htAbs ≤ 0 :=
    add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg hL0 hTopPos.le)
      (mul_nonpos_of_nonneg_of_nonpos hMass.le hHeat)
  unfold h3PathTopFourierGlobalDiffusionNormalizedRate244
    h3PathTopFourierGlobalDiffusionExcess244
    h3PathTopFourierGlobalViscousCeiling244
  dsimp only
  exact h3_normalizedDiffusion_scalar_le_viscousCeiling244
    (velocityH3Energy2At u t)
    (velocityH3DiffusionDerivative2At u t)
    (velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t)
    (velocityH3DiffusionDerivative0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t +
      velocityH3Energy0At u t *
        h3PathTopFourierGlobalHeatRate244 hH3 t htAbs)
    hE2 hL2 hA hCauchy hP

/-- The global signed rate has an unconditional upper envelope consisting of
an explicitly identified viscous moment budget, canonical gradient cost, and
the remaining *signed* top Leray transfer. -/
theorem h3Path_normalizedExcessRate_le_viscous_gradient_add_Leray244
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
      h3PathTopFourierGlobalLerayNormalizedRate244 hH3 hClass t ht := by
  have hSplit := h3Path_normalizedSignedExcess_eq_globalThreeChannels244
    hH3 hClass ht
  have hHeat := h3Path_globalDiffusionNormalizedRate_le_viscousCeiling244
    hH3 hClass ht hMass hD
  have hTransport := h3Path_globalOrderTwoNormalizedRate_le_gradientBudget244
    hH3 hClass ht hMass hD
  rw [hSplit]
  linarith only [hHeat, hTransport]

/-- Concrete global Leray rate forced by near-Young concentration after both
*proved* budgets.  Unlike the old background-ceiling theorem this requires no
extra assumption on the diffusion/Hilbert background. The fifth moment in the
ceiling can still grow without a terminal-uniform bound. -/
theorem h3Path_nearYoung_forces_globalLeray_after_viscousGradientBudgets244
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
      h3PathTopFourierGlobalLerayNormalizedRate244 hH3 hClass r
        ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩ := by
  obtain ⟨r, hr, hRate⟩ :=
    h3Path_nearYoung_forces_heatPlusLeray_after_orderTwoBudget244
      hH3 hClass hs ht hst hMass hD hK hNear
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hrClosed : r ∈ Set.Icc s t := ⟨hr.1.le, hr.2.le⟩
  have hVisc := h3Path_globalDiffusionNormalizedRate_le_viscousCeiling244
    hH3 hClass hrClass (hMass r hrClosed) (hD r hrClosed)
  refine ⟨r, hr, ?_⟩
  linarith only [hRate, hVisc]

end
end PrimeTensor.FirstMonomialTriad
