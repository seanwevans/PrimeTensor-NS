import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEFourierTransfer244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusQuantitativeModulus244
import Mathlib.Tactic

/-!
# Physical PDE control of finite-band Fourier gradient increments

The previous checkpoint bounds the exact *weighted* spectral square defect
on a fixed radial ball through the actual physical projected source.  Here
we insert the radial gradient multiplier that defines physical H³
low-frequency dissipation.

For any weighted states G,H, the sum of three squared gradient-multiplier
increments is bounded by (ρ+1)² times the weighted radial square defect.
The bound is proved directly from the exact Fourier densities, not by
replacing the localized increment with the full H³ norm difference.
Consequently the actual projected PDE source gives

  Σ_j ‖Mρ(G_j(s)-G_j(t))‖²
    ≤ (ρ+1)² · 3 W₃(ρ) · [C(t-s)]².

Both endpoints and both finite annulus radii remain explicit; no assertion
of a global H⁴ time derivative or uniform terminal rate is made.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3FiniteAnnulusPDEGradient244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3FiniteAnnulusPDEGradient244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Pointwise radial gradient energy of a *difference* is bounded by the
fixed cutoff multiplier ceiling times the true local weighted L² square
defect of the two spectral states. -/
theorem h3Path_lowRadialDissipation_of_difference_le_radialSquareDefect244
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (G H : H3SpectralVelocityState) :
    h3PathActualLowRadialDissipation244 ρ (G - H) ≤
      (ρ + 1) ^ 2 *
        h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ G H := by
  let S : Set H3FourierPoint3 := h3TerminalRadialFrequencyBelow ρ
  let f : H3FourierPoint3 → ℝ :=
    h3TerminalSpectralDissipationSingleDensity (G - H)
  let g : H3FourierPoint3 → ℝ :=
    h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity G H
  have h0 := h3Path_lowRadialGradientCoordinate_integrableOn244
    ρ hρ ((G - H) 0)
  have h1 := h3Path_lowRadialGradientCoordinate_integrableOn244
    ρ hρ ((G - H) 1)
  have h2 := h3Path_lowRadialGradientCoordinate_integrableOn244
    ρ hρ ((G - H) 2)
  have hf : Integrable f (volume.restrict S) := by
    have hSum := (h0.add h1).add h2
    change IntegrableOn f S volume
    have hEq : f =
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ * ‖((G - H) 0) ξ‖ ^ 2) +
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ * ‖((G - H) 1) ξ‖ ^ 2) +
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ * ‖((G - H) 2) ξ‖ ^ 2) := by
      funext ξ
      dsimp only [f, Pi.add_apply]
      unfold h3TerminalSpectralDissipationSingleDensity
      ring
    rw [hEq]
    exact hSum
  have hg : Integrable g (volume.restrict S) :=
    (h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity_integrable
      G H).mono_measure Measure.restrict_le_self
  have hmajor : Integrable
      (fun ξ : H3FourierPoint3 => (ρ + 1) ^ 2 * g ξ)
      (volume.restrict S) := hg.const_mul _
  have hPoint : ∀ᵐ ξ ∂(volume.restrict S),
      f ξ ≤ (ρ + 1) ^ 2 * g ξ := by
    rw [ae_restrict_iff' (measurableSet_h3TerminalRadialFrequencyBelow ρ)]
    filter_upwards [
      MeasureTheory.Lp.coeFn_sub (G 0) (H 0),
      MeasureTheory.Lp.coeFn_sub (G 1) (H 1),
      MeasureTheory.Lp.coeFn_sub (G 2) (H 2)
    ] with ξ hEq0 hEq1 hEq2
    intro hξ
    have hFreq : h3FourierGradientMagnitude ξ < ρ := by
      simpa only [S, h3TerminalRadialFrequencyBelow,
        Set.mem_ofPred_eq] using hξ
    have hCutoff : h3FourierGradientSquare ξ ≤ (ρ + 1) ^ 2 := by
      rw [← h3FourierGradientMagnitude_sq]
      exact pow_le_pow_left₀
        (h3FourierGradientMagnitude_nonneg ξ)
        (by linarith only [hFreq]) 2
    have hSumNonneg :
        0 ≤ ‖(G 0) ξ - (H 0) ξ‖ ^ 2 +
          ‖(G 1) ξ - (H 1) ξ‖ ^ 2 +
          ‖(G 2) ξ - (H 2) ξ‖ ^ 2 := by positivity
    dsimp only [f, g]
    unfold h3TerminalSpectralDissipationSingleDensity
      h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity
      h3TerminalSpectralDifferenceAt
    simp only [Pi.sub_apply, hEq0, hEq1, hEq2]
    exact mul_le_mul_of_nonneg_right hCutoff hSumNonneg
  change (∫ ξ : H3FourierPoint3, f ξ ∂(volume.restrict S)) ≤
    (ρ + 1) ^ 2 * ∫ ξ : H3FourierPoint3, g ξ ∂(volume.restrict S)
  calc
    _ ≤ ∫ ξ : H3FourierPoint3,
          (ρ + 1) ^ 2 * g ξ ∂(volume.restrict S) :=
      integral_mono_ae hf hmajor hPoint
    _ = (ρ + 1) ^ 2 *
          ∫ ξ : H3FourierPoint3, g ξ ∂(volume.restrict S) := by
      rw [integral_const_mul]

/-- Exact Hilbert form: the sum of the three *localized gradient multiplier*
increments, not the unrestricted H³ state increments, is controlled by
one bounded-radial spectral square defect. -/
theorem h3Path_lowRadialGradientIncrementSquare_le_radialDefect244
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (G H : H3SpectralVelocityState) :
    (∑ j : Fin 3,
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ
        (G j - H j)‖ ^ 2) ≤
      (ρ + 1) ^ 2 *
        h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ G H := by
  have hBase :=
    h3Path_lowRadialDissipation_of_difference_le_radialSquareDefect244
      ρ hρ G H
  rw [h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244
    ρ hρ (G - H)] at hBase
  simpa only [Pi.sub_apply] using hBase

/-- The genuine projected physical PDE source controls the localized
Fourier gradient increments with an explicit radius-dependent coefficient. -/
theorem h3Path_actualLowRadialGradientIncrementSquare_le_PDECeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (s t C : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc s t →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) :
    (∑ j : Fin 3,
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ
        ((h3AuditActualSpectralVelocityTotal hH3 s) j -
         (h3AuditActualSpectralVelocityTotal hH3 t) j)‖ ^ 2) ≤
      (ρ + 1) ^ 2 *
        ((3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
          (C * (t - s)) ^ 2) := by
  have hRadial :=
    h3Path_actualRadialWeightedSquareDefect_le_projectedPDECeiling244
      hH3 ρ hρ s t C hs ht hst hCeil
  have hGradient :=
    h3Path_lowRadialGradientIncrementSquare_le_radialDefect244
      ρ hρ
      (h3AuditActualSpectralVelocityTotal hH3 s)
      (h3AuditActualSpectralVelocityTotal hH3 t)
  calc
    _ ≤ (ρ + 1) ^ 2 *
      h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
        (h3AuditActualSpectralVelocityTotal hH3 s)
        (h3AuditActualSpectralVelocityTotal hH3 t) := hGradient
    _ ≤ (ρ + 1) ^ 2 *
        ((3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
          (C * (t - s)) ^ 2) :=
      mul_le_mul_of_nonneg_left hRadial (sq_nonneg _)

/-- The true H³ energy ceiling gives the corresponding physical PDE
source ceiling; no time derivative of weighted H³ is assumed. -/
theorem h3Path_actualLowRadialGradientIncrementSquare_le_H3EnergyCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (s t E : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hE : ∀ r : ℝ, r ∈ Set.Icc s t →
      velocityH3EnergyAt u r ≤ E) :
    (∑ j : Fin 3,
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ
        ((h3AuditActualSpectralVelocityTotal hH3 s) j -
         (h3AuditActualSpectralVelocityTotal hH3 t) j)‖ ^ 2) ≤
      (ρ + 1) ^ 2 *
        ((3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
          (((3 + h3AuditInitialLerayEnergyCoefficient) * E) * (t - s)) ^ 2) := by
  apply h3Path_actualLowRadialGradientIncrementSquare_le_PDECeiling244
    hH3 ρ hρ s t
    ((3 + h3AuditInitialLerayEnergyCoefficient) * E)
    hs ht hst
  intro r hr
  have hCoeff : 0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient := by
    have h := h3AuditInitialLerayEnergyCoefficient_nonneg
    linarith only [h]
  have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  exact (h3Path_physicalProjectedSource_norm_le_H3Energy244
    hH3 r hrAbs).trans
      (mul_le_mul_of_nonneg_left (hE r hr) hCoeff)

/-- Both annulus endpoints enjoy the same explicit physical-PDE
square-increment control, at their respective true Fourier cutoff radii. -/
theorem h3Path_actualFiniteAnnulusTwoGradientIncrements_le_PDECeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R Q : ℝ) (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (s t C : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc s t →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) :
    (∑ j : Fin 3,
      ‖h3PathLowRadialGradientMultiplierCLM244 Q hQ
        ((h3AuditActualSpectralVelocityTotal hH3 s) j -
         (h3AuditActualSpectralVelocityTotal hH3 t) j)‖ ^ 2) +
    (∑ j : Fin 3,
      ‖h3PathLowRadialGradientMultiplierCLM244 R hR
        ((h3AuditActualSpectralVelocityTotal hH3 s) j -
         (h3AuditActualSpectralVelocityTotal hH3 t) j)‖ ^ 2) ≤
    (Q + 1) ^ 2 *
      ((3 * h3TerminalRadialSobolevWeightSquareCeiling Q) *
        (C * (t - s)) ^ 2) +
    (R + 1) ^ 2 *
      ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
        (C * (t - s)) ^ 2) := by
  exact add_le_add
    (h3Path_actualLowRadialGradientIncrementSquare_le_PDECeiling244
      hH3 Q hQ s t C hs ht hst hCeil)
    (h3Path_actualLowRadialGradientIncrementSquare_le_PDECeiling244
      hH3 R hR s t C hs ht hst hCeil)

end
end PrimeTensor.FirstMonomialTriad
