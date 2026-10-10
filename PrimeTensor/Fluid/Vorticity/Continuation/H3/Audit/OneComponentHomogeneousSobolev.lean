import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentEndpointTimeIntegrability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Raw.Fourier.L2

/-!
# Fourier Ḣ^(3/2) density of the physical velocity component

The Fourier convention is q(ξ) = (2π)^2 |ξ|^2. The squared Ḣ^(3/2)
seminorm has Fourier weight q^(3/2) = sqrt(q^3). An H³ scalar spectral
state G is W3 times the raw Fourier field, with W3² = 1+q+q²+q³.

This module proves the exact frequency-domain domination

  sqrt(q³) |W3⁻¹ G|² ≤ |G|²

and its spatial integral bound. When applied to each selected transverse
component of a strong physical endpoint, this discharges the previously
explicit spectral-domination premise of the terminal integrability lemma.
Temporal measurability of the scalar time density is still a NAMED premise.
No published one-component PDE continuation theorem is used or asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

-- The Fourier carrier is a finite Euclidean coordinate space. The local
-- Fintype instance is required to synthesize its canonical volume measure.
noncomputable local instance axisFintypeH3AuditHomogeneousSobolev
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Genuine square-density for the homogeneous 3/2 derivative in the
project's 2π-normalized Fourier convention. -/
noncomputable def h3AuditHomogeneousThreeHalvesFourierSquareDensity
    (G : H3SpectralScalarState) (ξ : H3FourierPoint3) : ℝ :=
  Real.sqrt (h3FourierGradientSquare ξ ^ 3) *
    ‖h3SpectralScalarRawFourier G ξ‖ ^ 2

/-- Exact H³ weight bounds the homogeneous three-halves square weight.
This is frequency algebra, not a Navier--Stokes regularity claim. -/
theorem h3Audit_sqrt_gradientCube_le_sobolevWeightSquare
    (ξ : H3FourierPoint3) :
    Real.sqrt (h3FourierGradientSquare ξ ^ 3) ≤
      h3SobolevFrequencyWeight ξ ^ 2 := by
  let q : ℝ := h3FourierGradientSquare ξ
  have hq : 0 ≤ q := h3FourierGradientSquare_nonneg ξ
  have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq 3
  have hy : 0 ≤ Real.sqrt (q ^ 3) := Real.sqrt_nonneg _
  have hysq : (Real.sqrt (q ^ 3)) ^ 2 = q ^ 3 :=
    Real.sq_sqrt hq3
  have hSmall : Real.sqrt (q ^ 3) ≤ 1 + q ^ 3 := by
    nlinarith only [hysq, hy, sq_nonneg (Real.sqrt (q ^ 3) - 1)]
  have hLarge : 1 + q ^ 3 ≤ h3SobolevFrequencyWeight ξ ^ 2 := by
    rw [h3SobolevFrequencyWeight_sq]
    change 1 + q ^ 3 ≤ 1 + q + q ^ 2 + q ^ 3
    nlinarith only [hq, sq_nonneg q]
  exact hSmall.trans hLarge

/-- The actual raw-Fourier homogeneous Ḣ^(3/2) density is bounded by
that state's exact H³ weighted-square density. -/
theorem h3Audit_homogeneousThreeHalvesDensity_le_H3Square
    (G : H3SpectralScalarState) (ξ : H3FourierPoint3) :
    0 ≤ h3AuditHomogeneousThreeHalvesFourierSquareDensity G ξ ∧
    h3AuditHomogeneousThreeHalvesFourierSquareDensity G ξ ≤ ‖G ξ‖ ^ 2 := by
  let W : ℝ := h3SobolevFrequencyWeight ξ
  let s : ℝ := Real.sqrt (h3FourierGradientSquare ξ ^ 3)
  have hW : 0 < W := h3SobolevFrequencyWeight_pos ξ
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hBound : s ≤ W ^ 2 :=
    h3Audit_sqrt_gradientCube_le_sobolevWeightSquare ξ
  have hRaw : ‖h3SpectralScalarRawFourier G ξ‖ = W⁻¹ * ‖G ξ‖ := by
    unfold h3SpectralScalarRawFourier h3SobolevFrequencyWeightInvComplex
      h3SobolevFrequencyWeightInv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hW.le)]
  have hScaled : s * (W⁻¹) ^ 2 ≤ 1 := by
    calc
      s * (W⁻¹) ^ 2 = s / W ^ 2 := by
        rw [inv_pow]
        rfl
      _ ≤ 1 := by
        apply (div_le_iff₀ (pow_pos hW 2)).2
        simpa only [one_mul] using hBound
  constructor
  · unfold h3AuditHomogeneousThreeHalvesFourierSquareDensity
    exact mul_nonneg hs (sq_nonneg _)
  · unfold h3AuditHomogeneousThreeHalvesFourierSquareDensity
    change s * ‖h3SpectralScalarRawFourier G ξ‖ ^ 2 ≤ ‖G ξ‖ ^ 2
    calc
      s * ‖h3SpectralScalarRawFourier G ξ‖ ^ 2 =
          (s * (W⁻¹) ^ 2) * ‖G ξ‖ ^ 2 := by
            rw [hRaw]
            ring
      _ ≤ 1 * ‖G ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hScaled (sq_nonneg _)
      _ = ‖G ξ‖ ^ 2 := one_mul _

/-- The Ḣ^(3/2) square density is an honest integrable Fourier density,
with its integral controlled by the original spectral H³ norm squared. -/
theorem h3Audit_homogeneousThreeHalvesDensity_integrable_and_le_norm_sq
    (G : H3SpectralScalarState) :
    Integrable (h3AuditHomogeneousThreeHalvesFourierSquareDensity G)
        (volume : Measure H3FourierPoint3) ∧
    (∫ ξ : H3FourierPoint3,
       h3AuditHomogeneousThreeHalvesFourierSquareDensity G ξ) ≤ ‖G‖ ^ 2 := by
  have hGMeas : AEStronglyMeasurable
      (fun ξ : H3FourierPoint3 => G ξ)
      (volume : Measure H3FourierPoint3) :=
    MeasureTheory.Lp.aestronglyMeasurable G
  have hGInt : Integrable (fun ξ : H3FourierPoint3 => ‖G ξ‖ ^ 2)
      (volume : Measure H3FourierPoint3) :=
    (memLp_two_iff_integrable_sq_norm hGMeas).mp (MeasureTheory.Lp.memLp G)
  have hCoeffCont : Continuous
      (fun ξ : H3FourierPoint3 =>
        Real.sqrt (h3FourierGradientSquare ξ ^ 3)) := by
    unfold h3FourierGradientSquare
    fun_prop
  have hRawMeas : AEStronglyMeasurable
      (h3SpectralScalarRawFourier G)
      (volume : Measure H3FourierPoint3) :=
    (h3SpectralScalarRawFourier_memLp2 G).1
  have hFMeas : AEStronglyMeasurable
      (h3AuditHomogeneousThreeHalvesFourierSquareDensity G)
      (volume : Measure H3FourierPoint3) := by
    unfold h3AuditHomogeneousThreeHalvesFourierSquareDensity
    exact hCoeffCont.aestronglyMeasurable.mul
      ((hRawMeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
  have hFInt : Integrable (h3AuditHomogeneousThreeHalvesFourierSquareDensity G)
      (volume : Measure H3FourierPoint3) := by
    apply Integrable.mono' hGInt hFMeas
    filter_upwards with ξ
    have h := h3Audit_homogeneousThreeHalvesDensity_le_H3Square G ξ
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  refine ⟨hFInt, ?_⟩
  calc
    (∫ ξ : H3FourierPoint3,
       h3AuditHomogeneousThreeHalvesFourierSquareDensity G ξ) ≤
        ∫ ξ : H3FourierPoint3, ‖G ξ‖ ^ 2 := by
          apply integral_mono hFInt hGInt
          intro ξ
          exact (h3Audit_homogeneousThreeHalvesDensity_le_H3Square G ξ).2
    _ = ‖G‖ ^ 2 :=
      (h3FourierComplexL2_norm_sq_eq_integral_norm_sq G).symm

/-- The actual homogeneous three-halves Fourier square density of the
selected physical velocity component at strict preterminal time. -/
noncomputable def h3AuditHomogeneousThreeHalvesVelocityTimeDensity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    ∫ ξ : H3FourierPoint3,
      h3AuditHomogeneousThreeHalvesFourierSquareDensity
        (h3TerminalComplementSpectralStateAt hH3 p t ht) ξ
  else 0

/-- Spatial Fourier integration gives a nonnegative density dominated
by the same component's H³ norm squared, with no additional assumption. -/
theorem h3Audit_homogeneousThreeHalvesTimeDensity_domination
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    0 ≤ h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p t ∧
    h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p t ≤
      ‖h3TerminalComplementSpectralStateAt hH3 p t ht‖ ^ 2 := by
  have hIntBound := h3Audit_homogeneousThreeHalvesDensity_integrable_and_le_norm_sq
    (h3TerminalComplementSpectralStateAt hH3 p t ht)
  have hNonneg : 0 ≤ ∫ ξ : H3FourierPoint3,
      h3AuditHomogeneousThreeHalvesFourierSquareDensity
        (h3TerminalComplementSpectralStateAt hH3 p t ht) ξ := by
    apply integral_nonneg
    intro ξ
    exact (h3Audit_homogeneousThreeHalvesDensity_le_H3Square _ ξ).1
  simpa only [h3AuditHomogeneousThreeHalvesVelocityTimeDensity, dif_pos ht] using
    And.intro hNonneg hIntBound.2

/-- The formerly missing spectral domination is now proved. The ONLY
remaining hypothesis here is the temporal measurability of the actual
homogeneous Sobolev square density. -/
theorem h3Audit_complementEndpoint_homogeneousThreeHalves_integrable_of_timeMeasurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (p : H3TerminalCurlGradientPair)
    (hEndpoint : H3TerminalComplementGradientStrongH3EndpointPath hH3 p)
    (hTimeMeas : Measurable
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      IntegrableOn (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
        (Set.Ioo c T) := by
  exact h3Audit_complementEndpoint_integrable_measurableSpectralDominatedDensity
    hH3 hClass p hEndpoint
    (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
    hTimeMeas
    (fun t ht =>
      h3Audit_homogeneousThreeHalvesTimeDensity_domination hH3 p t ht)

/-- A physical curl-component endpoint gives an integrable homogeneous
three-halves time density for BOTH transverse velocities on one common
terminal interval; time-measurability remains an explicit premise. -/
theorem h3Audit_onePhysicalEndpoint_twoHomogeneousThreeHalves_integrable_of_timeMeasurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hPosMeas : Measurable
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3
        (h3TerminalActualVorticityPositiveComplementPair i)))
    (hNegMeas : Measurable
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3
        (h3TerminalActualVorticityNegativeComplementPair i))) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      IntegrableOn
        (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3
          (h3TerminalActualVorticityPositiveComplementPair i))
        (Set.Ioo c T) ∧
      IntegrableOn
        (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3
          (h3TerminalActualVorticityNegativeComplementPair i))
        (Set.Ioo c T) := by
  exact h3Audit_onePhysicalEndpoint_twoIntegrable_measurableSpectralDominatedDensities
    hH3 hClass i hPhysical
    (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3
      (h3TerminalActualVorticityPositiveComplementPair i))
    (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3
      (h3TerminalActualVorticityNegativeComplementPair i))
    hPosMeas hNegMeas
    (fun t ht => h3Audit_homogeneousThreeHalvesTimeDensity_domination hH3
      (h3TerminalActualVorticityPositiveComplementPair i) t ht)
    (fun t ht => h3Audit_homogeneousThreeHalvesTimeDensity_domination hH3
      (h3TerminalActualVorticityNegativeComplementPair i) t ht)

end
end Euclidean
end Bridge
end PrimeTensor
