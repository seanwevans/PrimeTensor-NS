import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentPhysicalFractionalL2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Convolution.Reality

/-!
# Real-valued homogeneous three-halves physical fractional derivative

The physical fractional L² realization in `OneComponentPhysicalFractionalL2`
is complex-valued because the Fourier isometry is complex. Its input, however,
is the canonical weighted Fourier encoding of an actual **real** velocity.

The homogeneous multiplier is real and even in frequency. The exact raw
Fourier transform of a real velocity is Hermitian. These facts imply that the
fractional Fourier multiplier is Hermitian as an L² class. The existing
Hermitian inverse-Fourier theorem therefore identifies the complex physical
fractional derivative with the complexification of a real physical L² state.

All identifications concern the actual velocity Fourier snapshot and the
project's exact `(2*pi)` convention. The external one-component continuation
theorem and an independent distributional Sobolev-space equivalence remain
separate obligations. No unconditional continuation is claimed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3AuditRealFractionalL2
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The homogeneous three-halves scalar multiplier, applied to a weighted
spectral state, is the raw Fourier amplitude multiplied by the actual
`(2*pi*|xi|)^(3/2)` frequency factor. -/
theorem h3Audit_threeHalvesMultiplierCLM_ae_raw
    (G : H3SpectralScalarState) :
    (h3AuditThreeHalvesMultiplierCLM G : H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (Real.sqrt (Real.sqrt (h3FourierGradientSquare ξ ^ 3)) : ℂ) *
        h3SpectralScalarRawFourier G ξ) := by
  rw [h3Audit_threeHalvesMultiplierCLM_apply]
  filter_upwards [h3Audit_threeHalvesMultiplierApply_ae G] with ξ hξ
  rw [hξ]
  unfold h3AuditThreeHalvesFourierMultiplier
    h3SpectralScalarRawFourier h3SobolevFrequencyWeightInvComplex
  push_cast
  ring

/-- The homogeneous fractional Fourier factor has even parity. -/
@[simp]
theorem h3Audit_threeHalvesRawFourierWeight_neg
    (ξ : H3FourierPoint3) :
    Real.sqrt (Real.sqrt (h3FourierGradientSquare (-ξ) ^ 3)) =
      Real.sqrt (Real.sqrt (h3FourierGradientSquare ξ ^ 3)) := by
  rw [h3FourierGradientSquare_neg]

/-- Real-even scalar multiplication preserves the exact L² Hermitian
condition, using the genuine raw velocity Fourier representative. -/
theorem h3Audit_threeHalvesMultiplierCLM_hermitian
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRawHermitian G) :
    H3FourierL2Hermitian (h3AuditThreeHalvesMultiplierCLM G) := by
  unfold H3FourierL2Hermitian
  have hAt := h3Audit_threeHalvesMultiplierCLM_ae_raw G
  have hNeg := h3Fourier_ae_neg hAt
  have hRaw := h3SpectralScalarRawFourier_hermitian_ae hG
  filter_upwards [hAt, hNeg, hRaw] with ξ hAtξ hNegξ hRawξ
  rw [hNegξ, hAtξ, hRawξ, h3Audit_threeHalvesRawFourierWeight_neg]
  simp only [map_mul, Complex.conj_ofReal]

/-- The inverse Fourier physical fractional derivative is the exact
complexification of its real part whenever the raw input is Hermitian. -/
theorem h3Audit_threeHalvesPhysicalFractionalL2_eq_complexify_real
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRawHermitian G) :
    h3AuditThreeHalvesPhysicalFractionalL2 G =
      h3ComplexifyFourierL2
        (h3RealPartFourierL2 (h3AuditThreeHalvesPhysicalFractionalL2 G)) := by
  unfold h3AuditThreeHalvesPhysicalFractionalL2
  exact h3FourierL2Hermitian_fourierInv_eq_complexify_real
    (h3AuditThreeHalvesMultiplierCLM G)
    (h3Audit_threeHalvesMultiplierCLM_hermitian hG)

/-- Real physical L² derivative associated to a weighted spectral scalar
state. Its real-valuedness is by construction, while its exact agreement
with the complex inverse Fourier state requires the Hermitian hypothesis. -/
noncomputable def h3AuditThreeHalvesPhysicalFractionalRealL2
    (G : H3SpectralScalarState) : H3FourierRealL2 :=
  h3RealPartFourierL2 (h3AuditThreeHalvesPhysicalFractionalL2 G)

/-- On real physical data the fractional real and complex L² norms are
exactly equal, without an additional normalization factor. -/
theorem h3Audit_threeHalvesPhysicalFractionalRealL2_norm_eq
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRawHermitian G) :
    ‖h3AuditThreeHalvesPhysicalFractionalRealL2 G‖ =
      ‖h3AuditThreeHalvesPhysicalFractionalL2 G‖ := by
  have hReal := h3Audit_threeHalvesPhysicalFractionalL2_eq_complexify_real hG
  rw [hReal]
  exact (norm_h3ComplexifyFourierL2_eq
    (h3AuditThreeHalvesPhysicalFractionalRealL2 G)).symm

/-- A strict-time complementary component is the Fourier encoding of a real
physical velocity component, so its deweighted Fourier state is Hermitian. -/
theorem h3Audit_complementSpectralState_rawHermitian
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    H3SpectralScalarRawHermitian
      (h3TerminalComplementSpectralStateAt hH3 p t ht) := by
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht hInt
  change H3SpectralScalarRawHermitian
    (velocityH3SpectralScalarAt u t hInt hMeas hFourier
      (h3ClassicalizationFinOfAxis
        (h3TerminalComplementComponentAxisForPair p)))
  exact velocityH3SpectralScalarAt_rawHermitian hFourier _

/-- The exact real physical-space fractional derivative at a strict
preterminal time (not just the complexification of a formal field). -/
noncomputable def h3AuditActualVelocityThreeHalvesRealDerivativeAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) : H3FourierRealL2 :=
  h3AuditThreeHalvesPhysicalFractionalRealL2
    (h3TerminalComplementSpectralStateAt hH3 p t ht)

/-- The previously constructed complex physical derivative of the *actual*
velocity is the complexification of this real physical derivative. -/
theorem h3Audit_actualVelocityThreeHalvesPhysicalDerivativeAt_eq_complexify_real
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3AuditActualVelocityThreeHalvesPhysicalDerivativeAt hH3 p t ht =
      h3ComplexifyFourierL2
        (h3AuditActualVelocityThreeHalvesRealDerivativeAt hH3 p t ht) := by
  exact h3Audit_threeHalvesPhysicalFractionalL2_eq_complexify_real
    (h3Audit_complementSpectralState_rawHermitian hH3 p t ht)

/-- The real fractional derivative inherits the *exact* homogeneous
three-halves Fourier square seminorm of the physical velocity. -/
theorem h3Audit_actualVelocityThreeHalvesRealDerivativeAt_norm_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3AuditActualVelocityThreeHalvesRealDerivativeAt hH3 p t ht‖ ^ 2 =
      h3AuditActualVelocityHomogeneousThreeHalvesFourierSquare hH3 p t := by
  calc
    ‖h3AuditActualVelocityThreeHalvesRealDerivativeAt hH3 p t ht‖ ^ 2 =
      ‖h3AuditActualVelocityThreeHalvesPhysicalDerivativeAt hH3 p t ht‖ ^ 2 := by
        congr 1
        exact h3Audit_threeHalvesPhysicalFractionalRealL2_norm_eq
          (h3Audit_complementSpectralState_rawHermitian hH3 p t ht)
    _ = _ :=
      h3Audit_actualVelocityThreeHalvesPhysicalDerivativeAt_norm_sq
        hH3 p t ht

/-- Extend the real physical derivative by zero outside `(0,T)` to match
the exact zero extension of the already defined Fourier seminorms. -/
noncomputable def h3AuditActualVelocityThreeHalvesRealDerivativeTotal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) : H3FourierRealL2 :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    h3AuditActualVelocityThreeHalvesRealDerivativeAt hH3 p t ht
  else 0

/-- The real and complex fractional derivative norm profiles agree at all
real times, including outside the strict preterminal interval. -/
theorem h3Audit_actualVelocityThreeHalvesRealDerivativeTotal_norm_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) :
    ‖h3AuditActualVelocityThreeHalvesRealDerivativeTotal hH3 p t‖ =
      ‖h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal hH3 p t‖ := by
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) T
  · simp only [h3AuditActualVelocityThreeHalvesRealDerivativeTotal,
        h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal, dif_pos ht]
    exact h3Audit_threeHalvesPhysicalFractionalRealL2_norm_eq
      (h3Audit_complementSpectralState_rawHermitian hH3 p t ht)
  · simp [h3AuditActualVelocityThreeHalvesRealDerivativeTotal,
      h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal, ht]

/-- A one-physical-curl-component endpoint gives real physical
fractional-derivative norms of both transverse velocity coordinates in
`L²` time on one common strict terminal interval. -/
theorem h3Audit_onePhysicalEndpoint_twoRealFractionalDerivative_timeL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      MemLp (fun t : ℝ =>
        ‖h3AuditActualVelocityThreeHalvesRealDerivativeTotal hH3
          (h3TerminalActualVorticityPositiveComplementPair i) t‖)
        2 (volume.restrict (Set.Ioo c T)) ∧
      MemLp (fun t : ℝ =>
        ‖h3AuditActualVelocityThreeHalvesRealDerivativeTotal hH3
          (h3TerminalActualVorticityNegativeComplementPair i) t‖)
        2 (volume.restrict (Set.Ioo c T)) := by
  obtain ⟨c, hc, hPos, hNeg⟩ :=
    h3Audit_onePhysicalEndpoint_twoPhysicalFractionalDerivative_timeL2
      hH3 hClass i hPhysical
  refine ⟨c, hc, ?_, ?_⟩
  · have hEq :
        (fun t : ℝ =>
          ‖h3AuditActualVelocityThreeHalvesRealDerivativeTotal hH3
            (h3TerminalActualVorticityPositiveComplementPair i) t‖) =
        (fun t : ℝ =>
          ‖h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal hH3
            (h3TerminalActualVorticityPositiveComplementPair i) t‖) := by
      funext t
      exact h3Audit_actualVelocityThreeHalvesRealDerivativeTotal_norm_eq hH3 _ t
    rw [hEq]
    exact hPos
  · have hEq :
        (fun t : ℝ =>
          ‖h3AuditActualVelocityThreeHalvesRealDerivativeTotal hH3
            (h3TerminalActualVorticityNegativeComplementPair i) t‖) =
        (fun t : ℝ =>
          ‖h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal hH3
            (h3TerminalActualVorticityNegativeComplementPair i) t‖) := by
      funext t
      exact h3Audit_actualVelocityThreeHalvesRealDerivativeTotal_norm_eq hH3 _ t
    rw [hEq]
    exact hNeg

end
end Euclidean
end Bridge
end PrimeTensor
