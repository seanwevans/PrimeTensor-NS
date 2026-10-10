import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentPhysicalFourierIdentification

/-!
# Physical-space L² realization of the homogeneous three-halves multiplier

The previous checkpoint identified the weighted Fourier three-halves square
energy with the Fourier transform of the ACTUAL logged velocity component.
Here we apply Mathlib's inverse L² Fourier isometry to the already-constructed
contractive multiplier. This produces a bona fide complex physical-space L²
fractional-derivative representative, and proves its spatial L² norm squared
is the exact homogeneous three-halves Fourier square energy.

The equality is an exact Plancherel statement, with the project's 2π Fourier
convention. It does NOT by itself identify the inverse-Fourier object with a
real-valued distributional fractional Laplacian, or formally import any
external Navier--Stokes continuation criterion. Those are separate bridges.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

-- The three-dimensional Fourier carrier is indexed by a finite axis type.
-- Without this local instance Lean cannot synthesize its normed group or
-- canonical product measure, making the inverse Fourier isometry ill-typed.
noncomputable local instance axisFintypeH3AuditPhysicalFractionalL2
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- An honest complex physical L² realization of the homogeneous three-halves
fractional multiplier of a weighted spectral H³ scalar state. The spectral
multiplier equals `(2π |ξ|)^(3/2)` times the *raw* Fourier field. -/
noncomputable def h3AuditThreeHalvesPhysicalFractionalL2
    (G : H3SpectralScalarState) : H3ComplexPhysicalScalarL2 :=
  (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm
    (h3AuditThreeHalvesMultiplierCLM G)

/-- Its Fourier transform is *exactly* the already-proved homogeneous
three-halves spectral multiplier (no new Fourier compatibility premise). -/
@[simp]
theorem h3Audit_fourier_threeHalvesPhysicalFractionalL2
    (G : H3SpectralScalarState) :
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
      (h3AuditThreeHalvesPhysicalFractionalL2 G) =
        h3AuditThreeHalvesMultiplierCLM G := by
  simp [h3AuditThreeHalvesPhysicalFractionalL2]

/-- Exact Plancherel norm identity for the spatial fractional multiplier. -/
theorem h3Audit_threeHalvesPhysicalFractionalL2_norm_sq
    (G : H3SpectralScalarState) :
    ‖h3AuditThreeHalvesPhysicalFractionalL2 G‖ ^ 2 =
      ∫ ξ : H3FourierPoint3,
        h3AuditHomogeneousThreeHalvesFourierSquareDensity G ξ := by
  calc
    ‖h3AuditThreeHalvesPhysicalFractionalL2 G‖ ^ 2 =
        ‖h3AuditThreeHalvesMultiplierCLM G‖ ^ 2 := by
          unfold h3AuditThreeHalvesPhysicalFractionalL2
          rw [(MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm.norm_map]
    _ = ∫ ξ : H3FourierPoint3,
        h3AuditHomogeneousThreeHalvesFourierSquareDensity G ξ :=
      (h3Audit_homogeneousThreeHalvesMass_eq_multiplierNormSq G).symm

/-- The spatial fractional L² derivative of an actual selected preterminal
velocity component, constructed from its genuine weighted H³ snapshot. -/
noncomputable def h3AuditActualVelocityThreeHalvesPhysicalDerivativeAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    H3ComplexPhysicalScalarL2 :=
  h3AuditThreeHalvesPhysicalFractionalL2
    (h3TerminalComplementSpectralStateAt hH3 p t ht)

/-- Exact physical-space squared L² norm of the selected fractional
representative, with no renormalization constant. -/
theorem h3Audit_actualVelocityThreeHalvesPhysicalDerivativeAt_norm_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3AuditActualVelocityThreeHalvesPhysicalDerivativeAt hH3 p t ht‖ ^ 2 =
      h3AuditActualVelocityHomogeneousThreeHalvesFourierSquare hH3 p t := by
  calc
    ‖h3AuditActualVelocityThreeHalvesPhysicalDerivativeAt hH3 p t ht‖ ^ 2 =
      ∫ ξ : H3FourierPoint3,
        h3AuditHomogeneousThreeHalvesFourierSquareDensity
          (h3TerminalComplementSpectralStateAt hH3 p t ht) ξ :=
      h3Audit_threeHalvesPhysicalFractionalL2_norm_sq _
    _ = h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p t := by
      simp [h3AuditHomogeneousThreeHalvesVelocityTimeDensity, ht]
    _ = h3AuditActualVelocityHomogeneousThreeHalvesFourierSquare hH3 p t :=
      (h3Audit_actualVelocityFourierSquare_eq_timeDensity hH3 p t).symm

/-- Zero-extension off the strict preterminal physical-time interval. -/
noncomputable def h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) :
    H3ComplexPhysicalScalarL2 :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    h3AuditActualVelocityThreeHalvesPhysicalDerivativeAt hH3 p t ht
  else 0

/-- The physical-space fractional representative retains the *same* square
energy at every time, including the zero extension. -/
theorem h3Audit_actualVelocityThreeHalvesPhysicalDerivativeTotal_norm_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) :
    ‖h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal hH3 p t‖ ^ 2 =
      h3AuditActualVelocityHomogeneousThreeHalvesFourierSquare hH3 p t := by
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) T
  · simpa only [h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal,
      dif_pos ht] using
        h3Audit_actualVelocityThreeHalvesPhysicalDerivativeAt_norm_sq
          hH3 p t ht
  · simp [h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal,
      h3AuditActualVelocityHomogeneousThreeHalvesFourierSquare, ht]

/-- In particular the spatial L² norm of the realized derivative is exactly
the previously identified velocity Fourier Ḣ^(3/2) seminorm. -/
theorem h3Audit_actualVelocityThreeHalvesPhysicalDerivativeTotal_norm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) :
    ‖h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal hH3 p t‖ =
      h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm hH3 p t := by
  have hSq := h3Audit_actualVelocityThreeHalvesPhysicalDerivativeTotal_norm_sq
    hH3 p t
  have hNonneg := h3Audit_homogeneousThreeHalvesTimeDensity_nonneg hH3 p t
  have hF := h3Audit_actualVelocityFourierSquare_eq_timeDensity hH3 p t
  have hRoot :
      h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm hH3 p t ^ 2 =
        h3AuditActualVelocityHomogeneousThreeHalvesFourierSquare hH3 p t := by
    unfold h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm
    rw [Real.sq_sqrt]
    rw [hF]
    exact hNonneg
  have hPos : 0 ≤ h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm
      hH3 p t := Real.sqrt_nonneg _
  nlinarith only [hSq, hRoot,
    norm_nonneg (h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal hH3 p t),
    hPos]

/-- A physical curl-component endpoint produces the actual fractional
physical-space L² norms in time L² for both transverse velocity coordinates
on the same late interval. This remains conditional on `hPhysical`. -/
theorem h3Audit_onePhysicalEndpoint_twoPhysicalFractionalDerivative_timeL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      MemLp (fun t : ℝ =>
        ‖h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal hH3
          (h3TerminalActualVorticityPositiveComplementPair i) t‖)
        2 (volume.restrict (Set.Ioo c T)) ∧
      MemLp (fun t : ℝ =>
        ‖h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal hH3
          (h3TerminalActualVorticityNegativeComplementPair i) t‖)
        2 (volume.restrict (Set.Ioo c T)) := by
  obtain ⟨c, hc, hP, hN⟩ :=
    h3Audit_onePhysicalEndpoint_twoActualVelocityFourier_timeL2
      hH3 hClass i hPhysical
  refine ⟨c, hc, ?_, ?_⟩
  · have hEq :
        (fun t : ℝ =>
          ‖h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal hH3
            (h3TerminalActualVorticityPositiveComplementPair i) t‖) =
        h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm hH3
          (h3TerminalActualVorticityPositiveComplementPair i) := by
      funext t
      exact h3Audit_actualVelocityThreeHalvesPhysicalDerivativeTotal_norm hH3 _ t
    rw [hEq]
    exact hP
  · have hEq :
        (fun t : ℝ =>
          ‖h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal hH3
            (h3TerminalActualVorticityNegativeComplementPair i) t‖) =
        h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm hH3
          (h3TerminalActualVorticityNegativeComplementPair i) := by
      funext t
      exact h3Audit_actualVelocityThreeHalvesPhysicalDerivativeTotal_norm hH3 _ t
    rw [hEq]
    exact hN

end
end Euclidean
end Bridge
end PrimeTensor
