import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalRadialTightnessEquivalence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalHighRadialDissipationCost244
import Mathlib.Tactic

/-!
# Full-third high-radial velocity mass pays genuine H³ viscosity

The high-radial projection used by the solenoidal Fourier flux is defined
componentwise in the native weighted Fourier L² product, whose norm is a
SUP norm. The physical radial dissipation estimates instead use the sum of
all three component squared Fourier amplitudes. This module proves their
exact compatibility. In particular, no identification of the sup norm with
three-coordinate Hilbert energy is made.

For rho = R+1, the physical high H³ dissipation and full H³ dissipation
both exceed rho² times the squared sup norm of the weighted high-radial
velocity. No Schwartz representative or endpoint regularity is assumed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeHighRadialViscousCoercivity244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The sum-of-squares Fourier energy of the exact highpass velocity is the
already-normalized complementary radial H³ square mass. -/
theorem thirdFullSpectralVelocityHighRadial_squareEnergy_eq_remainder244
    (R : ℕ) (U : H3SpectralVelocityState) :
    h3SpectralVelocitySquareEnergy
        (thirdFullSpectralVelocityHighRadialApply244 R U) =
      h3PathActualSpectralHighRadialRemainder244 ((R : ℝ) + 1) U := by
  let S : Set V3 := h3TopTailNaturalHighRadialSet R
  have hS : MeasurableSet S := measurableSet_h3TopTailNaturalHighRadialSet R
  calc
    h3SpectralVelocitySquareEnergy
        (thirdFullSpectralVelocityHighRadialApply244 R U) =
      ∫ ξ : V3,
        h3TerminalSpectralStateSquareAmplitude
          (thirdFullSpectralVelocityHighRadialApply244 R U) ξ ∂volume :=
          h3Path_spectralSquareEnergy_eq_totalFourierIntegral244 _
    _ = ∫ ξ : V3, S.indicator (h3TerminalSpectralStateSquareAmplitude U) ξ
          ∂volume := by
      apply integral_congr_ae
      filter_upwards [
        thirdFullSpectralHighRadialApply_ae244 R (U 0),
        thirdFullSpectralHighRadialApply_ae244 R (U 1),
        thirdFullSpectralHighRadialApply_ae244 R (U 2)
      ] with ξ h0 h1 h2
      change
        ‖(thirdFullSpectralHighRadialApply244 R (U 0) : V3 → ℂ) ξ‖ ^ 2 +
          ‖(thirdFullSpectralHighRadialApply244 R (U 1) : V3 → ℂ) ξ‖ ^ 2 +
          ‖(thirdFullSpectralHighRadialApply244 R (U 2) : V3 → ℂ) ξ‖ ^ 2 =
        S.indicator (h3TerminalSpectralStateSquareAmplitude U) ξ
      rw [h0, h1, h2]
      -- Use the unfolded Fourier set in the case split: `S` is a local
      -- abbreviation, while the ae representatives use the original set.
      by_cases hξ : ξ ∈ h3TopTailNaturalHighRadialSet R
      · simp only [S, Set.indicator_of_mem hξ]
        rfl
      · simp [S, Set.indicator_of_notMem hξ]
    _ = ∫ ξ in S, h3TerminalSpectralStateSquareAmplitude U ξ ∂volume := by
      exact integral_indicator hS
    _ = h3PathActualSpectralHighRadialRemainder244 ((R : ℝ) + 1) U := by
      simpa only [S, h3TopTailNaturalHighRadialSet] using
        (h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244
          ((R : ℝ) + 1) U).symm

/-- The vector carrier has a sup norm, not the sum of three squared component
norms. Its squared highpass norm is nevertheless bounded by the exact
three-coordinate Fourier high-radial square mass. -/
theorem thirdFullSpectralVelocityHighRadial_norm_sq_le_remainder244
    (R : ℕ) (U : H3SpectralVelocityState) :
    ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ ^ 2 ≤
      h3PathActualSpectralHighRadialRemainder244 ((R : ℝ) + 1) U := by
  calc
    ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ ^ 2 ≤
      h3SpectralVelocitySquareEnergy
        (thirdFullSpectralVelocityHighRadialApply244 R U) :=
          h3Path_spectralSupNorm_sq_le_squareEnergy244 _
    _ = h3PathActualSpectralHighRadialRemainder244 ((R : ℝ) + 1) U :=
      thirdFullSpectralVelocityHighRadial_squareEnergy_eq_remainder244 R U

/-- The exact physical high-radial H³ viscous density charges the original
highpass solenoidal Fourier carrier with the sharp frequency-square factor. -/
theorem thirdFullPhysical_highRadialViscousCoercivity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (R : ℕ) :
    ((R : ℝ) + 1) ^ 2 *
      ‖thirdFullSpectralVelocityHighRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2 ≤
      h3PathActualHighRadialDissipation244 ((R : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  have hMass := thirdFullSpectralVelocityHighRadial_norm_sq_le_remainder244
    R (h3AuditActualSpectralVelocityTotal hH3 t)
  have hDiss := h3Path_actualHighRadialDissipation_ge_squareHighMass244
    hH3 hClass t ht ((R : ℝ) + 1) (by positivity)
  exact (mul_le_mul_of_nonneg_left hMass (sq_nonneg _)).trans hDiss

/-- The full physical fourth-spatial-derivative H³ dissipation also pays the
same exact highpass cost, by the already-proved physical radial partition. -/
theorem thirdFullPhysical_fullViscousCoercivity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (R : ℕ) :
    ((R : ℝ) + 1) ^ 2 *
      ‖thirdFullSpectralVelocityHighRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2 ≤
      velocityH3DissipationAt u t := by
  have hMass := thirdFullSpectralVelocityHighRadial_norm_sq_le_remainder244
    R (h3AuditActualSpectralVelocityTotal hH3 t)
  have hDiss := h3Path_highRadialMass_le_fullDissipationAt244
    hH3 hClass t ht ((R : ℝ) + 1) (by positivity)
  exact (mul_le_mul_of_nonneg_left hMass (sq_nonneg _)).trans hDiss

end
end PrimeTensor.FirstMonomialTriad
