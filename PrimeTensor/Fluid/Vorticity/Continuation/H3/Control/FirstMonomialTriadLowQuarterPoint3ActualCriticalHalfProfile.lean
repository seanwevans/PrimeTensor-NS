import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3ActualDilationMonomial
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3CriticalHalfDilationScalar

/-!
# Actual critical-half estimate along every spatial dilation of one profile

The full 243-slot Point3 monomial has spatial degree four, the complete
fourth-derivative dissipation has degree five, and the four quadratic H3
energy orders have degrees -3, -1, 1, and 3, respectively.

The previously proved scalar fixed-shape estimate therefore applies to the
ACTUAL real Schwartz integrals. We retain all three velocity components,
all ordered derivative slots, and the canonical constant 1 in the final
square-root energy weight.

This is a *profile-dependent* coefficient under explicit positive endpoint
mass assumptions, NOT a coefficient uniform across Schwartz profiles, and
NOT a Navier--Stokes continuation or blowup theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeQuarterCriticalProfile (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every squared Schwartz component has nonnegative spatial integral. -/
theorem lowNormalRealSchwartzH3Energy0_nonneg
    (f : A3 → SchwartzMap V3 ℝ) :
    0 ≤ lowNormalRealSchwartzH3Energy0 f := by
  unfold lowNormalRealSchwartzH3Energy0
  apply Finset.sum_nonneg
  intro j _
  exact integral_nonneg (fun x => sq_nonneg (f j x))

/-- The complete first-derivative square mass is nonnegative. -/
theorem lowNormalRealSchwartzH3Energy1_nonneg
    (f : A3 → SchwartzMap V3 ℝ) :
    0 ≤ lowNormalRealSchwartzH3Energy1 f := by
  unfold lowNormalRealSchwartzH3Energy1
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg (fun x =>
    sq_nonneg ((∂_{h3FourierAxisDirection i} (f j)) x))

/-- All 27 second-derivative square integrals have nonnegative sum. -/
theorem lowNormalRealSchwartzH3Energy2_nonneg
    (f : A3 → SchwartzMap V3 ℝ) :
    0 ≤ lowNormalRealSchwartzH3Energy2 f := by
  unfold lowNormalRealSchwartzH3Energy2
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro k _
  exact integral_nonneg (fun x =>
    sq_nonneg ((∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k} (f j))) x))

/-- All 81 third-derivative square integrals have nonnegative sum. -/
theorem lowNormalRealSchwartzH3Energy3_nonneg
    (f : A3 → SchwartzMap V3 ℝ) :
    0 ≤ lowNormalRealSchwartzH3Energy3 f := by
  unfold lowNormalRealSchwartzH3Energy3
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro l _
  exact integral_nonneg (fun x =>
    sq_nonneg ((∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k}
        (∂_{h3FourierAxisDirection l} (f j)))) x))

/-- Every one of the actual 243 fourth-order dissipation integrals is
nonnegative. -/
theorem lowNormalRealSchwartzH3TopDissipation_nonneg
    (f : A3 → SchwartzMap V3 ℝ) :
    0 ≤ lowNormalRealSchwartzH3TopDissipation f := by
  unfold lowNormalRealSchwartzH3TopDissipation
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro l _
  apply Finset.sum_nonneg
  intro m _
  exact integral_nonneg (fun x =>
    sq_nonneg ((∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k}
        (∂_{h3FourierAxisDirection l}
          (∂_{h3FourierAxisDirection m} (f j))))) x))

/-- The existing unnormalized H3 quadratic energy is definitionally the
sum of the four newly scaled complete Schwartz energy blocks. -/
theorem lowNormalRealSchwartzH3EnergyQuadratic_eq_sum
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3EnergyQuadratic f =
      lowNormalRealSchwartzH3Energy0 f +
      lowNormalRealSchwartzH3Energy1 f +
      lowNormalRealSchwartzH3Energy2 f +
      lowNormalRealSchwartzH3Energy3 f := by
  rfl

/-- Exact dilation law for the pre-existing four-order quadratic energy. -/
theorem lowNormalRealSchwartzH3EnergyQuadratic_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3EnergyQuadratic
        (lowNormalSchwartzVelocityDilation scale hscale f) =
      (scale ^ 3)⁻¹ * lowNormalRealSchwartzH3Energy0 f +
      (scale ^ 2 * (scale ^ 3)⁻¹) * lowNormalRealSchwartzH3Energy1 f +
      (scale ^ 4 * (scale ^ 3)⁻¹) * lowNormalRealSchwartzH3Energy2 f +
      (scale ^ 6 * (scale ^ 3)⁻¹) * lowNormalRealSchwartzH3Energy3 f := by
  rw [lowNormalRealSchwartzH3EnergyQuadratic_eq_sum]
  rw [lowNormalRealSchwartzH3Energy0_dilation,
    lowNormalRealSchwartzH3Energy1_dilation,
    lowNormalRealSchwartzH3Energy2_dilation,
    lowNormalRealSchwartzH3Energy3_dilation]

/-- The true normalized energy is 1 plus the old quadratic energy. -/
theorem lowNormalRealSchwartzH3Energy_eq_one_add_quadratic
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy f =
      1 + lowNormalRealSchwartzH3EnergyQuadratic f := by
  rw [lowNormalRealSchwartzH3EnergyQuadratic_eq_sum]
  unfold lowNormalRealSchwartzH3Energy
  ring

/-- The unnormalized quadratic energy is nonnegative without extra
Schwartz moment or PDE assumptions. -/
theorem lowNormalRealSchwartzH3EnergyQuadratic_nonneg
    (f : A3 → SchwartzMap V3 ℝ) :
    0 ≤ lowNormalRealSchwartzH3EnergyQuadratic f := by
  rw [lowNormalRealSchwartzH3EnergyQuadratic_eq_sum]
  have h0 := lowNormalRealSchwartzH3Energy0_nonneg f
  have h1 := lowNormalRealSchwartzH3Energy1_nonneg f
  have h2 := lowNormalRealSchwartzH3Energy2_nonneg f
  have h3 := lowNormalRealSchwartzH3Energy3_nonneg f
  exact add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3

set_option maxHeartbeats 800000

/-- The actual squared critical-half inequality at one dilation follows
from the previous scalar polynomial bound, after cancellation of the
positive seventh power of the scale. No new profile estimate is assumed. -/
theorem lowNormalRealSchwartz_criticalHalf_squared_dilation_of_scalar
    (f : A3 → SchwartzMap V3 ℝ) (C scale : ℝ)
    (hscale : 0 < scale)
    (hScalar :
      (lowNormalRealSchwartzPoint3Monomial f) ^ 2 * scale ≤
        C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
          (lowNormalRealSchwartzH3Energy0 f +
            scale ^ 2 * lowNormalRealSchwartzH3Energy1 f +
            scale ^ 4 * lowNormalRealSchwartzH3Energy2 f +
            scale ^ 6 * lowNormalRealSchwartzH3Energy3 f)) :
    (lowNormalRealSchwartzPoint3Monomial
        (lowNormalSchwartzVelocityDilation scale hscale f)) ^ 2 ≤
      C ^ 2 *
        (lowNormalRealSchwartzH3TopDissipation
          (lowNormalSchwartzVelocityDilation scale hscale f)) ^ 2 *
        lowNormalRealSchwartzH3EnergyQuadratic
          (lowNormalSchwartzVelocityDilation scale hscale f) := by
  rw [lowNormalRealSchwartzPoint3Monomial_dilation,
    lowNormalRealSchwartzH3TopDissipation_dilation,
    lowNormalRealSchwartzH3EnergyQuadratic_dilation]
  have hs : scale ≠ 0 := ne_of_gt hscale
  have hScaled := mul_le_mul_of_nonneg_left hScalar
    (pow_nonneg hscale.le 7)
  calc
    (scale ^ 4 * lowNormalRealSchwartzPoint3Monomial f) ^ 2 =
        scale ^ 7 * ((lowNormalRealSchwartzPoint3Monomial f) ^ 2 * scale) := by
      ring
    _ ≤ scale ^ 7 * (C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
        (lowNormalRealSchwartzH3Energy0 f +
          scale ^ 2 * lowNormalRealSchwartzH3Energy1 f +
          scale ^ 4 * lowNormalRealSchwartzH3Energy2 f +
          scale ^ 6 * lowNormalRealSchwartzH3Energy3 f)) := hScaled
    _ = C ^ 2 *
        ((scale ^ 8 * (scale ^ 3)⁻¹) * lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
        ((scale ^ 3)⁻¹ * lowNormalRealSchwartzH3Energy0 f +
          (scale ^ 2 * (scale ^ 3)⁻¹) * lowNormalRealSchwartzH3Energy1 f +
          (scale ^ 4 * (scale ^ 3)⁻¹) * lowNormalRealSchwartzH3Energy2 f +
          (scale ^ 6 * (scale ^ 3)⁻¹) * lowNormalRealSchwartzH3Energy3 f) := by
      field_simp [hs]
      <;> ring

/-- For any fixed real Schwartz velocity with positive E0, E3 and fourth-
derivative mass, one finite profile-specific coefficient controls the *actual*
squared critical-half estimate at every positive isotropic spatial dilation. -/
theorem lowNormalRealSchwartz_exists_criticalHalf_squared_dilation_coefficient
    (f : A3 → SchwartzMap V3 ℝ)
    (hD : 0 < lowNormalRealSchwartzH3TopDissipation f)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hE3 : 0 < lowNormalRealSchwartzH3Energy3 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ scale : ℝ, ∀ hscale : 0 < scale,
      (lowNormalRealSchwartzPoint3Monomial
        (lowNormalSchwartzVelocityDilation scale hscale f)) ^ 2 ≤
        C ^ 2 *
          (lowNormalRealSchwartzH3TopDissipation
            (lowNormalSchwartzVelocityDilation scale hscale f)) ^ 2 *
          lowNormalRealSchwartzH3EnergyQuadratic
            (lowNormalSchwartzVelocityDilation scale hscale f) := by
  obtain ⟨C, hC, hAll⟩ := criticalHalfDilation_exists_uniform_coefficient
    (lowNormalRealSchwartzPoint3Monomial f)
    (lowNormalRealSchwartzH3TopDissipation f)
    (lowNormalRealSchwartzH3Energy0 f)
    (lowNormalRealSchwartzH3Energy1 f)
    (lowNormalRealSchwartzH3Energy2 f)
    (lowNormalRealSchwartzH3Energy3 f)
    hD hE0 hE3
    (lowNormalRealSchwartzH3Energy1_nonneg f)
    (lowNormalRealSchwartzH3Energy2_nonneg f)
  refine ⟨C, hC, ?_⟩
  intro scale hscale
  exact lowNormalRealSchwartz_criticalHalf_squared_dilation_of_scalar
    f C scale hscale (hAll scale hscale.le)

/-- Unsquared physical endpoint estimate, with the canonical normalized
H3 energy (including its constant one). The coefficient depends on `f` and
remains uniform only over its spatial dilation orbit. -/
theorem lowNormalRealSchwartz_exists_criticalHalf_dilation_coefficient
    (f : A3 → SchwartzMap V3 ℝ)
    (hD : 0 < lowNormalRealSchwartzH3TopDissipation f)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hE3 : 0 < lowNormalRealSchwartzH3Energy3 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ scale : ℝ, ∀ hscale : 0 < scale,
      lowNormalRealSchwartzPoint3Monomial
          (lowNormalSchwartzVelocityDilation scale hscale f) ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy
          (lowNormalSchwartzVelocityDilation scale hscale f)) *
          lowNormalRealSchwartzH3TopDissipation
            (lowNormalSchwartzVelocityDilation scale hscale f) := by
  obtain ⟨C, hC, hAll⟩ :=
    lowNormalRealSchwartz_exists_criticalHalf_squared_dilation_coefficient
      f hD hE0 hE3
  refine ⟨C, hC, ?_⟩
  intro scale hscale
  let g := lowNormalSchwartzVelocityDilation scale hscale f
  let E := lowNormalRealSchwartzH3EnergyQuadratic g
  let D := lowNormalRealSchwartzH3TopDissipation g
  let M := lowNormalRealSchwartzPoint3Monomial g
  let R := C * Real.sqrt (lowNormalRealSchwartzH3Energy g) * D
  have hE : 0 ≤ E := lowNormalRealSchwartzH3EnergyQuadratic_nonneg g
  have hDg : 0 ≤ D := lowNormalRealSchwartzH3TopDissipation_nonneg g
  have hTotal : lowNormalRealSchwartzH3Energy g = 1 + E :=
    lowNormalRealSchwartzH3Energy_eq_one_add_quadratic g
  have hSqrt : (Real.sqrt (lowNormalRealSchwartzH3Energy g)) ^ 2 =
      1 + E := by
    rw [Real.sq_sqrt]
    · exact hTotal
    · rw [hTotal]
      linarith
  have hBound : M ^ 2 ≤ C ^ 2 * D ^ 2 * E := hAll scale hscale
  have hLarger : M ^ 2 ≤ C ^ 2 * D ^ 2 * (1 + E) := by
    calc
      M ^ 2 ≤ C ^ 2 * D ^ 2 * E := hBound
      _ ≤ C ^ 2 * D ^ 2 * (1 + E) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) hDg
  have hR2 : R ^ 2 = C ^ 2 * D ^ 2 * (1 + E) := by
    dsimp [R]
    rw [mul_pow, mul_pow, hSqrt]
    ring
  change M ≤ R
  nlinarith [hLarger, hR2]

end
end PrimeTensor.FirstMonomialTriad
