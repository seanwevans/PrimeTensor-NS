import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3ActualCriticalHalfProfile

/-!
# Uniform critical-half endpoint: exact positive-shape criterion

The preceding module proves a coefficient on the spatial dilation orbit of
one Schwartz velocity. That coefficient may depend on the profile. Here we
characterize what would be needed for one coefficient valid for ALL real
Schwartz velocity profiles (hence, in particular, for all solenoidal ones).

Write `M(f)` for the signed complete physical 243-slot first monomial,
`E(f)` for the entire unnormalized quadratic H3 energy, and `D(f)` for
all 243 top-order fourth-derivative square integrals. The normalized
energy is `1 + E(f)`.

For a fixed nonnegative C, the following are equivalent:

* M(f) <= C * sqrt(1 + E(f)) * D(f) for every real Schwartz profile f;
* M(f)^2 <= C^2 * D(f)^2 * E(f) for every such f with M(f) > 0.

The first implication is NOT obtained by dropping the normalizing 1. It uses
the already proved arbitrary-amplitude laws and the exact endpoint
amplitude-ray characterization. The converse uses nonnegativity of the
quadratic forms and the inclusion E <= 1 + E.

We also isolate an amplitude-homogeneous shape-excess functional. Positive
excess for even one positive-monomial profile rules out that particular C.
We do NOT prove that such profiles exist for every C, or claim a global
Navier--Stokes regularity or nonextension theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeCriticalHalfUniformShape (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- On ALL real Schwartz profiles, the normalized critical-half endpoint
estimate is equivalent to a homogeneous *positive-shape* threshold. The
latter is required only when the signed first monomial is positive. -/
theorem lowNormalRealSchwartz_uniformCriticalHalf_iff_positiveShapeThreshold
    (C : ℝ) (hC : 0 ≤ C) :
    (∀ f : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartzPoint3Monomial f ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy f) *
          lowNormalRealSchwartzH3TopDissipation f) ↔
    (∀ f : A3 → SchwartzMap V3 ℝ,
      0 < lowNormalRealSchwartzPoint3Monomial f →
        (lowNormalRealSchwartzPoint3Monomial f) ^ 2 ≤
          C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
            lowNormalRealSchwartzH3EnergyQuadratic f) := by
  constructor
  · intro hUniform f hM
    have hE : 0 ≤ lowNormalRealSchwartzH3EnergyQuadratic f :=
      lowNormalRealSchwartzH3EnergyQuadratic_nonneg f
    have hD : 0 ≤ lowNormalRealSchwartzH3TopDissipation f :=
      lowNormalRealSchwartzH3TopDissipation_nonneg f
    have hB : 0 ≤ C * lowNormalRealSchwartzH3TopDissipation f :=
      mul_nonneg hC hD
    have hRay : ∀ a : ℝ, 0 < a →
        a ^ 3 * lowNormalRealSchwartzPoint3Monomial f ≤
          (C * lowNormalRealSchwartzH3TopDissipation f) *
            Real.sqrt (1 + a ^ 2 * lowNormalRealSchwartzH3EnergyQuadratic f) *
            a ^ 2 := by
      intro a ha
      have hAt := hUniform (fun j : A3 => a • f j)
      rw [lowNormalRealSchwartzPoint3Monomial_real_smul,
        lowNormalRealSchwartzH3TopDissipation_real_smul,
        lowNormalRealSchwartzH3Energy_eq_one_add_quadratic,
        lowNormalRealSchwartzH3EnergyQuadratic_real_smul] at hAt
      calc
        a ^ 3 * lowNormalRealSchwartzPoint3Monomial f ≤
            C * Real.sqrt (1 + a ^ 2 * lowNormalRealSchwartzH3EnergyQuadratic f) *
              (a ^ 2 * lowNormalRealSchwartzH3TopDissipation f) := hAt
        _ = (C * lowNormalRealSchwartzH3TopDissipation f) *
              Real.sqrt (1 + a ^ 2 * lowNormalRealSchwartzH3EnergyQuadratic f) *
              a ^ 2 := by ring
    have hThreshold :=
      (criticalHalfEnergyRayBound_iff
        (lowNormalRealSchwartzPoint3Monomial f)
        (lowNormalRealSchwartzH3EnergyQuadratic f)
        (C * lowNormalRealSchwartzH3TopDissipation f)
        hM hE hB).mp hRay
    calc
      (lowNormalRealSchwartzPoint3Monomial f) ^ 2 ≤
          (C * lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
            lowNormalRealSchwartzH3EnergyQuadratic f := hThreshold
      _ = C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
            lowNormalRealSchwartzH3EnergyQuadratic f := by ring
  · intro hShape f
    have hD : 0 ≤ lowNormalRealSchwartzH3TopDissipation f :=
      lowNormalRealSchwartzH3TopDissipation_nonneg f
    have hE : 0 ≤ lowNormalRealSchwartzH3EnergyQuadratic f :=
      lowNormalRealSchwartzH3EnergyQuadratic_nonneg f
    have hTotal : lowNormalRealSchwartzH3Energy f =
        1 + lowNormalRealSchwartzH3EnergyQuadratic f :=
      lowNormalRealSchwartzH3Energy_eq_one_add_quadratic f
    have hTotalNonneg : 0 ≤ lowNormalRealSchwartzH3Energy f := by
      rw [hTotal]
      linarith
    have hRight : 0 ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy f) *
          lowNormalRealSchwartzH3TopDissipation f :=
      mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) hD
    by_cases hM : 0 < lowNormalRealSchwartzPoint3Monomial f
    · have hThreshold := hShape f hM
      have hELe : lowNormalRealSchwartzH3EnergyQuadratic f ≤
          lowNormalRealSchwartzH3Energy f := by
        rw [hTotal]
        linarith
      have hExtended : (lowNormalRealSchwartzPoint3Monomial f) ^ 2 ≤
          C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
            lowNormalRealSchwartzH3Energy f := by
        calc
          _ ≤ C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
              lowNormalRealSchwartzH3EnergyQuadratic f := hThreshold
          _ ≤ C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
              lowNormalRealSchwartzH3Energy f :=
            mul_le_mul_of_nonneg_left hELe (by positivity)
      have hSquareRight :
          (C * Real.sqrt (lowNormalRealSchwartzH3Energy f) *
            lowNormalRealSchwartzH3TopDissipation f) ^ 2 =
          C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
            lowNormalRealSchwartzH3Energy f := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hTotalNonneg]
        ring
      have hSquared :
          (lowNormalRealSchwartzPoint3Monomial f) ^ 2 ≤
            (C * Real.sqrt (lowNormalRealSchwartzH3Energy f) *
              lowNormalRealSchwartzH3TopDissipation f) ^ 2 := by
        rw [hSquareRight]
        exact hExtended
      nlinarith
    · exact (le_of_not_gt hM).trans hRight

/-- Existence of ONE global endpoint coefficient is exactly existence of
ONE coefficient bounding the unnormalized positive-shape stress on all
real Schwartz profiles. Neither existence statement is asserted. -/
theorem lowNormalRealSchwartz_exists_uniformCriticalHalf_iff_shapeThreshold :
    (∃ C : ℝ, 0 ≤ C ∧
      ∀ f : A3 → SchwartzMap V3 ℝ,
        lowNormalRealSchwartzPoint3Monomial f ≤
          C * Real.sqrt (lowNormalRealSchwartzH3Energy f) *
            lowNormalRealSchwartzH3TopDissipation f) ↔
    (∃ C : ℝ, 0 ≤ C ∧
      ∀ f : A3 → SchwartzMap V3 ℝ,
        0 < lowNormalRealSchwartzPoint3Monomial f →
          (lowNormalRealSchwartzPoint3Monomial f) ^ 2 ≤
            C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
              lowNormalRealSchwartzH3EnergyQuadratic f) := by
  constructor
  · rintro ⟨C, hC, hBound⟩
    exact ⟨C, hC,
      (lowNormalRealSchwartz_uniformCriticalHalf_iff_positiveShapeThreshold
        C hC).mp hBound⟩
  · rintro ⟨C, hC, hBound⟩
    exact ⟨C, hC,
      (lowNormalRealSchwartz_uniformCriticalHalf_iff_positiveShapeThreshold
        C hC).mpr hBound⟩

/-- Signed excess of squared monomial over the homogeneous critical-half
budget. Its sign, rather than the profile's amplitude, detects a failure
of the shape criterion for a proposed coefficient. -/
noncomputable def lowNormalRealSchwartz_criticalHalfShapeExcess
    (C : ℝ) (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  (lowNormalRealSchwartzPoint3Monomial f) ^ 2 -
    C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
      lowNormalRealSchwartzH3EnergyQuadratic f

/-- Both sides of the positive-shape threshold have degree six under
real amplitude scaling. This is exact even when the amplitude is negative. -/
theorem lowNormalRealSchwartz_criticalHalfShapeExcess_real_smul
    (C a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartz_criticalHalfShapeExcess C
        (fun j : A3 => a • f j) =
      a ^ 6 * lowNormalRealSchwartz_criticalHalfShapeExcess C f := by
  unfold lowNormalRealSchwartz_criticalHalfShapeExcess
  rw [lowNormalRealSchwartzPoint3Monomial_real_smul,
    lowNormalRealSchwartzH3TopDissipation_real_smul,
    lowNormalRealSchwartzH3EnergyQuadratic_real_smul]
  ring

/-- A positive physical first monomial with positive shape excess is a
concrete obstruction to the proposed GLOBAL endpoint coefficient C.
This is conditional on finding such a witness, not a witness construction. -/
theorem lowNormalRealSchwartz_positiveShapeExcess_rulesOut_uniformCriticalHalf
    (C : ℝ) (hC : 0 ≤ C)
    (f : A3 → SchwartzMap V3 ℝ)
    (hM : 0 < lowNormalRealSchwartzPoint3Monomial f)
    (hExcess : 0 < lowNormalRealSchwartz_criticalHalfShapeExcess C f) :
    ¬ (∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartzPoint3Monomial g ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy g) *
          lowNormalRealSchwartzH3TopDissipation g) := by
  intro hGlobal
  have hThreshold :=
    ((lowNormalRealSchwartz_uniformCriticalHalf_iff_positiveShapeThreshold
      C hC).mp hGlobal) f hM
  change 0 < (lowNormalRealSchwartzPoint3Monomial f) ^ 2 -
    C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
      lowNormalRealSchwartzH3EnergyQuadratic f at hExcess
  have hStrict := sub_pos.mp hExcess
  exact (not_lt_of_ge hThreshold) hStrict

/-- Physical solenoidality for the exact canonical Point3 realization of a
real Schwartz velocity. This is the original three-coordinate divergence. -/
def lowNormalRealSchwartz_Point3Solenoidal
    (f : A3 → SchwartzMap V3 ℝ) : Prop :=
  ∀ x : Point3,
    ∑ j : A3, spatial3.d j (h3SchwartzPoint3Scalar (f j)) x = 0

/-- The physical divergence constraint is preserved by every real
velocity-amplitude rescaling. No Fourier constraint is substituted. -/
theorem lowNormalRealSchwartz_Point3Solenoidal_real_smul
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f) :
    lowNormalRealSchwartz_Point3Solenoidal (fun j : A3 => a • f j) := by
  intro x
  have hOriginal := hDiv x
  simp only [h3SchwartzPoint3Scalar_spatial_d,
    h3SchwartzPoint3Scalar] at hOriginal ⊢
  simp only [LineDeriv.lineDerivOp_smul, smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, hOriginal, mul_zero]

/-- The *solenoidal* global endpoint estimate is equivalent to a uniform
positive-shape stress threshold inside the actual physical divergence-free
Schwartz class. The necessity retains all positive amplitude rescalings
without leaving that class. -/
theorem lowNormalRealSchwartz_solenoidalUniformCriticalHalf_iff_shapeThreshold
    (C : ℝ) (hC : 0 ≤ C) :
    (∀ f : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal f →
      lowNormalRealSchwartzPoint3Monomial f ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy f) *
          lowNormalRealSchwartzH3TopDissipation f) ↔
    (∀ f : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal f →
      0 < lowNormalRealSchwartzPoint3Monomial f →
        (lowNormalRealSchwartzPoint3Monomial f) ^ 2 ≤
          C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
            lowNormalRealSchwartzH3EnergyQuadratic f) := by
  constructor
  · intro hUniform f hDiv hM
    have hE : 0 ≤ lowNormalRealSchwartzH3EnergyQuadratic f :=
      lowNormalRealSchwartzH3EnergyQuadratic_nonneg f
    have hD : 0 ≤ lowNormalRealSchwartzH3TopDissipation f :=
      lowNormalRealSchwartzH3TopDissipation_nonneg f
    have hB : 0 ≤ C * lowNormalRealSchwartzH3TopDissipation f :=
      mul_nonneg hC hD
    have hRay : ∀ a : ℝ, 0 < a →
        a ^ 3 * lowNormalRealSchwartzPoint3Monomial f ≤
          (C * lowNormalRealSchwartzH3TopDissipation f) *
            Real.sqrt (1 + a ^ 2 * lowNormalRealSchwartzH3EnergyQuadratic f) *
            a ^ 2 := by
      intro a ha
      have hAt := hUniform (fun j : A3 => a • f j)
        (lowNormalRealSchwartz_Point3Solenoidal_real_smul a f hDiv)
      rw [lowNormalRealSchwartzPoint3Monomial_real_smul,
        lowNormalRealSchwartzH3TopDissipation_real_smul,
        lowNormalRealSchwartzH3Energy_eq_one_add_quadratic,
        lowNormalRealSchwartzH3EnergyQuadratic_real_smul] at hAt
      calc
        a ^ 3 * lowNormalRealSchwartzPoint3Monomial f ≤
            C * Real.sqrt (1 + a ^ 2 * lowNormalRealSchwartzH3EnergyQuadratic f) *
              (a ^ 2 * lowNormalRealSchwartzH3TopDissipation f) := hAt
        _ = (C * lowNormalRealSchwartzH3TopDissipation f) *
              Real.sqrt (1 + a ^ 2 * lowNormalRealSchwartzH3EnergyQuadratic f) *
              a ^ 2 := by ring
    have hThreshold :=
      (criticalHalfEnergyRayBound_iff
        (lowNormalRealSchwartzPoint3Monomial f)
        (lowNormalRealSchwartzH3EnergyQuadratic f)
        (C * lowNormalRealSchwartzH3TopDissipation f)
        hM hE hB).mp hRay
    calc
      (lowNormalRealSchwartzPoint3Monomial f) ^ 2 ≤
          (C * lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
            lowNormalRealSchwartzH3EnergyQuadratic f := hThreshold
      _ = C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
            lowNormalRealSchwartzH3EnergyQuadratic f := by ring
  · intro hShape f hDiv
    have hD : 0 ≤ lowNormalRealSchwartzH3TopDissipation f :=
      lowNormalRealSchwartzH3TopDissipation_nonneg f
    have hE : 0 ≤ lowNormalRealSchwartzH3EnergyQuadratic f :=
      lowNormalRealSchwartzH3EnergyQuadratic_nonneg f
    have hTotal : lowNormalRealSchwartzH3Energy f =
        1 + lowNormalRealSchwartzH3EnergyQuadratic f :=
      lowNormalRealSchwartzH3Energy_eq_one_add_quadratic f
    have hTotalNonneg : 0 ≤ lowNormalRealSchwartzH3Energy f := by
      rw [hTotal]
      linarith
    have hRight : 0 ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy f) *
          lowNormalRealSchwartzH3TopDissipation f :=
      mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) hD
    by_cases hM : 0 < lowNormalRealSchwartzPoint3Monomial f
    · have hThreshold := hShape f hDiv hM
      have hELe : lowNormalRealSchwartzH3EnergyQuadratic f ≤
          lowNormalRealSchwartzH3Energy f := by
        rw [hTotal]
        linarith
      have hExtended : (lowNormalRealSchwartzPoint3Monomial f) ^ 2 ≤
          C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
            lowNormalRealSchwartzH3Energy f := by
        calc
          _ ≤ C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
              lowNormalRealSchwartzH3EnergyQuadratic f := hThreshold
          _ ≤ C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
              lowNormalRealSchwartzH3Energy f :=
            mul_le_mul_of_nonneg_left hELe (by positivity)
      have hSquareRight :
          (C * Real.sqrt (lowNormalRealSchwartzH3Energy f) *
            lowNormalRealSchwartzH3TopDissipation f) ^ 2 =
          C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2 *
            lowNormalRealSchwartzH3Energy f := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hTotalNonneg]
        ring
      have hSquared :
          (lowNormalRealSchwartzPoint3Monomial f) ^ 2 ≤
            (C * Real.sqrt (lowNormalRealSchwartzH3Energy f) *
              lowNormalRealSchwartzH3TopDissipation f) ^ 2 := by
        rw [hSquareRight]
        exact hExtended
      nlinarith
    · exact (le_of_not_gt hM).trans hRight

end
end PrimeTensor.FirstMonomialTriad
