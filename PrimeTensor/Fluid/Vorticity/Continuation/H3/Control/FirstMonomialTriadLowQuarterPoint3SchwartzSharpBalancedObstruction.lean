import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzSharpAdjacentCauchy

/-!
# Unconditional sharp balanced-shape obstruction for the signed first monomial

The coefficient-one Schwartz adjacent-energy inequalities are now theorems,
not interpolation hypotheses.  They remove the final analytic assumptions
from the earlier balanced-scale necessary condition for a uniform solenoidal
critical-half estimate.

At a positive scale with `scale^6 * E3 = E0`, a proposed uniform coefficient
`C` forces the twelfth-power shape inequality

  M^12 <= (2*C)^12 * D^12 * E0^5 * E3.

The factor 2 is the square root of the exact four-block factor 4.  This
file also gives a genuinely SIGNED obstruction: if this polynomial shape
excess is strictly positive for any solenoidal Schwartz profile, with
positive E0 and an actual balanced scale, it rules out the proposed
uniform coefficient.  There is no need to assume M > 0: negating the
velocity switches the cubic signed monomial while leaving the degree-36
balanced excess unchanged.

This is a necessary-condition and conditional-obstruction result.  It does
not manufacture an obstructing profile or prove a universal coefficient.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSharpBalancedObstruction (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Sharp, unconditional necessary balanced-shape inequality for the actual
solenoidal 243-slot signed first monomial.  The former cubic interpolation
hypotheses are discharged by the coefficient-one Schwartz theorems. -/
theorem lowNormalRealSchwartz_solenoidalSharpBalancedShape_necessary
    (C scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hM : 0 < lowNormalRealSchwartzPoint3Monomial f)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hBalance : scale ^ 6 * lowNormalRealSchwartzH3Energy3 f =
      lowNormalRealSchwartzH3Energy0 f)
    (hShape : ∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g →
      0 < lowNormalRealSchwartzPoint3Monomial g →
      (lowNormalRealSchwartzPoint3Monomial g) ^ 2 ≤
        C ^ 2 * (lowNormalRealSchwartzH3TopDissipation g) ^ 2 *
          lowNormalRealSchwartzH3EnergyQuadratic g) :
    (lowNormalRealSchwartzPoint3Monomial f) ^ 12 ≤
      (2 * C) ^ 12 * (lowNormalRealSchwartzH3TopDissipation f) ^ 12 *
      (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
      lowNormalRealSchwartzH3Energy3 f := by
  obtain ⟨hOne, hTwo⟩ :=
    lowNormalRealSchwartzH3Energy_sharp_cubicLogConvex f
  have hNecessary := lowNormalRealSchwartz_solenoidalBalancedShape_necessary
    C scale hscale f hDiv hM hE0 hOne hTwo hBalance hShape
  calc
    (lowNormalRealSchwartzPoint3Monomial f) ^ 12 ≤
        (4 * C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2) ^ 6 *
          (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
          lowNormalRealSchwartzH3Energy3 f := hNecessary
    _ = (2 * C) ^ 12 * (lowNormalRealSchwartzH3TopDissipation f) ^ 12 *
          (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
          lowNormalRealSchwartzH3Energy3 f := by ring

/-- The scale-free homogeneous shape criterion forces nonpositive
balanced excess at the effective coefficient `2*C`. -/
theorem lowNormalRealSchwartz_solenoidalSharpBalancedExcess_nonpos
    (C scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hM : 0 < lowNormalRealSchwartzPoint3Monomial f)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hBalance : scale ^ 6 * lowNormalRealSchwartzH3Energy3 f =
      lowNormalRealSchwartzH3Energy0 f)
    (hShape : ∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g →
      0 < lowNormalRealSchwartzPoint3Monomial g →
      (lowNormalRealSchwartzPoint3Monomial g) ^ 2 ≤
        C ^ 2 * (lowNormalRealSchwartzH3TopDissipation g) ^ 2 *
          lowNormalRealSchwartzH3EnergyQuadratic g) :
    lowNormalRealSchwartz_criticalHalfBalancedExcess (2 * C) f ≤ 0 := by
  have hNecessary := lowNormalRealSchwartz_solenoidalSharpBalancedShape_necessary
    C scale hscale f hDiv hM hE0 hBalance hShape
  unfold lowNormalRealSchwartz_criticalHalfBalancedExcess
  exact sub_nonpos.mpr hNecessary

/-- A positive signed first monomial with strictly positive sharp balanced
excess rules out this global solenoidal critical-half coefficient. -/
theorem lowNormalRealSchwartz_positiveSharpBalancedExcess_rulesOut_uniform
    (C : ℝ) (hC : 0 ≤ C)
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hM : 0 < lowNormalRealSchwartzPoint3Monomial f)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hBalance : scale ^ 6 * lowNormalRealSchwartzH3Energy3 f =
      lowNormalRealSchwartzH3Energy0 f)
    (hExcess : 0 < lowNormalRealSchwartz_criticalHalfBalancedExcess
      (2 * C) f) :
    ¬ (∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g →
      lowNormalRealSchwartzPoint3Monomial g ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy g) *
          lowNormalRealSchwartzH3TopDissipation g) := by
  intro hUniform
  have hShape :=
    (lowNormalRealSchwartz_solenoidalUniformCriticalHalf_iff_shapeThreshold
      C hC).mp hUniform
  have hNonpos := lowNormalRealSchwartz_solenoidalSharpBalancedExcess_nonpos
    C scale hscale f hDiv hM hE0 hBalance hShape
  exact (not_lt_of_ge hNonpos) hExcess

/-- Reversing the velocity changes the sign of the cubic physical monomial,
but not the twelfth-power balanced shape excess or its balancing condition.
Thus a negative-monomial witness also rules out the proposed coefficient. -/
theorem lowNormalRealSchwartz_negativeSharpBalancedExcess_rulesOut_uniform
    (C : ℝ) (hC : 0 ≤ C)
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hM : lowNormalRealSchwartzPoint3Monomial f < 0)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hBalance : scale ^ 6 * lowNormalRealSchwartzH3Energy3 f =
      lowNormalRealSchwartzH3Energy0 f)
    (hExcess : 0 < lowNormalRealSchwartz_criticalHalfBalancedExcess
      (2 * C) f) :
    ¬ (∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g →
      lowNormalRealSchwartzPoint3Monomial g ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy g) *
          lowNormalRealSchwartzH3TopDissipation g) := by
  let g : A3 → SchwartzMap V3 ℝ := fun j => (-1 : ℝ) • f j
  have hDivg : lowNormalRealSchwartz_Point3Solenoidal g :=
    lowNormalRealSchwartz_Point3Solenoidal_real_smul (-1) f hDiv
  have hMg : 0 < lowNormalRealSchwartzPoint3Monomial g := by
    change 0 < lowNormalRealSchwartzPoint3Monomial
      (fun j : A3 => (-1 : ℝ) • f j)
    rw [lowNormalRealSchwartzPoint3Monomial_real_smul]
    have hPow : (-1 : ℝ) ^ 3 = -1 := by norm_num
    rw [hPow, neg_one_mul]
    exact neg_pos.mpr hM
  -- Rewrite the exact amplitude laws BEFORE simplifying scalar (-1).  A broad
  -- `simp [g]` normalizes `(-1) • f j` to `-f j` too early and then the
  -- amplitude-scaling theorems no longer match syntactically.
  have hE0g_eq : lowNormalRealSchwartzH3Energy0 g =
      lowNormalRealSchwartzH3Energy0 f := by
    change lowNormalRealSchwartzH3Energy0
      (fun j : A3 => (-1 : ℝ) • f j) = _
    rw [lowNormalRealSchwartzH3Energy0_real_smul]
    norm_num
  have hE3g_eq : lowNormalRealSchwartzH3Energy3 g =
      lowNormalRealSchwartzH3Energy3 f := by
    change lowNormalRealSchwartzH3Energy3
      (fun j : A3 => (-1 : ℝ) • f j) = _
    rw [lowNormalRealSchwartzH3Energy3_real_smul]
    norm_num
  have hExcessg_eq : lowNormalRealSchwartz_criticalHalfBalancedExcess
      (2 * C) g = lowNormalRealSchwartz_criticalHalfBalancedExcess (2 * C) f := by
    change lowNormalRealSchwartz_criticalHalfBalancedExcess
      (2 * C) (fun j : A3 => (-1 : ℝ) • f j) = _
    rw [lowNormalRealSchwartz_criticalHalfBalancedExcess_real_smul]
    norm_num
  have hE0g : 0 < lowNormalRealSchwartzH3Energy0 g := by
    rw [hE0g_eq]
    exact hE0
  have hBalanceg : scale ^ 6 * lowNormalRealSchwartzH3Energy3 g =
      lowNormalRealSchwartzH3Energy0 g := by
    rw [hE3g_eq, hE0g_eq]
    exact hBalance
  have hExcessg : 0 < lowNormalRealSchwartz_criticalHalfBalancedExcess
      (2 * C) g := by
    rw [hExcessg_eq]
    exact hExcess
  exact lowNormalRealSchwartz_positiveSharpBalancedExcess_rulesOut_uniform
    C hC scale hscale g hDivg hMg hE0g hBalanceg hExcessg

/-- Sign-free obstruction. Strict polynomial excess itself implies the
signed monomial is nonzero; either it or its negated Schwartz velocity is
then a positive-monomial counterexample to the proposed uniform constant.
The existence of a strict-excess witness is NOT asserted. -/
theorem lowNormalRealSchwartz_sharpBalancedExcess_rulesOut_uniform
    (C : ℝ) (hC : 0 ≤ C)
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hBalance : scale ^ 6 * lowNormalRealSchwartzH3Energy3 f =
      lowNormalRealSchwartzH3Energy0 f)
    (hExcess : 0 < lowNormalRealSchwartz_criticalHalfBalancedExcess
      (2 * C) f) :
    ¬ (∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g →
      lowNormalRealSchwartzPoint3Monomial g ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy g) *
          lowNormalRealSchwartzH3TopDissipation g) := by
  let M : ℝ := lowNormalRealSchwartzPoint3Monomial f
  let Q : ℝ := (2 * C) ^ 12 *
    (lowNormalRealSchwartzH3TopDissipation f) ^ 12 *
    (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
    lowNormalRealSchwartzH3Energy3 f
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    have hE3 := lowNormalRealSchwartzH3Energy3_nonneg f
    positivity
  have hStrict : Q < M ^ 12 := by
    have h := hExcess
    change 0 < M ^ 12 - Q at h
    exact sub_pos.mp h
  have hMpower : 0 < M ^ 12 := lt_of_le_of_lt hQ hStrict
  rcases lt_trichotomy M 0 with hNeg | hZero | hPos
  · exact lowNormalRealSchwartz_negativeSharpBalancedExcess_rulesOut_uniform
      C hC scale hscale f hDiv hNeg hE0 hBalance hExcess
  · exfalso
    have hFalse : (0 : ℝ) < 0 := by simpa [hZero] using hMpower
    exact (lt_irrefl (0 : ℝ)) hFalse
  · exact lowNormalRealSchwartz_positiveSharpBalancedExcess_rulesOut_uniform
      C hC scale hscale f hDiv hPos hE0 hBalance hExcess

end
end PrimeTensor.FirstMonomialTriad
