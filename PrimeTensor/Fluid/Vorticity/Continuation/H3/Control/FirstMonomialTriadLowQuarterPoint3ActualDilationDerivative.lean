import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3CriticalHalfDilationScalar
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Real Schwartz-space dilation and exact derivative scaling

This module starts the transport of the scalar critical-half dilation
calculation to the actual real Schwartz carrier used by the physical H3
first monomial. For each strictly positive spatial scale, a continuous
linear equivalence realizes `x ↦ scale • x`. Precomposition preserves
Schwartz regularity. All directional derivatives through order four
then have their exact expected powers of `scale`.

No change-of-variables formula for integrals is asserted here. Those
identities, and the physical 243-slot monomial scaling, are separate steps.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean
open scoped LineDeriv SchwartzMap

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeQuarterActualDilation (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The real spatial isotropic dilation as a continuous linear equivalence.
Strict positivity also makes this an orientation-preserving invertible map. -/
noncomputable def lowNormalSchwartzDilationEquiv
    (scale : ℝ) (hscale : 0 < scale) : V3 ≃L[ℝ] V3 :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 scale hscale.ne')

@[simp] theorem lowNormalSchwartzDilationEquiv_apply
    (scale : ℝ) (hscale : 0 < scale) (x : V3) :
    lowNormalSchwartzDilationEquiv scale hscale x = scale • x := rfl

/-- Pullback of a real Schwartz component by positive isotropic dilation.
Unlike merely composing raw functions, this definition constructs a true
`SchwartzMap` and retains every regularity/decay guarantee. -/
noncomputable def lowNormalSchwartzDilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : SchwartzMap V3 ℝ) : SchwartzMap V3 ℝ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (lowNormalSchwartzDilationEquiv scale hscale) f

@[simp] theorem lowNormalSchwartzDilation_apply
    (scale : ℝ) (hscale : 0 < scale)
    (f : SchwartzMap V3 ℝ) (x : V3) :
    lowNormalSchwartzDilation scale hscale f x = f (scale • x) := by
  change f (lowNormalSchwartzDilationEquiv scale hscale x) = _
  rw [lowNormalSchwartzDilationEquiv_apply]

/-- The first derivative acquires exactly one power of the dilation. -/
theorem lowNormalSchwartzDilation_lineDeriv
    (scale : ℝ) (hscale : 0 < scale)
    (m : V3) (f : SchwartzMap V3 ℝ) :
    ∂_{m} (lowNormalSchwartzDilation scale hscale f) =
      scale • lowNormalSchwartzDilation scale hscale (∂_{m} f) := by
  change
    ∂_{m} (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (lowNormalSchwartzDilationEquiv scale hscale) f) =
      scale • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
        (lowNormalSchwartzDilationEquiv scale hscale) (∂_{m} f)
  rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
  rw [lowNormalSchwartzDilationEquiv_apply]
  rw [LineDeriv.lineDerivOp_left_smul]
  exact map_smul
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (lowNormalSchwartzDilationEquiv scale hscale)) scale (∂_{m} f)

/-- Two successive derivatives acquire two powers of the scale. -/
theorem lowNormalSchwartzDilation_twoLineDerivs
    (scale : ℝ) (hscale : 0 < scale)
    (m n : V3) (f : SchwartzMap V3 ℝ) :
    ∂_{m} (∂_{n} (lowNormalSchwartzDilation scale hscale f)) =
      scale ^ 2 • lowNormalSchwartzDilation scale hscale
        (∂_{m} (∂_{n} f)) := by
  calc
    _ = ∂_{m} (scale • lowNormalSchwartzDilation scale hscale (∂_{n} f)) := by
      rw [lowNormalSchwartzDilation_lineDeriv]
    _ = scale • (∂_{m} (lowNormalSchwartzDilation scale hscale (∂_{n} f))) := by
      rw [LineDeriv.lineDerivOp_smul]
    _ = scale • (scale • lowNormalSchwartzDilation scale hscale
          (∂_{m} (∂_{n} f))) := by
      rw [lowNormalSchwartzDilation_lineDeriv]
    _ = scale ^ 2 • lowNormalSchwartzDilation scale hscale
          (∂_{m} (∂_{n} f)) := by
      rw [smul_smul, pow_two]

/-- Three successive derivatives acquire three powers of the scale. -/
theorem lowNormalSchwartzDilation_threeLineDerivs
    (scale : ℝ) (hscale : 0 < scale)
    (m n p : V3) (f : SchwartzMap V3 ℝ) :
    ∂_{m} (∂_{n} (∂_{p} (lowNormalSchwartzDilation scale hscale f))) =
      scale ^ 3 • lowNormalSchwartzDilation scale hscale
        (∂_{m} (∂_{n} (∂_{p} f))) := by
  calc
    _ = ∂_{m} (scale ^ 2 • lowNormalSchwartzDilation scale hscale
        (∂_{n} (∂_{p} f))) := by
      rw [lowNormalSchwartzDilation_twoLineDerivs]
    _ = scale ^ 2 • ∂_{m} (lowNormalSchwartzDilation scale hscale
        (∂_{n} (∂_{p} f))) := by
      rw [LineDeriv.lineDerivOp_smul]
    _ = scale ^ 2 • (scale • lowNormalSchwartzDilation scale hscale
        (∂_{m} (∂_{n} (∂_{p} f)))) := by
      rw [lowNormalSchwartzDilation_lineDeriv]
    _ = scale ^ 3 • lowNormalSchwartzDilation scale hscale
        (∂_{m} (∂_{n} (∂_{p} f))) := by
      rw [smul_smul]
      congr 1

/-- Fourth derivatives carry exactly four powers: the derivative order
occurring in the top H3 dissipation budget. -/
theorem lowNormalSchwartzDilation_fourLineDerivs
    (scale : ℝ) (hscale : 0 < scale)
    (m n p q : V3) (f : SchwartzMap V3 ℝ) :
    ∂_{m} (∂_{n} (∂_{p} (∂_{q}
      (lowNormalSchwartzDilation scale hscale f)))) =
      scale ^ 4 • lowNormalSchwartzDilation scale hscale
        (∂_{m} (∂_{n} (∂_{p} (∂_{q} f)))) := by
  calc
    _ = ∂_{m} (scale ^ 3 • lowNormalSchwartzDilation scale hscale
        (∂_{n} (∂_{p} (∂_{q} f)))) := by
      rw [lowNormalSchwartzDilation_threeLineDerivs]
    _ = scale ^ 3 • ∂_{m} (lowNormalSchwartzDilation scale hscale
        (∂_{n} (∂_{p} (∂_{q} f)))) := by
      rw [LineDeriv.lineDerivOp_smul]
    _ = scale ^ 3 • (scale • lowNormalSchwartzDilation scale hscale
        (∂_{m} (∂_{n} (∂_{p} (∂_{q} f))))) := by
      rw [lowNormalSchwartzDilation_lineDeriv]
    _ = scale ^ 4 • lowNormalSchwartzDilation scale hscale
        (∂_{m} (∂_{n} (∂_{p} (∂_{q} f)))) := by
      rw [smul_smul]
      congr 1

/-- Apply the same true Schwartz dilation independently to all three
velocity components without selecting or removing any component. -/
noncomputable def lowNormalSchwartzVelocityDilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) : A3 → SchwartzMap V3 ℝ :=
  fun j => lowNormalSchwartzDilation scale hscale (f j)

@[simp] theorem lowNormalSchwartzVelocityDilation_apply
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) (j : A3) (x : V3) :
    lowNormalSchwartzVelocityDilation scale hscale f j x =
      f j (scale • x) :=
  lowNormalSchwartzDilation_apply scale hscale (f j) x

end
end PrimeTensor.FirstMonomialTriad
