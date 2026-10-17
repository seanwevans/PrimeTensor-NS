import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzHolderActualRoots244
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Actual Schwartz L² and L⁴ norm-to-integral roots for the 243 slots

The 243-slot real Hölder/energy theorem previously had exactly three
hypotheses, asserting that the extended-real L² and L⁴ seminorms of its
actual derivative jets were the real positive square/fourth roots of their
Bochner square/fourth-power integrals.

For Schwartz functions, `SchwartzMap.memLp` supplies integrability. The
existing `realLpEnorm`/`eLpNorm` identity and
`MemLp.eLpNorm_eq_integral_rpow_norm` then yield the real root formulas.
We instantiate these formulas on each actual derivative jet, eliminating
all three residual hypotheses of the 243-slot E₂ E₃⁵ theorem.

No incompressibility, Navier--Stokes path, conditional slot estimate,
new axiom, or critical-half endpoint estimate is assumed here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv ENNReal

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3
private abbrev SlotsNorm244 := A3 × (A3 × (A3 × (A3 × A3)))

noncomputable local instance axisFintypeHolderNormIdentities244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The project's raw `realLpEnorm` coincides with mathlib's `eLpNorm`
for any finite positive real exponent. Keeping this abstract avoids
repeating the lintegral-to-Lp conversion in the two root formulas. -/
private theorem schwartz_rawLp_eq_eLpNorm244
    (g : SchwartzMap V3 ℝ) (p : ℝ)
    (hp : 0 ≤ p)
    (hp0 : ENNReal.ofReal p ≠ 0)
    (hpTop : ENNReal.ofReal p ≠ ∞) :
    realLpEnorm volume p (g : V3 → ℝ) =
      eLpNorm (g : V3 → ℝ) (ENNReal.ofReal p) (volume : Measure V3) := by
  unfold realLpEnorm
  have hELp :=
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := ENNReal.ofReal p)
      (μ := (volume : Measure V3))
      (f := (g : V3 → ℝ)) hp0 hpTop
  symm
  simpa only [ENNReal.toReal_ofReal hp] using hELp

/-- An exact L² norm-to-integral identity on the physical Euclidean
Schwartz carrier, valid even when the integral vanishes. -/
theorem lowNormalSchwartz_realLpEnorm_two_eq_actualRoot244
    (g : SchwartzMap V3 ℝ) :
    realLpEnorm volume 2 (g : V3 → ℝ) =
      ENNReal.ofReal (Real.sqrt (∫ ξ : V3, (g ξ) ^ 2)) := by
  have hMem : MemLp (g : V3 → ℝ) (ENNReal.ofReal 2)
      (volume : Measure V3) :=
    g.memLp (ENNReal.ofReal 2) (volume : Measure V3)
  have hFormula :
      eLpNorm (g : V3 → ℝ) (ENNReal.ofReal 2) (volume : Measure V3) =
        ENNReal.ofReal
          ((∫ ξ : V3, ‖g ξ‖ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)) := by
    simpa only [show (ENNReal.ofReal (2 : ℝ)).toReal = (2 : ℝ) by norm_num] using
      (hMem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp))
  have hIntegral :
      (∫ ξ : V3, ‖g ξ‖ ^ (2 : ℝ)) =
        (∫ ξ : V3, (g ξ) ^ (2 : ℕ)) := by
    apply integral_congr_ae
    filter_upwards with ξ
    calc
      ‖g ξ‖ ^ (2 : ℝ) = ‖g ξ‖ ^ (2 : ℕ) :=
        Real.rpow_natCast (‖g ξ‖) 2
      _ = (g ξ) ^ 2 := by
        rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (sq_nonneg _)]
  calc
    realLpEnorm volume 2 (g : V3 → ℝ) =
        eLpNorm (g : V3 → ℝ) (ENNReal.ofReal 2) (volume : Measure V3) :=
      schwartz_rawLp_eq_eLpNorm244 g 2 (by norm_num) (by norm_num) (by simp)
    _ = ENNReal.ofReal
          ((∫ ξ : V3, ‖g ξ‖ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)) := hFormula
    _ = ENNReal.ofReal (Real.sqrt (∫ ξ : V3, (g ξ) ^ 2)) := by
      rw [hIntegral, Real.sqrt_eq_rpow]
      norm_num

/-- Square root of a square root is exactly the nonnegative real fourth
root. The nonnegativity hypothesis handles the zero-integral case. -/
private theorem sqrt_sqrt_eq_quarter_rpow244
    (x : ℝ) (hx : 0 ≤ x) :
    x ^ ((4 : ℝ)⁻¹) = Real.sqrt (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hx]
  norm_num

/-- An exact L⁴ norm-to-integral identity on the physical Euclidean
Schwartz carrier. There is no unspecified finite seminorm factor. -/
theorem lowNormalSchwartz_realLpEnorm_four_eq_actualRoot244
    (g : SchwartzMap V3 ℝ) :
    realLpEnorm volume 4 (g : V3 → ℝ) =
      ENNReal.ofReal (Real.sqrt (Real.sqrt (∫ ξ : V3, (g ξ) ^ 4))) := by
  have hMem : MemLp (g : V3 → ℝ) (ENNReal.ofReal 4)
      (volume : Measure V3) :=
    g.memLp (ENNReal.ofReal 4) (volume : Measure V3)
  have hFormula :
      eLpNorm (g : V3 → ℝ) (ENNReal.ofReal 4) (volume : Measure V3) =
        ENNReal.ofReal
          ((∫ ξ : V3, ‖g ξ‖ ^ (4 : ℝ)) ^ ((4 : ℝ)⁻¹)) := by
    simpa only [show (ENNReal.ofReal (4 : ℝ)).toReal = (4 : ℝ) by norm_num] using
      (hMem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp))
  have hIntegral :
      (∫ ξ : V3, ‖g ξ‖ ^ (4 : ℝ)) =
        (∫ ξ : V3, (g ξ) ^ (4 : ℕ)) := by
    apply integral_congr_ae
    filter_upwards with ξ
    calc
      ‖g ξ‖ ^ (4 : ℝ) = ‖g ξ‖ ^ (4 : ℕ) :=
        Real.rpow_natCast (‖g ξ‖) 4
      _ = |(g ξ) ^ 4| := by
        rw [Real.norm_eq_abs, ← abs_pow]
      _ = (g ξ) ^ 4 := abs_of_nonneg (by positivity)
  have hIntegralNonneg : 0 ≤ (∫ ξ : V3, (g ξ) ^ 4) :=
    integral_nonneg (fun ξ => by positivity)
  calc
    realLpEnorm volume 4 (g : V3 → ℝ) =
        eLpNorm (g : V3 → ℝ) (ENNReal.ofReal 4) (volume : Measure V3) :=
      schwartz_rawLp_eq_eLpNorm244 g 4 (by norm_num) (by norm_num) (by simp)
    _ = ENNReal.ofReal
          ((∫ ξ : V3, ‖g ξ‖ ^ (4 : ℝ)) ^ ((4 : ℝ)⁻¹)) := hFormula
    _ = ENNReal.ofReal (Real.sqrt (Real.sqrt (∫ ξ : V3, (g ξ) ^ 4))) := by
      rw [hIntegral, sqrt_sqrt_eq_quarter_rpow244 _ hIntegralNonneg]

/-- The actual third-, middle-, and cross-jet norm hypotheses of the
previously conditional theorem are all consequences of Schwartz `MemLp`. -/
theorem lowNormalRealSchwartz_firstMonomial_holder244_energyGN_unconditional
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzPoint3Monomial f) ^ 4 ≤
      (16 : ℝ) * (Fintype.card A3 : ℝ) ^ 9 *
        lowNormalSecondJetSobolevRealConstant ^ 6 *
          (lowNormalRealSchwartzH3Energy2 f *
            (lowNormalRealSchwartzH3Energy3 f) ^ 5) := by
  refine lowNormalRealSchwartz_firstMonomial_holder244_energyGN_of_normIdentities
    f ?_ ?_ ?_
  · intro p
    exact lowNormalSchwartz_realLpEnorm_two_eq_actualRoot244
      (∂_{h3FourierAxisDirection p.1}
        (∂_{h3FourierAxisDirection p.2.1}
          (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.2))))
  · intro p
    exact lowNormalSchwartz_realLpEnorm_four_eq_actualRoot244
      (∂_{h3FourierAxisDirection p.2.1}
        (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.1)))
  · intro p
    exact lowNormalSchwartz_realLpEnorm_four_eq_actualRoot244
      (∂_{h3FourierAxisDirection p.1}
        (∂_{h3FourierAxisDirection p.2.2.2.1} (f p.2.2.2.2)))

end
end PrimeTensor.FirstMonomialTriad
