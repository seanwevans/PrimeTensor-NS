import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3LerayTransverseConstraint
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Tactic

/-!
# Longitudinal heat rigidity of the full infinite Fourier Leray equation

The exact ordered Leray source is perpendicular to each output frequency.
We use the *real* time derivative of a complex Fourier coefficient, apply
its complex-linear frequency pairing (restricted to real scalars), and obtain
the homogeneous scalar heat ODE. Gronwall with zero initial longitudinal
component then proves persistence of solenoidality on the closed local
interval, including the initial endpoint.

The final theorem works for any coefficientwise differentiable Fourier flow
satisfying the exact projected equation, with high analytic Wiener bounds.
It does not silently derive this differentiability from the previously
constructed integral solution: passage from that integral identity to
classical derivatives (requiring source continuity) is the remaining bridge.
No global-in-time or real-space continuation claim is made.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev LHIndex244 := thirdFullThreeBandZ3Index244
private abbrev LHBand244 := EuclideanSpace ℂ (Fin 3)

/-- The general homogeneous scalar heat equation with zero initial data
has no nonzero solution, even if only right derivatives are controlled at
the left endpoint. Gronwall does not require a strictly positive viscosity. -/
theorem thirdFullThreeBand_z3LongitudinalHeat_scalarRigidity244
    (a b lambda : ℝ) (hlambda : 0 ≤ lambda)
    (w : ℝ → ℂ)
    (hCont : ContinuousOn w (Icc a b))
    (hInitial : w a = 0)
    (hDeriv : ∀ t ∈ Ico a b,
      HasDerivAt w ((-lambda) • w t) t) :
    ∀ t ∈ Icc a b, w t = 0 := by
  have hRight : ∀ t ∈ Ico a b,
      HasDerivWithinAt w ((-lambda) • w t) (Ici t) t := by
    intro t ht
    exact (hDeriv t ht).hasDerivWithinAt
  have hNorm (t : ℝ) :
      ‖(-lambda) • w t‖ ≤ lambda * ‖w t‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hlambda]
  exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hCont hRight hInitial (fun t ht => hNorm t)

/-- Applying the genuinely complex Fourier pairing to the exact vector
Navier--Stokes derivative produces the homogeneous longitudinal heat
ODE. The complex-linear functional is restricted to real scalars because
time is real, not complex. -/
theorem thirdFullThreeBand_z3LongitudinalHeat_scalarDerivative244
    (mu : ℝ) (g : ℝ → LHIndex244 → LHBand244)
    (t : ℝ) (n : LHIndex244)
    (hODE : HasDerivAt (fun r : ℝ => g r n)
      ((-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
        g t n + thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n) t)
    (hTransverse : thirdFullThreeBandZ3FourierIsTransverse244 n
      (thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n)) :
    HasDerivAt
      (fun r : ℝ => inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 n) (g r n))
      ((-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
        inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 n) (g t n)) t := by
  let xi := thirdFullThreeBandZ3ComplexFrequency244 n
  let lambda : ℝ := mu * ‖xi‖ ^ 2
  let L : LHBand244 →L[ℝ] ℂ := ((innerSL ℂ) xi).restrictScalars ℝ
  have hPair : HasFDerivAt (fun v : LHBand244 => L v) L (g t n) :=
    L.hasFDerivAt
  have hComp := hPair.comp_hasDerivAt t hODE
  have hSource : L (thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n) = 0 := by
    change inner ℂ xi (thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n) = 0
    exact hTransverse
  have hDerivative : L
      ((-lambda) • g t n + thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n) =
      (-lambda) • L (g t n) := by
    rw [map_add, map_smul, hSource, add_zero]
  change HasDerivAt (fun r : ℝ => L (g r n))
    (L ((-lambda) • g t n +
      thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n)) t at hComp
  rw [hDerivative] at hComp
  exact hComp

/-- For a classical coefficientwise solution, the analytic bound implies
that the *actual infinite ordered* nonlinear source is transverse at every
time; hence no nonlinear longitudinal term survives in the scalar ODE. -/
theorem thirdFullThreeBand_z3LongitudinalHeat_projectedDerivative244
    (mu a b : ℝ)
    (g : ℝ → LHIndex244 → LHBand244)
    (hHigh : ∀ t ∈ Icc a b,
      Summable (fun n : LHIndex244 =>
        thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n * ‖g t n‖) ∧
      thirdFullThreeBandZ3InfiniteWienerMass244
        (Real.log (9 / 5 : ℝ)) (g t) ≤ 100)
    (hODE : ∀ t ∈ Ico a b, ∀ n : LHIndex244,
      HasDerivAt (fun r : ℝ => g r n)
        ((-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
          g t n + thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n) t) :
    ∀ t ∈ Ico a b, ∀ n : LHIndex244,
      HasDerivAt
        (fun r : ℝ => inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 n) (g r n))
        ((-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
          inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 n) (g t n)) t := by
  intro t ht n
  have hSource := thirdFullThreeBand_z3InfiniteOrderedLeray_transverse_of_mass244
    (g t) (hHigh t ⟨ht.1, ht.2.le⟩).1
    (hHigh t ⟨ht.1, ht.2.le⟩).2 n
  exact thirdFullThreeBand_z3LongitudinalHeat_scalarDerivative244
    mu g t n (hODE t ht n) hSource

/-- SOLENOIDAL RIGIDITY: an exact, coefficientwise differentiable complex
Fourier NS solution with the constructed 9/5 analytic bound preserves the
zero-longitudinal constraint for the entire common interval.

This is the nonlinear-to-linear reduction plus Gronwall, not a premise that
the solution remains transverse. The remaining bridge for the previously
constructed *integral* solution is differentiability of its source. -/
theorem thirdFullThreeBand_z3LongitudinalHeat_solenoidalRigidity244
    (mu a b : ℝ) (hmu : 0 ≤ mu)
    (g : ℝ → LHIndex244 → LHBand244)
    (hCont : ∀ n : LHIndex244,
      ContinuousOn (fun t : ℝ => g t n) (Icc a b))
    (hHigh : ∀ t ∈ Icc a b,
      Summable (fun n : LHIndex244 =>
        thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n * ‖g t n‖) ∧
      thirdFullThreeBandZ3InfiniteWienerMass244
        (Real.log (9 / 5 : ℝ)) (g t) ≤ 100)
    (hInitial : ∀ n : LHIndex244,
      thirdFullThreeBandZ3FourierIsTransverse244 n (g a n))
    (hODE : ∀ t ∈ Ico a b, ∀ n : LHIndex244,
      HasDerivAt (fun r : ℝ => g r n)
        ((-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
          g t n + thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n) t) :
    ∀ t ∈ Icc a b, ∀ n : LHIndex244,
      thirdFullThreeBandZ3FourierIsTransverse244 n (g t n) := by
  intro t ht n
  let w : ℝ → ℂ := fun r =>
    inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 n) (g r n)
  have hContW : ContinuousOn w (Icc a b) :=
    (((innerSL ℂ) (thirdFullThreeBandZ3ComplexFrequency244 n)).continuous).comp_continuousOn
      (hCont n)
  have hLam : 0 ≤ mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 :=
    mul_nonneg hmu (sq_nonneg _)
  have hDerivW : ∀ r ∈ Ico a b,
      HasDerivAt w
        ((-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) • w r) r := by
    intro r hr
    exact thirdFullThreeBand_z3LongitudinalHeat_projectedDerivative244
      mu a b g hHigh hODE r hr n
  exact thirdFullThreeBand_z3LongitudinalHeat_scalarRigidity244
    a b (mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)
    hLam w hContW (hInitial n) hDerivW t ht

end
end PrimeTensor.FirstMonomialTriad
