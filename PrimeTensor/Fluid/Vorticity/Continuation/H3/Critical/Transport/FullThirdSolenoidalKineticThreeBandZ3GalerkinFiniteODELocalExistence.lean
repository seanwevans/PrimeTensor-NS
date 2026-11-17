import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinMovingBallPersistence
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# Actual finite Z³ Galerkin coefficient ODE: local existence

This is a fresh reconstruction, independent of the discarded FiniteODEFlow
attempt. Its state space is the finite subtype `{n // n ∈ s}`, NOT the
unbounded Fourier function space. The vector field is the complete projected
complex Leray convolution already defined and audited upstream.

The mathematical obstruction addressed here is finite-dimensional local
existence. This does NOT yet give the common cutoff-independent interval:
that requires a blow-up alternative plus the proved moving-ball barrier.

No sorry, axiom or assumed solution curve occurs in this module. The key
smoothness proof is intentionally explicit and subject to Lean verification.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev LocalODEIndex244 := thirdFullThreeBandZ3Index244
private abbrev LocalODEBand244 := EuclideanSpace ℂ (Fin 3)

/-- A genuine finite dimensional complex Fourier coefficient space. -/
abbrev thirdFullThreeBandZ3GalerkinFiniteState244
    (s : Finset LocalODEIndex244) :=
  {n : LocalODEIndex244 // n ∈ s} → LocalODEBand244

/-- Extend retained finite coefficients by zero away from the cutoff. -/
def thirdFullThreeBandZ3GalerkinFiniteExtend244
    (s : Finset LocalODEIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (n : LocalODEIndex244) : LocalODEBand244 :=
  if hn : n ∈ s then x ⟨n, hn⟩ else 0

theorem thirdFullThreeBand_z3GalerkinFiniteExtend_on244
    (s : Finset LocalODEIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (n : LocalODEIndex244) (hn : n ∈ s) :
    thirdFullThreeBandZ3GalerkinFiniteExtend244 s x n = x ⟨n, hn⟩ := by
  simp [thirdFullThreeBandZ3GalerkinFiniteExtend244, hn]

theorem thirdFullThreeBand_z3GalerkinFiniteExtend_off244
    (s : Finset LocalODEIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (n : LocalODEIndex244) (hn : n ∉ s) :
    thirdFullThreeBandZ3GalerkinFiniteExtend244 s x n = 0 := by
  simp [thirdFullThreeBandZ3GalerkinFiniteExtend244, hn]

/-- The ACTUAL Galerkin vector field, restricted to retained frequencies.
No six-mode closure and no artificial scalar surrogate. -/
def thirdFullThreeBandZ3GalerkinFiniteField244
    (mu : ℝ) (s : Finset LocalODEIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s) :
    thirdFullThreeBandZ3GalerkinFiniteState244 s :=
  fun n =>
    thirdFullThreeBandZ3GalerkinNSField244 mu s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) n.1

/-- The zero-extension of finite coefficients is a C¹ function of the
finite state. The membership condition is fixed while x varies: this
proof splits it *before* invoking fun_prop. -/
theorem thirdFullThreeBand_z3GalerkinFiniteExtend_contDiff244
    (s : Finset LocalODEIndex244) (n : LocalODEIndex244) :
    ContDiff ℝ 1 (fun x : thirdFullThreeBandZ3GalerkinFiniteState244 s =>
      thirdFullThreeBandZ3GalerkinFiniteExtend244 s x n) := by
  classical
  by_cases hn : n ∈ s
  · simp only [thirdFullThreeBandZ3GalerkinFiniteExtend244, dif_pos hn]
    fun_prop
  · simp only [thirdFullThreeBandZ3GalerkinFiniteExtend244, dif_neg hn]
    fun_prop

attribute [fun_prop] thirdFullThreeBand_z3GalerkinFiniteExtend_contDiff244

/-- Every coefficient of the actual finite Leray field is real-C¹.
The two convolution sums are finite, and the collision test `p + q = n`
is fixed while the state varies. We therefore split it *before*
using the differentiability rules. -/
theorem thirdFullThreeBand_z3GalerkinFiniteField_coord_contDiff244
    (mu : ℝ) (s : Finset LocalODEIndex244)
    (n : {n : LocalODEIndex244 // n ∈ s}) :
    ContDiff ℝ 1 (fun x : thirdFullThreeBandZ3GalerkinFiniteState244 s =>
      thirdFullThreeBandZ3GalerkinFiniteField244 mu s x n) := by
  classical
  let E := thirdFullThreeBandZ3GalerkinFiniteState244 s
  let U : E → LocalODEIndex244 → LocalODEBand244 :=
    thirdFullThreeBandZ3GalerkinFiniteExtend244 s
  have hU (p : LocalODEIndex244) :
      ContDiff ℝ 1 (fun x : E => U x p) :=
    thirdFullThreeBand_z3GalerkinFiniteExtend_contDiff244 s p
  have hVisc : ContDiff ℝ 1 (fun x : E =>
      (-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n.1‖ ^ 2)) • U x n.1) :=
    (hU n.1).const_smul _
  have hProj : ContDiff ℝ 1 (fun v : LocalODEBand244 =>
      thirdFullThreeBandZ3ComplexLeray244 n.1 v) :=
    ((thirdFullThreeBandZ3ComplexLeray244 n.1).restrictScalars ℝ).contDiff
  have hSource : ContDiff ℝ 1 (fun x : E =>
      ∑ p ∈ s, ∑ q ∈ s,
        if p + q = n.1 then
          thirdFullThreeBandZ3ComplexTransport244 n.1 q (U x p) (U x q)
        else 0) := by
    apply ContDiff.sum
    intro p hp
    apply ContDiff.sum
    intro q hq
    by_cases h : p + q = n.1
    · simp only [if_pos h]
      have hInner : ContDiff ℝ 1 (fun x : E =>
          inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 q) (U x p)) :=
        (contDiff_const.inner ℂ (hU p))
      have hScalar : ContDiff ℝ 1 (fun x : E =>
          -Complex.I * inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 q) (U x p)) :=
        contDiff_const.mul hInner
      have hSmul : ContDiff ℝ 1 (fun x : E =>
          (-Complex.I * inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 q) (U x p)) • U x q) :=
        hScalar.smul (hU q)
      change ContDiff ℝ 1 (fun x : E =>
        thirdFullThreeBandZ3ComplexLeray244 n.1
          ((-Complex.I * inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 q) (U x p)) • U x q))
      exact hProj.comp hSmul
    · simp only [if_neg h]
      exact contDiff_const
  change ContDiff ℝ 1 (fun x : E =>
    (-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n.1‖ ^ 2)) • U x n.1 +
      ∑ p ∈ s, ∑ q ∈ s,
        if p + q = n.1 then
          thirdFullThreeBandZ3ComplexTransport244 n.1 q (U x p) (U x q)
        else 0)
  exact hVisc.add hSource

/-- The finite coefficient field is real-C¹ as a map on the FINITE
subtype-indexed coefficient space. The outer `contDiff_pi` is essential:
there is deliberately no `Fintype` instance on the whole Z³ lattice. -/
theorem thirdFullThreeBand_z3GalerkinFiniteField_contDiff244
    (mu : ℝ) (s : Finset LocalODEIndex244) :
    ContDiff ℝ 1 (thirdFullThreeBandZ3GalerkinFiniteField244 mu s) := by
  classical
  apply contDiff_pi.mpr
  intro n
  exact thirdFullThreeBand_z3GalerkinFiniteField_coord_contDiff244 mu s n

/-- Genuine Picard–Lindelöf local existence for the complete finite
Galerkin ODE. The existence interval may depend on the cutoff. -/
theorem thirdFullThreeBand_z3GalerkinFiniteField_exists_local244
    (mu a : ℝ) (s : Finset LocalODEIndex244)
    (x₀ : thirdFullThreeBandZ3GalerkinFiniteState244 s) :
    ∃ α : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s,
      α a = x₀ ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ t ∈ Ioo (a - δ) (a + δ),
          HasDerivAt α
            (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (α t)) t := by
  have hC1 : ContDiffAt ℝ 1
      (thirdFullThreeBandZ3GalerkinFiniteField244 mu s) x₀ :=
    (thirdFullThreeBand_z3GalerkinFiniteField_contDiff244 mu s).contDiffAt
  exact hC1.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ a

end
end PrimeTensor.FirstMonomialTriad
