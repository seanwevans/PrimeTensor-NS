import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinRestartSeam
import Mathlib.Tactic

/-!
# Finite Z³ Galerkin: a genuine strong right-maximal endpoint lies beyond the analytic horizon

For every finite set of frequencies S, the complete projected Leray ODE is a
finite-dimensional smooth vector field. The preceding theorem restarts ANY
strong solution on [a,b) at a finite right endpoint inside the common
analytic window and glues an exact strong solution across that endpoint.

Here we turn the exact restart into a sharp, cutoff-independent alternative:

  a < b,  strong ODE on [a,b),  strict W_log(2)(u(a)) < 100,
  0 ≤ mu ≤ 1/10

  => (the strong solution extends beyond b) OR (window < b - a).

In particular a right-maximal half-open strong Galerkin solution cannot have
terminal time b ≤ a + window. The endpoint b = a + window is excluded too.

This theorem does NOT construct a maximal solution or assert existence on the
full common horizon. Those require an existence/maximal-flow construction and
compatibility of solutions on overlapping intervals, which remain separate.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev MaxIndex244 := thirdFullThreeBandZ3Index244

/-- An exact strong continuation of the SAME finite complex Leray field,
agreeing with the given solution on every preterminal time. The extension
exists on an interval longer than [a,b), and is differentiable at the old
terminal time b; no ball condition is imposed on the extension. -/
def thirdFullThreeBandZ3GalerkinStrongRightExtendible244
    (mu a b : ℝ) (s : Finset MaxIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧
    ∃ gamma : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s,
      (∀ t ∈ Ico a b, gamma t = alpha t) ∧
      (∀ t ∈ Ico a (b + delta),
        HasDerivAt gamma
          (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)) t)

/-- Right-maximality is an EXPLICIT property of a given strong half-open
trajectory: there is no longer exact strong extension that agrees on [a,b).
It does not assume or assert that such a maximal trajectory exists. -/
def thirdFullThreeBandZ3GalerkinStrongRightMaximal244
    (mu a b : ℝ) (s : Finset MaxIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s) : Prop :=
  ¬ thirdFullThreeBandZ3GalerkinStrongRightExtendible244 mu a b s alpha

/-- The established two-sided Picard restart is a real extension witness
for every potential preterminal b in the uniform analytic window. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_extendible_insideWindow244
    (mu a b : ℝ) (hab : a < b)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset MaxIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha a)) < 100) :
    thirdFullThreeBandZ3GalerkinStrongRightExtendible244 mu a b s alpha := by
  obtain ⟨delta, hDelta, gamma, _hInitial, hAgree, hStrong,
      _hHigh, _hSpeed⟩ :=
    thirdFullThreeBand_z3GalerkinPreterminalGluedStrongRestart244
      mu a b hab hmu hmuMax hWindow s alpha hODE hInitial
  exact ⟨delta, hDelta, gamma, hAgree, hStrong⟩

/-- Genuine finite Navier--Stokes Galerkin endpoint alternative:
EITHER the trajectory admits an exact C¹ continuation through b,
OR b lies strictly AFTER the cutoff-independent window.

No uniform local Picard radius is postulated: the proof uses the already
established analytic nonescape, Picard restart, and seam derivative. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_strongEndpointAlternative244
    (mu a b : ℝ) (hab : a < b)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset MaxIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha a)) < 100) :
    thirdFullThreeBandZ3GalerkinStrongRightExtendible244 mu a b s alpha ∨
      thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 < b - a := by
  by_cases hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244
  · exact Or.inl
      (thirdFullThreeBand_z3GalerkinFiniteODE_extendible_insideWindow244
        mu a b hab hmu hmuMax hWindow s alpha hODE hInitial)
  · exact Or.inr (lt_of_not_ge hWindow)

/-- A genuinely right-maximal finite Galerkin strong path can terminate
only STRICTLY BEYOND the universal analytic horizon.

The cutoff S does not appear in the lower-bound constant. This is the
no-premature-maximal-endpoint theorem, conditional only on the existence of
a right-maximal path; constructing it is a subsequent obligation. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_rightMaximal_beyondWindow244
    (mu a b : ℝ) (hab : a < b)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset MaxIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha a)) < 100)
    (hMaximal : thirdFullThreeBandZ3GalerkinStrongRightMaximal244
      mu a b s alpha) :
    thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 < b - a := by
  have hAlternative :=
    thirdFullThreeBand_z3GalerkinFiniteODE_strongEndpointAlternative244
      mu a b hab hmu hmuMax s alpha hODE hInitial
  rcases hAlternative with hExtend | hBeyond
  · exact False.elim (hMaximal hExtend)
  · exact hBeyond

end
end PrimeTensor.FirstMonomialTriad
