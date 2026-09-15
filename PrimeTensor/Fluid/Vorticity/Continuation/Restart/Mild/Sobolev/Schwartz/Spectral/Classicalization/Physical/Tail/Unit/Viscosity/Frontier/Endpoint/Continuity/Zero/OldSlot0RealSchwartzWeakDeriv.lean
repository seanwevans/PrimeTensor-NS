import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldSlot0RealSchwartzWeak

/-!
# Pressure-free slot0 weak continuity against real Schwartz derivatives

`OldSlot0RealSchwartzWeak` proves continuity of the transported old zeroth
endpoint coordinate against every real Schwartz test.

A coordinate directional derivative of a real Schwartz function is again a
real Schwartz function.  Therefore the same pressure-free continuity statement
holds immediately when the fixed test is

    ∂_{e_a} φ.

This small checkpoint packages the derivative-tested form explicitly.  It adds
no PDE estimate, endpoint-continuity assumption, pressure term, or temporal
integrability hypothesis.  The next scalar checkpoint can use this form without
reopening the cutoff-density argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldSlot0RealSchwartzWeakDeriv
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Weak continuity of the old zeroth endpoint coordinate against one
coordinate derivative of an arbitrary real Schwartz test. -/
theorem continuous_h3PreterminalOldSlot0_realSchwartzLineDerivPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three)
    (j : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q))
          ((∂_{h3FourierAxisDirection a} φ :
              𝓢(H3FourierPoint3, ℝ)).toLp
            2 (volume : Measure H3FourierPoint3))) := by
  exact
    continuous_h3PreterminalOldSlot0_realSchwartzPairing
      hNS ht hEnd hE hTail
      (∂_{h3FourierAxisDirection a} φ)
      j

/-- Finite-coordinate specialization of the preceding derivative-tested weak
continuity statement. -/
theorem continuous_h3PreterminalOldSlot0_realSchwartzFinLineDerivPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (i j : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q))
          ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
              𝓢(H3FourierPoint3, ℝ)).toLp
            2 (volume : Measure H3FourierPoint3))) := by
  exact
    continuous_h3PreterminalOldSlot0_realSchwartzLineDerivPairing
      hNS ht hEnd hE hTail φ (h3AxisOfFin3 i) j

end

end Euclidean
end Bridge
end PrimeTensor
