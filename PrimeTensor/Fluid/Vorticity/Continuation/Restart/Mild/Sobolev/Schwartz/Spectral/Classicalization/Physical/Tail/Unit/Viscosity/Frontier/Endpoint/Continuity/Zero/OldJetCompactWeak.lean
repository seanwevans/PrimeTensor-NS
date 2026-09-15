import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldThirdWeakPairing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.L2.Jet.Continuity

/-!
# Pressure-free compact weak continuity of the actual old H³ L² endpoint jets

The preceding pressure-free branch established continuity of the physical
integrals

    q ↦ ∫ ψ u_j(t+q)
    q ↦ ∫ ψ ∂ᵢ∂ₖ∂ₗ u_j(t+q)

for every compact smooth scalar test `ψ`.

This file identifies those integrals with the genuine real Hilbert pairings

    ⟪ψ, J₀(q)⟫
    ⟪ψ, J₃(q)⟫

where `J₀` and `J₃` are the exact `H3ScalarL2` coordinates carried by
`h3PreterminalCanonicalL2JetOnElapsed`.

The identification is quotient-safe: both `L²` factors are replaced almost
everywhere by their concrete representatives and `L2.inner_def` is used
directly.

Consequently the actual zeroth and ordered-third endpoint jet paths are weakly
continuous against every compact smooth physical test, with no pressure,
temporal-derivative integrability, endpoint continuity, or mild equation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldJetCompactWeak
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldJetCompactWeak :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The actual zeroth `H3ScalarL2` endpoint jet is represented almost
everywhere by the old logged velocity component. -/
theorem h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_old_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    (h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail (h3JetSlot0 j) q :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    loggedVelocityComponent
      u
      (t + (q : ℝ))
      (h3AxisOfFin3 j) := by
  unfold h3PreterminalCanonicalL2JetOnElapsed
  unfold velocityH3L2JetAt
  dsimp only

  have hCoe :=
    MeasureTheory.MemLp.coeFn_toLp
      (velocityH3JetFieldAt_memLp2
        (h3PreterminalTailIntegrableOnElapsed
          hEnd hTail q)
        (h3PreterminalTailMeasurableOnElapsed
          hNS ht hEnd hTail q)
        (h3JetSlot0 j))

  simpa [
    velocityH3JetFieldAt,
    h3JetSlot0
  ] using hCoe

/-- The actual ordered-third `H3ScalarL2` endpoint jet is represented almost
everywhere by the corresponding ordered third derivative of the old velocity. -/
theorem h3PreterminalCanonicalL2JetOnElapsed_slot3_ae_eq_old_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j i k l : Fin 3) :
    (h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail (h3JetSlot3 j i k l) q :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d
      (h3AxisOfFin3 i)
      (spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 l)
          (loggedVelocityComponent
            u
            (t + (q : ℝ))
            (h3AxisOfFin3 j)))) := by
  unfold h3PreterminalCanonicalL2JetOnElapsed
  unfold velocityH3L2JetAt
  dsimp only

  have hCoe :=
    MeasureTheory.MemLp.coeFn_toLp
      (velocityH3JetFieldAt_memLp2
        (h3PreterminalTailIntegrableOnElapsed
          hEnd hTail q)
        (h3PreterminalTailMeasurableOnElapsed
          hNS ht hEnd hTail q)
        (h3JetSlot3 j i k l))

  simpa [
    velocityH3JetFieldAt,
    h3JetSlot3
  ] using hCoe

/-- Hilbert pairing of a compact test with the actual zeroth endpoint jet is
exactly the pressure-free old velocity scalar pairing. -/
theorem h3WeakTestFunctionPhysicalL2_inner_preterminalOldSlot0_eq_pairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (j : Fin 3)
    (q : Set.Icc (0 : ℝ) tau) :
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 ψ)
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) q)
      =
    h3PreterminalOldVelocityWeakScalarPairingOnElapsed
      hNS ht hEnd hTail ψ j q := by
  rw [MeasureTheory.L2.inner_def]

  unfold h3PreterminalOldVelocityWeakScalarPairingOnElapsed

  apply integral_congr_ae

  filter_upwards [
    h3WeakTestFunctionPhysicalL2_ae ψ,
    h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_old_pressureFree
      hNS ht hEnd hTail q j
  ] with x hψ hJ

  rw [hψ, hJ]

  simpa [mul_comm]

/-- Hilbert pairing of a compact test with the actual ordered-third endpoint
jet is exactly the pressure-free old third-derivative scalar pairing. -/
theorem h3WeakTestFunctionPhysicalL2_inner_preterminalOldSlot3_eq_pairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (j i k l : Fin 3)
    (q : Set.Icc (0 : ℝ) tau) :
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 ψ)
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot3 j i k l) q)
      =
    h3PreterminalOldVelocityThirdWeakScalarPairingOnElapsed
      hNS ht hEnd hTail ψ j i k l q := by
  rw [MeasureTheory.L2.inner_def]

  unfold h3PreterminalOldVelocityThirdWeakScalarPairingOnElapsed

  apply integral_congr_ae

  filter_upwards [
    h3WeakTestFunctionPhysicalL2_ae ψ,
    h3PreterminalCanonicalL2JetOnElapsed_slot3_ae_eq_old_pressureFree
      hNS ht hEnd hTail q j i k l
  ] with x hψ hJ

  rw [hψ, hJ]

  simpa [mul_comm]

/-- Compact-test weak Hilbert continuity of one actual zeroth endpoint jet
coordinate. -/
theorem continuous_h3WeakTest_inner_preterminalOldSlot0
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (j : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 ψ)
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q)) := by
  have hPair :
      Continuous
        (h3PreterminalOldVelocityWeakScalarPairingOnElapsed
          hNS ht hEnd hTail ψ j) :=
    continuous_h3PreterminalOldVelocityWeakScalarPairingOnElapsed
      hNS ht hEnd hE hTail ψ j

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 ψ)
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q))
        =
      h3PreterminalOldVelocityWeakScalarPairingOnElapsed
        hNS ht hEnd hTail ψ j := by
    funext q
    exact
      h3WeakTestFunctionPhysicalL2_inner_preterminalOldSlot0_eq_pairing
        hNS ht hEnd hTail ψ j q

  rw [hEq]

  exact hPair

/-- Compact-test weak Hilbert continuity of one actual ordered-third endpoint
jet coordinate. -/
theorem continuous_h3WeakTest_inner_preterminalOldSlot3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (j i k l : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 ψ)
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) q)) := by
  have hPair :
      Continuous
        (h3PreterminalOldVelocityThirdWeakScalarPairingOnElapsed
          hNS ht hEnd hTail ψ j i k l) :=
    continuous_h3PreterminalOldVelocityThirdWeakScalarPairingOnElapsed
      hNS ht hEnd hE hTail ψ j i k l

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 ψ)
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) q))
        =
      h3PreterminalOldVelocityThirdWeakScalarPairingOnElapsed
        hNS ht hEnd hTail ψ j i k l := by
    funext q
    exact
      h3WeakTestFunctionPhysicalL2_inner_preterminalOldSlot3_eq_pairing
        hNS ht hEnd hTail ψ j i k l q

  rw [hEq]

  exact hPair

/-- Pressure-free compact-test weak continuity package for precisely the
zeroth and ordered-third physical `L²` endpoint coordinates used by the
continuation interface. -/
def H3PreterminalCanonicalL2EndpointCompactWeakContinuousOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  (∀
    (j : Fin 3)
    (ψ : H3WeakTestFunction),
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          inner ℝ
            (h3WeakTestFunctionPhysicalL2 ψ)
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q)))
  ∧
  (∀
    (j i k l : Fin 3)
    (ψ : H3WeakTestFunction),
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          inner ℝ
            (h3WeakTestFunctionPhysicalL2 ψ)
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i k l) q)))

/-- The old preterminal solution satisfies compact-test weak continuity of the
actual endpoint jet coordinates outright. -/
theorem h3PreterminalCanonicalL2EndpointCompactWeakContinuousOnElapsed_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalCanonicalL2EndpointCompactWeakContinuousOnElapsed
      hNS ht hEnd hTail := by
  constructor
  · intro j ψ
    exact
      continuous_h3WeakTest_inner_preterminalOldSlot0
        hNS ht hEnd hE hTail ψ j
  · intro j i k l ψ
    exact
      continuous_h3WeakTest_inner_preterminalOldSlot3
        hNS ht hEnd hE hTail ψ j i k l

end

end Euclidean
end Bridge
end PrimeTensor
