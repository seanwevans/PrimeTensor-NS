import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldSlot0RealSchwartzWeakFTC

/-!
# Pressure-free weak continuity of old first spatial jets against real Schwartz tests

`OldSlot0RealSchwartzWeakFTC` proved the raw Euclidean integration-by-parts
identity

    ∫ (∂ᵢ uⱼ) φ = - ∫ uⱼ (∂ᵢ φ)

for every retained elapsed snapshot and every real Schwartz test.

This file passes that identity through the actual quotient `L²` classes used by
the H³ endpoint jet.  The canonical physical slot `1 (j,i)` is represented
almost everywhere by `∂ᵢ uⱼ`; after carrier transport, the corresponding
Fourier-carrier real `L²` class is represented almost everywhere by the raw
transported derivative.  The same is already true for slot `0`.

Consequently

    ⟪ transport(J₁(j,i,q)), φ ⟫
      =
    - ⟪ transport(J₀(j,q)), ∂ᵢ φ ⟫.

The right-hand side is continuous in elapsed time by
`OldSlot0RealSchwartzWeakDeriv`, so every old first spatial jet is weakly
continuous against arbitrary real Schwartz tests.

No pressure, temporal derivative, endpoint continuity, or mild equation enters.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldSlot1RealSchwartzWeak
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldSlot1RealSchwartzWeak :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The actual first `H3ScalarL2` endpoint jet is represented almost everywhere
by the corresponding first spatial derivative of the old velocity. -/
theorem h3PreterminalCanonicalL2JetOnElapsed_slot1_ae_eq_old_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j i : Fin 3) :
    (h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail (h3JetSlot1 j i) q :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d
      (h3AxisOfFin3 i)
      (loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 j)) := by
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
        (h3JetSlot1 j i))

  simpa [
    velocityH3JetFieldAt,
    h3JetSlot1
  ] using hCoe

/-- After canonical carrier transport, the old zeroth jet is represented almost
everywhere by the raw transported velocity coordinate. -/
theorem h3ToFourierRealL2_preterminalOldSlot0_ae_eq_transport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    (h3ToFourierRealL2
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) q) :
        H3FourierPoint3 → ℝ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3TransportScalarField
      (loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 j)) := by
  let f : ScalarField3 :=
    loggedVelocityComponent
      u
      (t + (q : ℝ))
      (h3AxisOfFin3 j)

  let hf : MemLp f 2 (volume : Measure Point3) :=
    h3PreterminalOldSlot0_raw_memLp_two
      hNS ht hEnd hTail q j

  have hPhysical :
      h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) q
        =
      hf.toLp f := by
    apply MeasureTheory.Lp.ext

    have hOld :=
      h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_old_pressureFree
        hNS ht hEnd hTail q j

    have hToLp :=
      MeasureTheory.MemLp.coeFn_toLp hf

    exact hOld.trans hToLp.symm

  rw [hPhysical]

  exact
    h3ToFourierRealL2_coeFn_eq_transport hf

/-- After canonical carrier transport, the old first jet is represented almost
everywhere by the raw transported first spatial derivative. -/
theorem h3ToFourierRealL2_preterminalOldSlot1_ae_eq_transport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j i : Fin 3) :
    (h3ToFourierRealL2
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot1 j i) q) :
        H3FourierPoint3 → ℝ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3TransportScalarField
      (spatial3.d
        (h3AxisOfFin3 i)
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 j))) := by
  let f : ScalarField3 :=
    spatial3.d
      (h3AxisOfFin3 i)
      (loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 j))

  let hf : MemLp f 2 (volume : Measure Point3) :=
    h3PreterminalOldSlot1_raw_memLp_two
      hNS ht hEnd hTail q j i

  have hPhysical :
      h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot1 j i) q
        =
      hf.toLp f := by
    apply MeasureTheory.Lp.ext

    have hOld :=
      h3PreterminalCanonicalL2JetOnElapsed_slot1_ae_eq_old_pressureFree
        hNS ht hEnd hTail q j i

    have hToLp :=
      MeasureTheory.MemLp.coeFn_toLp hf

    exact hOld.trans hToLp.symm

  rw [hPhysical]

  exact
    h3ToFourierRealL2_coeFn_eq_transport hf

/-- Fourier-carrier Hilbert pairing of the old zeroth jet with a real Schwartz
test is the corresponding raw transported integral. -/
theorem inner_h3ToFourierRealL2_preterminalOldSlot0_realSchwartz_eq_integral
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j : Fin 3) :
    inner ℝ
        (h3ToFourierRealL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q))
        (φ.toLp 2 (volume : Measure H3FourierPoint3))
      =
    ∫ x : H3FourierPoint3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3TransportScalarField
          (loggedVelocityComponent
            u
            (t + (q : ℝ))
            (h3AxisOfFin3 j))) x)
        (φ x)
      ∂volume := by
  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  filter_upwards [
    h3ToFourierRealL2_preterminalOldSlot0_ae_eq_transport
      hNS ht hEnd hTail q j,
    φ.coeFn_toLp 2 (volume : Measure H3FourierPoint3)
  ] with x hJ hφ

  rw [hJ, hφ]
  simpa [smul_eq_mul, mul_comm]

/-- Fourier-carrier Hilbert pairing of the old first jet with a real Schwartz
test is the corresponding raw transported derivative integral. -/
theorem inner_h3ToFourierRealL2_preterminalOldSlot1_realSchwartz_eq_integral
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i : Fin 3) :
    inner ℝ
        (h3ToFourierRealL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot1 j i) q))
        (φ.toLp 2 (volume : Measure H3FourierPoint3))
      =
    ∫ x : H3FourierPoint3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3TransportScalarField
          (spatial3.d
            (h3AxisOfFin3 i)
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 j)))) x)
        (φ x)
      ∂volume := by
  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  filter_upwards [
    h3ToFourierRealL2_preterminalOldSlot1_ae_eq_transport
      hNS ht hEnd hTail q j i,
    φ.coeFn_toLp 2 (volume : Measure H3FourierPoint3)
  ] with x hJ hφ

  rw [hJ, hφ]
  simpa [smul_eq_mul, mul_comm]

/-- Exact Fourier-carrier weak spatial derivative identity for the actual old
slot0 and slot1 endpoint `L²` classes. -/
theorem inner_h3ToFourierRealL2_preterminalOldSlot1_realSchwartz_eq_neg_slot0LineDeriv
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i : Fin 3) :
    inner ℝ
        (h3ToFourierRealL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot1 j i) q))
        (φ.toLp 2 (volume : Measure H3FourierPoint3))
      =
    -
    inner ℝ
        (h3ToFourierRealL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
            𝓢(H3FourierPoint3, ℝ)).toLp
          2 (volume : Measure H3FourierPoint3)) := by
  rw [
    inner_h3ToFourierRealL2_preterminalOldSlot1_realSchwartz_eq_integral
      hNS ht hEnd hTail q φ j i,
    inner_h3ToFourierRealL2_preterminalOldSlot0_realSchwartz_eq_integral
      hNS ht hEnd hTail q
      (∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ)
      j
  ]

  exact
    h3PreterminalOldSlot1_transport_realSchwartz_integral_eq_neg_slot0LineDeriv
      hNS ht hEnd hTail q φ j i

/-- Pressure-free weak continuity of every old first spatial endpoint jet
against every real Schwartz test. -/
theorem continuous_h3PreterminalOldSlot1_realSchwartzPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot1 j i) q))
          (φ.toLp 2 (volume : Measure H3FourierPoint3))) := by
  have hZero :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          inner ℝ
            (h3ToFourierRealL2
              (h3PreterminalCanonicalL2JetOnElapsed
                hNS ht hEnd hTail (h3JetSlot0 j) q))
            ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
                𝓢(H3FourierPoint3, ℝ)).toLp
              2 (volume : Measure H3FourierPoint3))) :=
    continuous_h3PreterminalOldSlot0_realSchwartzFinLineDerivPairing
      hNS ht hEnd hE hTail φ i j

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot1 j i) q))
          (φ.toLp 2 (volume : Measure H3FourierPoint3)))
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        -
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q))
          ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
              𝓢(H3FourierPoint3, ℝ)).toLp
            2 (volume : Measure H3FourierPoint3))) := by
    funext q
    exact
      inner_h3ToFourierRealL2_preterminalOldSlot1_realSchwartz_eq_neg_slot0LineDeriv
        hNS ht hEnd hTail q φ j i

  rw [hEq]

  exact hZero.neg

end

end Euclidean
end Bridge
end PrimeTensor
