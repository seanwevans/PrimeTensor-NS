import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldSlot1RealSchwartzWeakFTC

/-!
# Pressure-free weak continuity of old second spatial jets against real Schwartz tests

`OldSlot1RealSchwartzWeakFTC` proved the raw Euclidean identity

    ∫ (∂ᵢ∂ₖ uⱼ) φ = - ∫ (∂ₖ uⱼ) (∂ᵢ φ)

for every retained elapsed snapshot and every real Schwartz test.

This file identifies the raw ordered-second derivative with the actual
`H3ScalarL2` slot `h3JetSlot2 j i k`, transports that quotient class to the
Euclidean Fourier carrier, and rewrites its Hilbert pairing as the raw integral.
Thus

    ⟪ transport(J₂(j,i,k,q)), φ ⟫
      =
    - ⟪ transport(J₁(j,k,q)), ∂ᵢ φ ⟫.

The right-hand side is continuous by the already-proved slot1 arbitrary
real-Schwartz weak continuity theorem, so slot2 weak continuity follows without
pressure, temporal derivatives, endpoint continuity, or a mild equation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldSlot2RealSchwartzWeak
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldSlot2RealSchwartzWeak :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The actual ordered-second `H3ScalarL2` endpoint jet is represented almost
everywhere by the corresponding ordered second spatial derivative. -/
theorem h3PreterminalCanonicalL2JetOnElapsed_slot2_ae_eq_old_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j i k : Fin 3) :
    (h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail (h3JetSlot2 j i k) q :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d
      (h3AxisOfFin3 i)
      (spatial3.d
        (h3AxisOfFin3 k)
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 j))) := by
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
        (h3JetSlot2 j i k))

  simpa [
    velocityH3JetFieldAt,
    h3JetSlot2
  ] using hCoe

/-- After canonical carrier transport, the ordered-second endpoint jet is
represented almost everywhere by the transported raw ordered-second
derivative. -/
theorem h3ToFourierRealL2_preterminalOldSlot2_ae_eq_transport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j i k : Fin 3) :
    (h3ToFourierRealL2
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot2 j i k) q) :
        H3FourierPoint3 → ℝ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3TransportScalarField
      (spatial3.d
        (h3AxisOfFin3 i)
        (spatial3.d
          (h3AxisOfFin3 k)
          (loggedVelocityComponent
            u
            (t + (q : ℝ))
            (h3AxisOfFin3 j)))) := by
  let f : ScalarField3 :=
    spatial3.d
      (h3AxisOfFin3 i)
      (spatial3.d
        (h3AxisOfFin3 k)
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 j)))

  let hf : MemLp f 2 (volume : Measure Point3) :=
    h3PreterminalOldSlot2_raw_memLp_two
      hNS ht hEnd hTail q j i k

  have hPhysical :
      h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot2 j i k) q
        =
      hf.toLp f := by
    apply MeasureTheory.Lp.ext

    have hOld :=
      h3PreterminalCanonicalL2JetOnElapsed_slot2_ae_eq_old_pressureFree
        hNS ht hEnd hTail q j i k

    have hToLp :=
      MeasureTheory.MemLp.coeFn_toLp hf

    exact hOld.trans hToLp.symm

  rw [hPhysical]

  exact
    h3ToFourierRealL2_coeFn_eq_transport hf

/-- Fourier-carrier Hilbert pairing of an ordered-second endpoint jet with a
real Schwartz test is the corresponding raw transported integral. -/
theorem inner_h3ToFourierRealL2_preterminalOldSlot2_realSchwartz_eq_integral
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i k : Fin 3) :
    inner ℝ
        (h3ToFourierRealL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot2 j i k) q))
        (φ.toLp 2 (volume : Measure H3FourierPoint3))
      =
    ∫ x : H3FourierPoint3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3TransportScalarField
          (spatial3.d
            (h3AxisOfFin3 i)
            (spatial3.d
              (h3AxisOfFin3 k)
              (loggedVelocityComponent
                u
                (t + (q : ℝ))
                (h3AxisOfFin3 j))))) x)
        (φ x)
      ∂volume := by
  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  filter_upwards [
    h3ToFourierRealL2_preterminalOldSlot2_ae_eq_transport
      hNS ht hEnd hTail q j i k,
    φ.coeFn_toLp 2 (volume : Measure H3FourierPoint3)
  ] with x hJ hφ

  rw [hJ, hφ]
  simpa [smul_eq_mul, mul_comm]

/-- Exact Fourier-carrier weak spatial derivative identity for the actual old
slot1 and ordered-slot2 endpoint `L²` classes. -/
theorem inner_h3ToFourierRealL2_preterminalOldSlot2_realSchwartz_eq_neg_slot1LineDeriv
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i k : Fin 3) :
    inner ℝ
        (h3ToFourierRealL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot2 j i k) q))
        (φ.toLp 2 (volume : Measure H3FourierPoint3))
      =
    -
    inner ℝ
        (h3ToFourierRealL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot1 j k) q))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
            𝓢(H3FourierPoint3, ℝ)).toLp
          2 (volume : Measure H3FourierPoint3)) := by
  rw [
    inner_h3ToFourierRealL2_preterminalOldSlot2_realSchwartz_eq_integral
      hNS ht hEnd hTail q φ j i k,
    inner_h3ToFourierRealL2_preterminalOldSlot1_realSchwartz_eq_integral
      hNS ht hEnd hTail q
      (∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ)
      j k
  ]

  exact
    h3PreterminalOldSlot2_transport_realSchwartz_integral_eq_neg_slot1LineDeriv
      hNS ht hEnd hTail q φ j i k

/-- Pressure-free weak continuity of every old ordered-second spatial endpoint
jet against every real Schwartz test. -/
theorem continuous_h3PreterminalOldSlot2_realSchwartzPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i k : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j i k) q))
          (φ.toLp 2 (volume : Measure H3FourierPoint3))) := by
  have hOne :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          inner ℝ
            (h3ToFourierRealL2
              (h3PreterminalCanonicalL2JetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j k) q))
            ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
                𝓢(H3FourierPoint3, ℝ)).toLp
              2 (volume : Measure H3FourierPoint3))) :=
    continuous_h3PreterminalOldSlot1_realSchwartzPairing
      hNS ht hEnd hE hTail
      (∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ)
      j k

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j i k) q))
          (φ.toLp 2 (volume : Measure H3FourierPoint3)))
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        -
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot1 j k) q))
          ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
              𝓢(H3FourierPoint3, ℝ)).toLp
            2 (volume : Measure H3FourierPoint3))) := by
    funext q
    exact
      inner_h3ToFourierRealL2_preterminalOldSlot2_realSchwartz_eq_neg_slot1LineDeriv
        hNS ht hEnd hTail q φ j i k

  rw [hEq]

  exact hOne.neg

end

end Euclidean
end Bridge
end PrimeTensor
