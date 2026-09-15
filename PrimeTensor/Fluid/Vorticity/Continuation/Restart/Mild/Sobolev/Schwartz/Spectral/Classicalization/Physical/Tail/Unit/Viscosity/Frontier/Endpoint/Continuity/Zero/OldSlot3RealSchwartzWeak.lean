import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldSlot2RealSchwartzWeakFTC

/-!
# Pressure-free weak continuity of old third spatial jets against real Schwartz tests

`OldSlot2RealSchwartzWeakFTC` proves the final raw Euclidean identity

    ∫ (∂ᵢ∂ₖ∂ₗ uⱼ) φ
      =
    - ∫ (∂ₖ∂ₗ uⱼ) (∂ᵢ φ)

for every retained elapsed snapshot and every real Schwartz test.

The physical quotient representative of slot `3` was already proved in
`OldJetCompactWeak`.  This file transports that quotient class to the
Euclidean Fourier carrier and identifies its Hilbert pairing with the raw
integral.  Consequently

    ⟪ transport(J₃(j,i,k,l,q)), φ ⟫
      =
    - ⟪ transport(J₂(j,k,l,q)), ∂ᵢ φ ⟫.

The right-hand side is continuous by the slot2 arbitrary real-Schwartz weak
continuity theorem.  Thus every ordered H³ jet coordinate, from slot `0`
through slot `3`, now has pressure-free weak continuity against arbitrary real
Schwartz tests.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldSlot3RealSchwartzWeak
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldSlot3RealSchwartzWeak :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- After canonical carrier transport, the ordered-third endpoint jet is
represented almost everywhere by the transported raw ordered-third
derivative. -/
theorem h3ToFourierRealL2_preterminalOldSlot3_ae_eq_transport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j i k l : Fin 3) :
    (h3ToFourierRealL2
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot3 j i k l) q) :
        H3FourierPoint3 → ℝ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3TransportScalarField
      (spatial3.d
        (h3AxisOfFin3 i)
        (spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 l)
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 j))))) := by
  let f : ScalarField3 :=
    spatial3.d
      (h3AxisOfFin3 i)
      (spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 l)
          (loggedVelocityComponent
            u
            (t + (q : ℝ))
            (h3AxisOfFin3 j))))

  let hf : MemLp f 2 (volume : Measure Point3) :=
    h3PreterminalOldSlot3_raw_memLp_two
      hNS ht hEnd hTail q j i k l

  have hPhysical :
      h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot3 j i k l) q
        =
      hf.toLp f := by
    apply MeasureTheory.Lp.ext

    have hOld :=
      h3PreterminalCanonicalL2JetOnElapsed_slot3_ae_eq_old_pressureFree
        hNS ht hEnd hTail q j i k l

    have hToLp :=
      MeasureTheory.MemLp.coeFn_toLp hf

    exact hOld.trans hToLp.symm

  rw [hPhysical]

  exact
    h3ToFourierRealL2_coeFn_eq_transport hf

/-- Fourier-carrier Hilbert pairing of an ordered-third endpoint jet with a
real Schwartz test is the corresponding raw transported integral. -/
theorem inner_h3ToFourierRealL2_preterminalOldSlot3_realSchwartz_eq_integral
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i k l : Fin 3) :
    inner ℝ
        (h3ToFourierRealL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) q))
        (φ.toLp 2 (volume : Measure H3FourierPoint3))
      =
    ∫ x : H3FourierPoint3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3TransportScalarField
          (spatial3.d
            (h3AxisOfFin3 i)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 l)
                (loggedVelocityComponent
                  u
                  (t + (q : ℝ))
                  (h3AxisOfFin3 j)))))) x)
        (φ x)
      ∂volume := by
  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  filter_upwards [
    h3ToFourierRealL2_preterminalOldSlot3_ae_eq_transport
      hNS ht hEnd hTail q j i k l,
    φ.coeFn_toLp 2 (volume : Measure H3FourierPoint3)
  ] with x hJ hφ

  rw [hJ, hφ]
  simpa [smul_eq_mul, mul_comm]

/-- Exact Fourier-carrier weak spatial derivative identity for the actual old
ordered-slot2 and ordered-slot3 endpoint `L²` classes. -/
theorem inner_h3ToFourierRealL2_preterminalOldSlot3_realSchwartz_eq_neg_slot2LineDeriv
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i k l : Fin 3) :
    inner ℝ
        (h3ToFourierRealL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) q))
        (φ.toLp 2 (volume : Measure H3FourierPoint3))
      =
    -
    inner ℝ
        (h3ToFourierRealL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot2 j k l) q))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
            𝓢(H3FourierPoint3, ℝ)).toLp
          2 (volume : Measure H3FourierPoint3)) := by
  rw [
    inner_h3ToFourierRealL2_preterminalOldSlot3_realSchwartz_eq_integral
      hNS ht hEnd hTail q φ j i k l,
    inner_h3ToFourierRealL2_preterminalOldSlot2_realSchwartz_eq_integral
      hNS ht hEnd hTail q
      (∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ)
      j k l
  ]

  exact
    h3PreterminalOldSlot3_transport_realSchwartz_integral_eq_neg_slot2LineDeriv
      hNS ht hEnd hTail q φ j i k l

/-- Pressure-free weak continuity of every old ordered-third spatial endpoint
jet against every real Schwartz test. -/
theorem continuous_h3PreterminalOldSlot3_realSchwartzPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i k l : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i k l) q))
          (φ.toLp 2 (volume : Measure H3FourierPoint3))) := by
  have hTwo :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          inner ℝ
            (h3ToFourierRealL2
              (h3PreterminalCanonicalL2JetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j k l) q))
            ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
                𝓢(H3FourierPoint3, ℝ)).toLp
              2 (volume : Measure H3FourierPoint3))) :=
    continuous_h3PreterminalOldSlot2_realSchwartzPairing
      hNS ht hEnd hE hTail
      (∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ)
      j k l

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i k l) q))
          (φ.toLp 2 (volume : Measure H3FourierPoint3)))
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        -
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j k l) q))
          ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
              𝓢(H3FourierPoint3, ℝ)).toLp
            2 (volume : Measure H3FourierPoint3))) := by
    funext q
    exact
      inner_h3ToFourierRealL2_preterminalOldSlot3_realSchwartz_eq_neg_slot2LineDeriv
        hNS ht hEnd hTail q φ j i k l

  rw [hEq]

  exact hTwo.neg

end

end Euclidean
end Bridge
end PrimeTensor
