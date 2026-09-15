import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldSlot3RealSchwartzWeak

/-!
# Pressure-free real-Schwartz weak continuity of the full old H³ jet

The preceding slot files establish arbitrary real-Schwartz weak continuity
separately for the four semantic derivative families

    slot0 : uⱼ,
    slot1 : ∂ᵢ uⱼ,
    slot2 : ∂ᵢ∂ₖ uⱼ,
    slot3 : ∂ᵢ∂ₖ∂ₗ uⱼ.

`H3JetIndex` is exactly the nested finite sum of those four families.  This
file packages the completed ladder into one theorem for an arbitrary one of the
120 concrete H³ jet coordinates.

No new analytic input occurs here: the proof is only structural elimination of
the jet index followed by the corresponding already-proved slot theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldJetRealSchwartzWeak
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldJetRealSchwartzWeak :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Every one of the 120 old H³ endpoint jet coordinates has pressure-free weak
continuity against every real Schwartz test on the Euclidean Fourier carrier. -/
theorem continuous_h3PreterminalOldJet_realSchwartzPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : H3JetIndex) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail a q))
          (φ.toLp 2 (volume : Measure H3FourierPoint3))) := by
  rcases a with j | a
  · simpa [h3JetSlot0] using
      (continuous_h3PreterminalOldSlot0_realSchwartzPairing
        hNS ht hEnd hE hTail φ j)

  · rcases a with ji | a
    · rcases ji with ⟨j, i⟩
      simpa [h3JetSlot1] using
        (continuous_h3PreterminalOldSlot1_realSchwartzPairing
          hNS ht hEnd hE hTail φ j i)

    · rcases a with jik | jikl
      · rcases jik with ⟨j, ⟨i, k⟩⟩
        simpa [h3JetSlot2] using
          (continuous_h3PreterminalOldSlot2_realSchwartzPairing
            hNS ht hEnd hE hTail φ j i k)

      · rcases jikl with ⟨j, ⟨i, ⟨k, l⟩⟩⟩
        simpa [h3JetSlot3] using
          (continuous_h3PreterminalOldSlot3_realSchwartzPairing
            hNS ht hEnd hE hTail φ j i k l)

end

end Euclidean
end Bridge
end PrimeTensor
