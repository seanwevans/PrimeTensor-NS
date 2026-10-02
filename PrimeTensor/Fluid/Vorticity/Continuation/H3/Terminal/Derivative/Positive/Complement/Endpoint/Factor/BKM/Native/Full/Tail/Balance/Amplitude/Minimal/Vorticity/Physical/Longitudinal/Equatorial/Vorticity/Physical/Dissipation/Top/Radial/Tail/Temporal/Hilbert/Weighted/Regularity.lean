import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Derivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# C¹ regularity of the selected top-tail weighted Hilbert path

The selected cutoff-free weighted velocity state

    q² û_i

already has a strong Fourier `L²` derivative at every strict interior point of
each positive compact restart slab.  That derivative is the weighted
Navier--Stokes right-hand side

    -q³ û_i - q² F_i,

and the right-hand side is strongly continuous in Fourier `L²`.

This file packages those two existing facts into the exact local temporal
regularity needed for the physical old-state transport:

    DifferentiableOn ℝ V (Q/2,Q)
      ∧
    ContinuousOn (deriv V) (Q/2,Q).

Equivalently, the selected weighted Hilbert path is `C¹` on the strict slab.
No new estimate or endpoint hypothesis is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/--
The selected intrinsic `q² û_i` Fourier `L²` path has a continuous strong
derivative on every strict positive restart slab.
-/
theorem h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_temporalDerivativeRegularity
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3) :
    let V : ℝ → H3FourierComplexL2 :=
      Set.IccExtend
        (by linarith : Q / 2 ≤ Q)
        (
          h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
            hNS ht₀ hE hTail hQ hQR i
        )
    let I : Set ℝ :=
      Set.Ioo (Q / 2) Q
    DifferentiableOn ℝ V I
      ∧
    ContinuousOn (deriv V) I := by

  dsimp only

  have hHalfLe :
      Q / 2 ≤ Q := by
    linarith

  let Vclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR i

  let Gclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR i

  let V : ℝ → H3FourierComplexL2 :=
    Set.IccExtend
      hHalfLe
      Vclosed

  let G : ℝ → H3FourierComplexL2 :=
    Set.IccExtend
      hHalfLe
      Gclosed

  let I : Set ℝ :=
    Set.Ioo (Q / 2) Q

  have hGClosedContinuous :
      Continuous Gclosed := by
    dsimp only [Gclosed]
    exact
      continuous_h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
        hNS ht₀ hE hTail hQ hQR i

  have hGContinuous :
      Continuous G := by
    dsimp only [G]
    exact
      hGClosedContinuous.Icc_extend'

  have hDifferentiable :
      DifferentiableOn ℝ V I := by

    intro x hx

    have hD :=
      h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_hasDerivAt
        hNS ht₀ hE hTail hQ hQR i hx

    exact
      hD.differentiableAt.differentiableWithinAt

  have hDerivEq :
      ∀ x : ℝ,
        x ∈ I
          →
        deriv V x = G x := by

    intro x hx

    have hD :=
      h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_hasDerivAt
        hNS ht₀ hE hTail hQ hQR i hx

    have hGx :
        G x
          =
        Gclosed
          ⟨x, hx.1.le, hx.2.le⟩ := by

      dsimp only [G]

      rw [
        Set.IccExtend_of_mem
          hHalfLe
          Gclosed
          ⟨hx.1.le, hx.2.le⟩
      ]

    rw [hD.deriv]

    exact hGx.symm

  refine
    ⟨
      hDifferentiable,
      ?_
    ⟩

  apply
    hGContinuous.continuousOn.congr

  intro x hx

  exact
    hDerivEq x hx

/--
Equivalent `C¹` packaging of the selected weighted Hilbert path on the strict
restart slab.
-/
theorem h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_contDiffOn_one
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3) :
    let V : ℝ → H3FourierComplexL2 :=
      Set.IccExtend
        (by linarith : Q / 2 ≤ Q)
        (
          h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
            hNS ht₀ hE hTail hQ hQR i
        )
    ContDiffOn ℝ 1 V (Set.Ioo (Q / 2) Q) := by

  dsimp only

  let V : ℝ → H3FourierComplexL2 :=
    Set.IccExtend
      (by linarith : Q / 2 ≤ Q)
      (
        h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR i
      )

  have hRegularity :
      DifferentiableOn ℝ V (Set.Ioo (Q / 2) Q)
        ∧
      ContinuousOn
        (deriv V)
        (Set.Ioo (Q / 2) Q) := by

    dsimp only [V]

    exact
      h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_temporalDerivativeRegularity
        hNS ht₀ hE hTail hQ hQR i

  have hCriterion :
      ContDiffOn ℝ 1 V (Set.Ioo (Q / 2) Q)
        ↔
      DifferentiableOn ℝ V (Set.Ioo (Q / 2) Q)
        ∧
      ContinuousOn
        (deriv V)
        (Set.Ioo (Q / 2) Q) := by

    simpa using
      (
        contDiffOn_succ_iff_deriv_of_isOpen
          (𝕜 := ℝ)
          (f := V)
          (s := Set.Ioo (Q / 2) Q)
          (n := 0)
          isOpen_Ioo
      )

  exact
    hCriterion.2
      hRegularity

end

end Euclidean
end Bridge
end PrimeTensor
