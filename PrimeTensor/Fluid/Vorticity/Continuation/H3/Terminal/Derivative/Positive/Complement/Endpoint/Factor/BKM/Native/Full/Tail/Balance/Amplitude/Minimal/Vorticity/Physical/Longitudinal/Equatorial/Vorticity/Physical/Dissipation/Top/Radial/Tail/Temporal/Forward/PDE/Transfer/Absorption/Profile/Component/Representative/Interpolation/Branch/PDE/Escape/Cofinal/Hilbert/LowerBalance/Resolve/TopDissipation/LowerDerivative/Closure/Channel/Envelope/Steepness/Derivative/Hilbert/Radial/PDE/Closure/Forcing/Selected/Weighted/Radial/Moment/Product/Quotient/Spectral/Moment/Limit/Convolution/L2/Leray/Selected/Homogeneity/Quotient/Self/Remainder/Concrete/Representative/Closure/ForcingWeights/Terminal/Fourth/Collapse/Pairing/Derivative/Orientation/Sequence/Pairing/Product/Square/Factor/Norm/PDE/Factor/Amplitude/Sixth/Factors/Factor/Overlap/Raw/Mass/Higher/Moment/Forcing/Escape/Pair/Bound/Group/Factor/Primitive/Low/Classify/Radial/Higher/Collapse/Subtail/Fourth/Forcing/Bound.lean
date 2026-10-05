import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors.Factor.Overlap.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.Fourth.Forcing

/-!
# Bound the terminal q²-forcing derivative by two radial Leray channels

The preceding checkpoint identifies the actual terminal derivative

    d/dt (q² F_j)

with a fixed `(2π)^4` multiple of the radial-order-four product-rule state

    |ξ|⁴ [N(R,U)_j + N(U,R)_j].

This file removes the representative ambiguity and rewrites that state as the
sum of the two canonical radial Leray `L²` packages.  The generic finite Leray
estimate then gives a completely explicit bound by two finite order-five
convolution sums.

This is the last analytic step needed before finite-channel extraction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalFourthQForcingDerivativeBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQForcingDerivativeBound :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 1800000

/--
At every strict time, the terminal `q² F_j` derivative is bounded by the two
finite radial-Leray product-rule channels `N(R,U)` and `N(U,R)`.

Both selected spectral factors retain raw moment order ten, so each complete
order-four Leray package is controlled by order-five scalar convolution norms.
-/
theorem norm_deriv_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_le_two_radialLeray
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ∃ U R : H3SpectralFinVectorState,
      ∃ hU :
          ∀ k : Fin 3,
            H3RawFourierMomentIntegrable
              (((2 * (4 + 1) : ℕ) : ℝ))
              (U k),
      ∃ hR :
          ∀ k : Fin 3,
            H3RawFourierMomentIntegrable
              (((2 * (4 + 1) : ℕ) : ℝ))
              (R k),
        U =
          h3TerminalVelocitySpectralStateAt
            hH3 t
            ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
          ∧
        ‖deriv
            (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
              hH3 hClass j)
            t‖
          ≤
        ((2 * Real.pi) ^ 4 : ℝ)
          *
        (
          (
            ∑ k : Fin 3,
              2 *
                (
                  ∑ l : Fin 3,
                    (2 * Real.pi) *
                      ‖h3RawProductConvolutionRadialFourierL2
                          5
                          (R k) (U l)
                          (hR k) (hU l)‖
                )
          )
            +
          (
            ∑ k : Fin 3,
              2 *
                (
                  ∑ l : Fin 3,
                    (2 * Real.pi) *
                      ‖h3RawProductConvolutionRadialFourierL2
                          5
                          (U k) (R l)
                          (hU k) (hR l)‖
                )
          )
        ) := by

  obtain
    ⟨U, R, D, hU10, hR10, hUTerm, hDeriv, hDAE⟩ :=
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_deriv_exists_productRuleRepresentative
      hH3 hClass ht j

  let hU :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (4 + 1) : ℕ) : ℝ))
          (U k) := by
    intro k
    simpa using hU10 k

  let hR :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (4 + 1) : ℕ) : ℝ))
          (R k) := by
    intro k
    simpa using hR10 k

  let LRU : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2
      4 R U j hR hU

  let LUR : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2
      4 U R j hU hR

  have hLRUAE :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      4 R U j hR hU

  have hLURAE :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      4 U R j hU hR

  have hAddAE :=
    MeasureTheory.Lp.coeFn_add
      LRU LUR

  have hDEq :
      D = LRU + LUR := by

    apply MeasureTheory.Lp.ext

    filter_upwards [hDAE, hLRUAE, hLURAE, hAddAE]
      with ξ hDξ hLRUξ hLURξ hAddξ

    rw [hDξ, hAddξ]
    simp only [Pi.add_apply]
    rw [hLRUξ, hLURξ]

    ring

  have hLRU :
      ‖LRU‖
        ≤
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    5
                    (R k) (U l)
                    (hR k) (hU l)‖
          ) := by

    dsimp only [LRU]

    exact
      norm_h3RawFinLerayOuterProductDivergenceRadialFourierL2_le
        4 R U j hR hU

  have hLUR :
      ‖LUR‖
        ≤
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    5
                    (U k) (R l)
                    (hU k) (hR l)‖
          ) := by

    dsimp only [LUR]

    exact
      norm_h3RawFinLerayOuterProductDivergenceRadialFourierL2_le
        4 U R j hU hR

  have hDNorm :
      ‖D‖
        ≤
      (
        ∑ k : Fin 3,
          2 *
            (
              ∑ l : Fin 3,
                (2 * Real.pi) *
                  ‖h3RawProductConvolutionRadialFourierL2
                      5
                      (R k) (U l)
                      (hR k) (hU l)‖
            )
      )
        +
      (
        ∑ k : Fin 3,
          2 *
            (
              ∑ l : Fin 3,
                (2 * Real.pi) *
                  ‖h3RawProductConvolutionRadialFourierL2
                      5
                      (U k) (R l)
                      (hU k) (hR l)‖
            )
      ) := by

    rw [hDEq]

    exact
      (norm_add_le LRU LUR).trans
        (add_le_add hLRU hLUR)

  refine
    ⟨
      U,
      R,
      hU,
      hR,
      hUTerm,
      ?_
    ⟩

  rw [hDeriv, norm_smul]

  have hCoeff0 :
      0 ≤ ((2 * Real.pi) ^ 4 : ℝ) := by
    positivity

  rw [
    Real.norm_eq_abs,
    abs_of_nonneg hCoeff0
  ]

  exact
    mul_le_mul_of_nonneg_left
      hDNorm
      hCoeff0

end

end Euclidean
end Bridge
end PrimeTensor
