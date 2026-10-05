import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.Representative

/-!
# Bound the terminal q-forcing derivative by two radial Leray channels

The preceding checkpoint identifies the actual terminal derivative

    d/dt (q F_j)

with a fixed `(2π)^2` multiple of the radial-order-two product-rule state

    |ξ|² [N(R,U)_j + N(U,R)_j].

This file rewrites that state as the sum of the two canonical radial Leray
`L²` packages.  The generic finite Leray estimate then bounds the derivative by
two finite order-three convolution sums.

This is the lower-order analogue of the already closed fourth-q bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalSecondQForcingDerivativeBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalSecondQForcingDerivativeBound :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 1800000

/--
At every strict time, the terminal `q F_j` derivative is bounded by the two
finite radial-Leray product-rule channels `N(R,U)` and `N(U,R)`.

Both selected spectral factors retain raw moment order six, so each complete
order-two Leray package is controlled by order-three scalar convolution norms.
-/
theorem norm_deriv_h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_le_two_radialLeray
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
              (((2 * (2 + 1) : ℕ) : ℝ))
              (U k),
      ∃ hR :
          ∀ k : Fin 3,
            H3RawFourierMomentIntegrable
              (((2 * (2 + 1) : ℕ) : ℝ))
              (R k),
        U =
          h3TerminalVelocitySpectralStateAt
            hH3 t
            ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
          ∧
        (∀ i : Fin 3,
          (
            (
              h3SpectralScalarRawFourierL2 (R i) :
              H3FourierComplexL2
            ) :
            H3FourierPoint3 → ℂ
          )
            =ᵐ[(volume : Measure H3FourierPoint3)]
          (fun ξ : H3FourierPoint3 =>
            -(h3FourierGradientSquare ξ : ℂ)
                *
              (
                (
                  h3SpectralScalarRawFourierL2 (U i) :
                  H3FourierComplexL2
                ) ξ
              )
              -
            h3RawFinLerayOuterProductDivergence
              U U i ξ))
          ∧
        ‖deriv
            (h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
              hH3 hClass j)
            t‖
          ≤
        ((2 * Real.pi) ^ 2 : ℝ)
          *
        (
          (
            ∑ k : Fin 3,
              2 *
                (
                  ∑ l : Fin 3,
                    (2 * Real.pi) *
                      ‖h3RawProductConvolutionRadialFourierL2
                          3
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
                          3
                          (U k) (R l)
                          (hU k) (hR l)‖
                )
          )
        ) := by

  have hRep :=
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_deriv_exists_productRuleRepresentative
      hH3 hClass ht j

  let U : H3SpectralFinVectorState :=
    Classical.choose hRep

  have hAfterU :=
    Classical.choose_spec hRep

  let R : H3SpectralFinVectorState :=
    Classical.choose hAfterU

  have hAfterR :=
    Classical.choose_spec hAfterU

  let D : H3FourierComplexL2 :=
    Classical.choose hAfterR

  have hData :=
    Classical.choose_spec hAfterR

  have hU6 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (6 : ℝ)
          (U k) :=
    hData.1

  have hR6 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (6 : ℝ)
          (R k) :=
    hData.2.1

  have hUTerm :
      U =
        h3TerminalVelocitySpectralStateAt
          hH3 t
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ :=
    hData.2.2.1

  have hRPDE :=
    hData.2.2.2.1

  have hDeriv :=
    hData.2.2.2.2.1

  have hDAE :=
    hData.2.2.2.2.2

  let hU :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (2 + 1) : ℕ) : ℝ))
          (U k) := by
    intro k
    simpa using hU6 k

  let hR :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (2 + 1) : ℕ) : ℝ))
          (R k) := by
    intro k
    simpa using hR6 k

  let LRU : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2
      2 R U j hR hU

  let LUR : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2
      2 U R j hU hR

  have hLRUAE :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      2 R U j hR hU

  have hLURAE :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      2 U R j hU hR

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
                    3
                    (R k) (U l)
                    (hR k) (hU l)‖
          ) := by

    dsimp only [LRU]

    exact
      norm_h3RawFinLerayOuterProductDivergenceRadialFourierL2_le
        2 R U j hR hU

  have hLUR :
      ‖LUR‖
        ≤
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    3
                    (U k) (R l)
                    (hU k) (hR l)‖
          ) := by

    dsimp only [LUR]

    exact
      norm_h3RawFinLerayOuterProductDivergenceRadialFourierL2_le
        2 U R j hU hR

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
                      3
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
                      3
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
      hRPDE,
      ?_
    ⟩

  rw [hDeriv, norm_smul]

  have hCoeff0 :
      0 ≤ ((2 * Real.pi) ^ 2 : ℝ) := by
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
