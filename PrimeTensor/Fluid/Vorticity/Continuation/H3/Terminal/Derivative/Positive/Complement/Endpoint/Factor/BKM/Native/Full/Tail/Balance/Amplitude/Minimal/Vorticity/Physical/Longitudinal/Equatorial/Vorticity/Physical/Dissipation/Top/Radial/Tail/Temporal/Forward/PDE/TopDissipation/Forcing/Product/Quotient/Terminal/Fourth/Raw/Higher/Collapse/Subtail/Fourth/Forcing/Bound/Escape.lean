import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher.Collapse.Subtail.Fourth.Forcing.Bound
import Mathlib.Data.Finset.Max
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Freeze one fourth-q forcing-derivative radial product channel

The actual terminal derivative `d/dt(q² F_j)` is bounded by two finite
radial-Leray sums, one for each product-rule orientation

    N(R,U),   N(U,R).

At each strict time choose one admissible pair of spectral states `U,R`
supplied by the preceding representative/bound theorem.  There are then only

    2 × 3 × 3 = 18

scalar order-five radial product-convolution channels.

This file packages the chosen data, bounds the complete derivative envelope by
one universal positive coefficient times a maximizing channel, and freezes one
orientation and coordinate pair along a cofinal subsequence whenever the
terminal forcing derivative norm tends to `+∞`.

No new PDE estimate occurs here; this is a finite-channel extraction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalFourthQForcingDerivativeEscape
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQForcingDerivativeEscape :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 2200000

/-- Chosen spectral input data for the terminal fourth-q forcing derivative. -/
structure H3TerminalFourthQForcingDerivativeLerayData where
  U : H3SpectralFinVectorState
  R : H3SpectralFinVectorState
  hU :
    ∀ k : Fin 3,
      H3RawFourierMomentIntegrable
        (((2 * (4 + 1) : ℕ) : ℝ))
        (U k)
  hR :
    ∀ k : Fin 3,
      H3RawFourierMomentIntegrable
        (((2 * (4 + 1) : ℕ) : ℝ))
        (R k)

/--
At each strict time there is an admissible Leray datum whose two orientation
sums bound the actual terminal fourth-q forcing derivative.
-/
theorem exists_h3TerminalFourthQForcingDerivativeLerayData_bound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ∃ d : H3TerminalFourthQForcingDerivativeLerayData,
      d.U =
        h3TerminalVelocitySpectralStateAt
          hH3 t
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
        ∧
      (∀ i : Fin 3,
        (
          (
            h3SpectralScalarRawFourierL2 (d.R i) :
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
                h3SpectralScalarRawFourierL2 (d.U i) :
                H3FourierComplexL2
              ) ξ
            )
            -
          h3RawFinLerayOuterProductDivergence
            d.U d.U i ξ))
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
                        (d.R k) (d.U l)
                        (d.hR k) (d.hU l)‖
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
                        (d.U k) (d.R l)
                        (d.hU k) (d.hR l)‖
              )
        )
      ) := by

  have hBoundRep :=
    norm_deriv_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_le_two_radialLeray
      hH3 hClass ht j

  let U : H3SpectralFinVectorState :=
    Classical.choose hBoundRep

  have hAfterU :=
    Classical.choose_spec hBoundRep

  let R : H3SpectralFinVectorState :=
    Classical.choose hAfterU

  have hAfterR :=
    Classical.choose_spec hAfterU

  let hU :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (4 + 1) : ℕ) : ℝ))
          (U k) :=
    Classical.choose hAfterR

  have hAfterHU :=
    Classical.choose_spec hAfterR

  let hR :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (4 + 1) : ℕ) : ℝ))
          (R k) :=
    Classical.choose hAfterHU

  have hData :=
    Classical.choose_spec hAfterHU

  have hUTerm :
      U =
        h3TerminalVelocitySpectralStateAt
          hH3 t
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ :=
    hData.1

  have hRPDE :=
    hData.2.1

  have hBound :=
    hData.2.2

  exact
    ⟨
      {
        U := U
        R := R
        hU := hU
        hR := hR
      },
      hUTerm,
      hRPDE,
      hBound
    ⟩

/-- Canonical choice of one admissible product-rule Leray datum at a strict time. -/
noncomputable def h3TerminalFourthQForcingDerivativeLerayDataAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    H3TerminalFourthQForcingDerivativeLerayData :=
  Classical.choose
    (exists_h3TerminalFourthQForcingDerivativeLerayData_bound
      hH3 hClass ht j)

/-- The canonical chosen datum retains the quantitative derivative bound. -/
theorem norm_deriv_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_le_chosenLerayData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let d :=
      h3TerminalFourthQForcingDerivativeLerayDataAt
        hH3 hClass ht j
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
                      (d.R k) (d.U l)
                      (d.hR k) (d.hU l)‖
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
                      (d.U k) (d.R l)
                      (d.hU k) (d.hR l)‖
            )
      )
    ) := by

  dsimp only

  exact
    (Classical.choose_spec
      (exists_h3TerminalFourthQForcingDerivativeLerayData_bound
        hH3 hClass ht j)).2.2

/--
The canonical chosen product-rule datum uses exactly the terminal physical
velocity state in its `U` slot.  The `R` slot remains the selected
projected-RHS state.
-/
theorem h3TerminalFourthQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    (
      h3TerminalFourthQForcingDerivativeLerayDataAt
        hH3 hClass ht j
    ).U
      =
    h3TerminalVelocitySpectralStateAt
      hH3 t
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ := by

  exact
    (Classical.choose_spec
      (exists_h3TerminalFourthQForcingDerivativeLerayData_bound
        hH3 hClass ht j)).1

/--
The chosen projected-RHS slot retains the exact unit-viscosity raw Fourier PDE.
-/
theorem h3TerminalFourthQForcingDerivativeLerayDataAt_R_rawFourier_ae_eq_unitPDE
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) :
    let d :=
      h3TerminalFourthQForcingDerivativeLerayDataAt
        hH3 hClass ht j
    (
      (
        h3SpectralScalarRawFourierL2 (d.R i) :
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
            h3SpectralScalarRawFourierL2 (d.U i) :
            H3FourierComplexL2
          ) ξ
        )
        -
      h3RawFinLerayOuterProductDivergence
        d.U d.U i ξ) := by

  dsimp only

  exact
    (Classical.choose_spec
      (exists_h3TerminalFourthQForcingDerivativeLerayData_bound
        hH3 hClass ht j)).2.1 i

/--
One of the 18 scalar product-rule channels.  Orientation `0` is `N(R,U)`;
orientation `1` is `N(U,R)`.
-/
noncomputable def h3TerminalFourthQForcingDerivativeRadialProductNormAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) : ℝ :=
  let d :=
    h3TerminalFourthQForcingDerivativeLerayDataAt
      hH3 hClass ht j
  if o = 0 then
    ‖h3RawProductConvolutionRadialFourierL2
        5
        (d.R k) (d.U l)
        (d.hR k) (d.hU l)‖
  else
    ‖h3RawProductConvolutionRadialFourierL2
        5
        (d.U k) (d.R l)
        (d.hU k) (d.hR l)‖

theorem h3TerminalFourthQForcingDerivativeRadialProductNormAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    0 ≤
      h3TerminalFourthQForcingDerivativeRadialProductNormAt
        hH3 hClass ht j o k l := by

  unfold h3TerminalFourthQForcingDerivativeRadialProductNormAt

  split <;> exact norm_nonneg _

/-- Named complete two-orientation radial-Leray envelope. -/
noncomputable def h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) : ℝ :=
  let d :=
    h3TerminalFourthQForcingDerivativeLerayDataAt
      hH3 hClass ht j
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
                    (d.R k) (d.U l)
                    (d.hR k) (d.hU l)‖
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
                    (d.U k) (d.R l)
                    (d.hU k) (d.hR l)‖
          )
    )
  )

theorem h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    0 ≤
      h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt
        hH3 hClass ht j := by

  unfold h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt
  dsimp only

  apply mul_nonneg
  · positivity

  apply add_nonneg

  · apply Finset.sum_nonneg
    intro k hk
    apply mul_nonneg
    · norm_num
    apply Finset.sum_nonneg
    intro l hl
    exact
      mul_nonneg
        (by positivity)
        (norm_nonneg _)

  · apply Finset.sum_nonneg
    intro k hk
    apply mul_nonneg
    · norm_num
    apply Finset.sum_nonneg
    intro l hl
    exact
      mul_nonneg
        (by positivity)
        (norm_nonneg _)

/-- The actual derivative norm is bounded by the named chosen-data envelope. -/
theorem norm_deriv_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_le_radialLerayEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ‖deriv
        (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j)
        t‖
      ≤
    h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt
      hH3 hClass ht j := by

  simpa only [
    h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt
  ] using
    norm_deriv_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_le_chosenLerayData
      hH3 hClass ht j

/--
Derivative-norm escape forces escape of the named two-orientation radial-Leray
envelope on the same sequence.
-/
theorem h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt_tendstoAtTop_of_deriv_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hDerivTop :
      Tendsto
        (
          fun n : ℕ =>
            ‖deriv
              (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
                hH3 hClass j)
              (τ n)‖
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt
            hH3 hClass (hτ n) j
      )
      atTop
      atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        M
          ≤
        ‖deriv
          (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
            hH3 hClass j)
          (τ n)‖ :=
    hDerivTop.eventually
      (eventually_ge_atTop M)

  filter_upwards [hLarge] with n hn

  exact
    hn.trans
      (
        norm_deriv_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_le_radialLerayEnvelope
          hH3 hClass (hτ n) j
      )

/--
Universal positive coefficient bounding all eighteen product-rule channels by
one maximizing channel.
-/
noncomputable def h3TerminalFourthQForcingDerivativeFixedChannelCoefficient : ℝ :=
  ((2 * Real.pi) ^ 4 : ℝ) * 36 * (2 * Real.pi)

theorem h3TerminalFourthQForcingDerivativeFixedChannelCoefficient_pos :
    0 < h3TerminalFourthQForcingDerivativeFixedChannelCoefficient := by
  unfold h3TerminalFourthQForcingDerivativeFixedChannelCoefficient
  positivity

/--
At each strict time the complete two-orientation derivative envelope is
bounded by one universal positive coefficient times one of its eighteen scalar
radial product channels.
-/
theorem exists_channel_h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt_le_fixedCoefficient_mul_productNorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ∃ o : Fin 2,
      ∃ k l : Fin 3,
        h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt
            hH3 hClass ht j
          ≤
        h3TerminalFourthQForcingDerivativeFixedChannelCoefficient
          *
        h3TerminalFourthQForcingDerivativeRadialProductNormAt
          hH3 hClass ht j o k l := by

  classical

  let f : Fin 2 × Fin 3 × Fin 3 → ℝ :=
    fun p =>
      h3TerminalFourthQForcingDerivativeRadialProductNormAt
        hH3 hClass ht j p.1 p.2.1 p.2.2

  have hUnivNonempty :
      (Finset.univ : Finset (Fin 2 × Fin 3 × Fin 3)).Nonempty := by
    exact
      ⟨
        (0, 0, 0),
        Finset.mem_univ _
      ⟩

  obtain
    ⟨p, _hpMem, hpMax⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (Fin 2 × Fin 3 × Fin 3))
      f
      hUnivNonempty

  refine
    ⟨
      p.1,
      p.2.1,
      p.2.2,
      ?_
    ⟩

  let d :=
    h3TerminalFourthQForcingDerivativeLerayDataAt
      hH3 hClass ht j

  have hRU :
      (
        ∑ k : Fin 3,
          2 *
            (
              ∑ l : Fin 3,
                (2 * Real.pi) *
                  ‖h3RawProductConvolutionRadialFourierL2
                      5
                      (d.R k) (d.U l)
                      (d.hR k) (d.hU l)‖
            )
      )
        ≤
      18 * ((2 * Real.pi) * f p) := by

    have hInner :
        ∀ k : Fin 3,
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    5
                    (d.R k) (d.U l)
                    (d.hR k) (d.hU l)‖
          )
            ≤
          3 * ((2 * Real.pi) * f p) := by

      intro k

      calc
        (
          ∑ l : Fin 3,
            (2 * Real.pi) *
              ‖h3RawProductConvolutionRadialFourierL2
                  5
                  (d.R k) (d.U l)
                  (d.hR k) (d.hU l)‖
        )
            ≤
          ((Finset.univ : Finset (Fin 3)).card : ℕ)
            •
          ((2 * Real.pi) * f p) := by

              exact
                Finset.sum_le_card_nsmul
                  (Finset.univ : Finset (Fin 3))
                  (fun l : Fin 3 =>
                    (2 * Real.pi) *
                      ‖h3RawProductConvolutionRadialFourierL2
                          5
                          (d.R k) (d.U l)
                          (d.hR k) (d.hU l)‖)
                  ((2 * Real.pi) * f p)
                  (fun l hl =>
                    mul_le_mul_of_nonneg_left
                      (
                        by
                          have hMax :=
                            hpMax
                              (0, k, l)
                              (Finset.mem_univ _)
                          simpa [
                            f,
                            h3TerminalFourthQForcingDerivativeRadialProductNormAt,
                            d
                          ] using hMax
                      )
                      (by positivity))

        _ = 3 * ((2 * Real.pi) * f p) := by
              norm_num [nsmul_eq_mul]

    calc
      (
        ∑ k : Fin 3,
          2 *
            (
              ∑ l : Fin 3,
                (2 * Real.pi) *
                  ‖h3RawProductConvolutionRadialFourierL2
                      5
                      (d.R k) (d.U l)
                      (d.hR k) (d.hU l)‖
            )
      )
          ≤
        ((Finset.univ : Finset (Fin 3)).card : ℕ)
          •
        (2 * (3 * ((2 * Real.pi) * f p))) := by

            exact
              Finset.sum_le_card_nsmul
                (Finset.univ : Finset (Fin 3))
                (fun k : Fin 3 =>
                  2 *
                    (
                      ∑ l : Fin 3,
                        (2 * Real.pi) *
                          ‖h3RawProductConvolutionRadialFourierL2
                              5
                              (d.R k) (d.U l)
                              (d.hR k) (d.hU l)‖
                    ))
                (2 * (3 * ((2 * Real.pi) * f p)))
                (fun k hk =>
                  mul_le_mul_of_nonneg_left
                    (hInner k)
                    (by norm_num))
      _ = 18 * ((2 * Real.pi) * f p) := by
            norm_num [nsmul_eq_mul]
            ring

  have hUR :
      (
        ∑ k : Fin 3,
          2 *
            (
              ∑ l : Fin 3,
                (2 * Real.pi) *
                  ‖h3RawProductConvolutionRadialFourierL2
                      5
                      (d.U k) (d.R l)
                      (d.hU k) (d.hR l)‖
            )
      )
        ≤
      18 * ((2 * Real.pi) * f p) := by

    have hInner :
        ∀ k : Fin 3,
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    5
                    (d.U k) (d.R l)
                    (d.hU k) (d.hR l)‖
          )
            ≤
          3 * ((2 * Real.pi) * f p) := by

      intro k

      calc
        (
          ∑ l : Fin 3,
            (2 * Real.pi) *
              ‖h3RawProductConvolutionRadialFourierL2
                  5
                  (d.U k) (d.R l)
                  (d.hU k) (d.hR l)‖
        )
            ≤
          ((Finset.univ : Finset (Fin 3)).card : ℕ)
            •
          ((2 * Real.pi) * f p) := by

              exact
                Finset.sum_le_card_nsmul
                  (Finset.univ : Finset (Fin 3))
                  (fun l : Fin 3 =>
                    (2 * Real.pi) *
                      ‖h3RawProductConvolutionRadialFourierL2
                          5
                          (d.U k) (d.R l)
                          (d.hU k) (d.hR l)‖)
                  ((2 * Real.pi) * f p)
                  (fun l hl =>
                    mul_le_mul_of_nonneg_left
                      (
                        by
                          have hMax :=
                            hpMax
                              (1, k, l)
                              (Finset.mem_univ _)
                          simpa [
                            f,
                            h3TerminalFourthQForcingDerivativeRadialProductNormAt,
                            d
                          ] using hMax
                      )
                      (by positivity))

        _ = 3 * ((2 * Real.pi) * f p) := by
              norm_num [nsmul_eq_mul]

    calc
      (
        ∑ k : Fin 3,
          2 *
            (
              ∑ l : Fin 3,
                (2 * Real.pi) *
                  ‖h3RawProductConvolutionRadialFourierL2
                      5
                      (d.U k) (d.R l)
                      (d.hU k) (d.hR l)‖
            )
      )
          ≤
        ((Finset.univ : Finset (Fin 3)).card : ℕ)
          •
        (2 * (3 * ((2 * Real.pi) * f p))) := by

            exact
              Finset.sum_le_card_nsmul
                (Finset.univ : Finset (Fin 3))
                (fun k : Fin 3 =>
                  2 *
                    (
                      ∑ l : Fin 3,
                        (2 * Real.pi) *
                          ‖h3RawProductConvolutionRadialFourierL2
                              5
                              (d.U k) (d.R l)
                              (d.hU k) (d.hR l)‖
                    ))
                (2 * (3 * ((2 * Real.pi) * f p)))
                (fun k hk =>
                  mul_le_mul_of_nonneg_left
                    (hInner k)
                    (by norm_num))
      _ = 18 * ((2 * Real.pi) * f p) := by
            norm_num [nsmul_eq_mul]
            ring

  unfold h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt
  dsimp only [d]

  change
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
                        (d.R k) (d.U l)
                        (d.hR k) (d.hU l)‖
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
                        (d.U k) (d.R l)
                        (d.hU k) (d.hR l)‖
              )
        )
      )
      ≤
    h3TerminalFourthQForcingDerivativeFixedChannelCoefficient
      *
    f p

  calc
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
                        (d.R k) (d.U l)
                        (d.hR k) (d.hU l)‖
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
                        (d.U k) (d.R l)
                        (d.hU k) (d.hR l)‖
              )
        )
      )
        ≤
      ((2 * Real.pi) ^ 4 : ℝ)
        *
      (
        18 * ((2 * Real.pi) * f p)
          +
        18 * ((2 * Real.pi) * f p)
      ) := by
        exact
          mul_le_mul_of_nonneg_left
            (add_le_add hRU hUR)
            (by positivity)
    _ =
      h3TerminalFourthQForcingDerivativeFixedChannelCoefficient
        *
      f p := by
        unfold h3TerminalFourthQForcingDerivativeFixedChannelCoefficient
        ring

/--
If the terminal `q² F_j` derivative norm escapes, a cofinal subsequence freezes
one product-rule orientation and one coordinate pair whose order-five radial
product-convolution norm also escapes.
-/
theorem exists_fixed_orientation_pair_subsequence_of_h3TerminalFourthQForcingDerivative_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hDerivTop :
      Tendsto
        (
          fun n : ℕ =>
            ‖deriv
              (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
                hH3 hClass j)
              (τ n)‖
        )
        atTop
        atTop) :
    ∃ o : Fin 2,
      ∃ k l : Fin 3,
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n)
            ∧
          Tendsto s atTop atTop
            ∧
          Tendsto
            (fun n : ℕ => τ (s n))
            atTop
            (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalFourthQForcingDerivativeRadialProductNormAt
                  hH3 hClass (hτ (s n)) j o k l
            )
            atTop
            atTop := by

  classical

  have hEnvelopeTop :=
    h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt_tendstoAtTop_of_deriv_tendstoAtTop
      hH3 hClass j τ hτ hDerivTop

  have hChoice :
      ∀ n : ℕ,
        ∃ p : Fin 2 × Fin 3 × Fin 3,
          h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt
              hH3 hClass (hτ n) j
            ≤
          h3TerminalFourthQForcingDerivativeFixedChannelCoefficient
            *
          h3TerminalFourthQForcingDerivativeRadialProductNormAt
            hH3 hClass (hτ n) j p.1 p.2.1 p.2.2 := by

    intro n

    obtain
      ⟨o, k, l, hBound⟩ :=
      exists_channel_h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt_le_fixedCoefficient_mul_productNorm
        hH3 hClass (hτ n) j

    exact
      ⟨
        (o, k, l),
        hBound
      ⟩

  choose p hp using hChoice

  have hCPos :
      0 < h3TerminalFourthQForcingDerivativeFixedChannelCoefficient :=
    h3TerminalFourthQForcingDerivativeFixedChannelCoefficient_pos

  have hChosenTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeRadialProductNormAt
              hH3 hClass (hτ n) j
              (p n).1 (p n).2.1 (p n).2.2
        )
        atTop
        atTop := by

    refine tendsto_atTop.2 ?_

    intro M

    let M0 : ℝ :=
      max M 0

    have hMLe :
        M ≤ M0 := by
      dsimp only [M0]
      exact le_max_left M 0

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          h3TerminalFourthQForcingDerivativeFixedChannelCoefficient * M0
            <
          h3TerminalFourthQForcingDerivativeRadialLerayEnvelopeAt
            hH3 hClass (hτ n) j :=
      hEnvelopeTop.eventually
        (
          eventually_gt_atTop
            (
              h3TerminalFourthQForcingDerivativeFixedChannelCoefficient * M0
            )
        )

    filter_upwards [hLarge] with n hn

    have hScaled :
        h3TerminalFourthQForcingDerivativeFixedChannelCoefficient * M0
          <
        h3TerminalFourthQForcingDerivativeFixedChannelCoefficient
          *
        h3TerminalFourthQForcingDerivativeRadialProductNormAt
          hH3 hClass (hτ n) j
          (p n).1 (p n).2.1 (p n).2.2 :=
      lt_of_lt_of_le
        hn
        (hp n)

    have hM0Lt :
        M0
          <
        h3TerminalFourthQForcingDerivativeRadialProductNormAt
          hH3 hClass (hτ n) j
          (p n).1 (p n).2.1 (p n).2.2 := by

      by_contra hNot

      have hReverse :
          h3TerminalFourthQForcingDerivativeRadialProductNormAt
              hH3 hClass (hτ n) j
              (p n).1 (p n).2.1 (p n).2.2
            ≤
          M0 :=
        le_of_not_gt hNot

      have hScaledReverse :
          h3TerminalFourthQForcingDerivativeFixedChannelCoefficient
              *
            h3TerminalFourthQForcingDerivativeRadialProductNormAt
              hH3 hClass (hτ n) j
              (p n).1 (p n).2.1 (p n).2.2
            ≤
          h3TerminalFourthQForcingDerivativeFixedChannelCoefficient * M0 :=
        mul_le_mul_of_nonneg_left
          hReverse
          hCPos.le

      exact
        (not_lt_of_ge hScaledReverse)
          hScaled

    exact
      le_of_lt
        (
          lt_of_le_of_lt
            hMLe
            hM0Lt
        )

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q : Fin 2 × Fin 3 × Fin 3,
          p n = q :=
    Frequently.of_forall
      (
        fun n =>
          ⟨
            p n,
            rfl
          ⟩
      )

  obtain
    ⟨q, hFrequently⟩ :=
    (Filter.frequently_exists).1
      hFrequentlySome

  obtain
    ⟨s, hMono, hFixed⟩ :=
    extraction_of_frequently_atTop
      hFrequently

  have hs :
      ∀ n : ℕ,
        n ≤ s n := by
    intro n
    exact hMono.le_apply

  have hsTop :
      Tendsto s atTop atTop :=
    hMono.tendsto_atTop

  have hTauSub :
      Tendsto
        (fun n : ℕ => τ (s n))
        atTop
        (𝓝 T) :=
    hTauTendsto.comp
      hsTop

  have hChannelTopBeforeRewrite :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeRadialProductNormAt
              hH3 hClass (hτ (s n)) j
              (p (s n)).1
              (p (s n)).2.1
              (p (s n)).2.2
        )
        atTop
        atTop :=
    hChosenTop.comp
      hsTop

  have hChannelTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeRadialProductNormAt
              hH3 hClass (hτ (s n)) j
              q.1 q.2.1 q.2.2
        )
        atTop
        atTop := by

    simpa only [hFixed] using
      hChannelTopBeforeRewrite

  exact
    ⟨
      q.1,
      q.2.1,
      q.2.2,
      s,
      hs,
      hsTop,
      hTauSub,
      hChannelTop
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
