import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self

/-!
# Vanishing quadratic remainder in the selected Leray quotient

Write the selected spectral velocity difference quotient as

    D_h = R(x) + E_h,

where `R(x)` is the projected RHS at the base slab point and `E_h` is the
genuine spectral slope error.  Bilinearity gives

    N(D_h,D_h)
      = N(R,R) + N(E_h,R) + N(R,E_h) + N(E_h,E_h).

The preceding files already show that all three error channels tend strongly
to zero in every finite radial Fourier `L²` norm.  The `N(R,R)` term is fixed.
Therefore multiplication by the explicit quotient factor `h` forces the full
quadratic remainder to zero.

This file packages precisely that expanded `L²` remainder.  No new analytic
estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedSpectralSlopeQuadraticRemainder
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/--
The order-`m` radial `L²` package of the expanded quadratic quotient remainder

    h [N(R,R) + N(E_h,R) + N(R,E_h) + N(E_h,E_h)].
-/
noncomputable def h3PreterminalSelectedVelocitySpectralSlopeQuadraticRemainderRadialFourierL2
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ) :
    H3FourierComplexL2 := by

  let sx : Set.Icc (Q / 2) Q :=
    ⟨x, hx.1.le, hx.2.le⟩

  let R : H3SpectralFinVectorState :=
    h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
      hNS ht₀ hE hTail hQ hQR sx

  let hR :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (R r) :=
    fun r =>
      h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
        (2 * (m + 1)) (by omega)
        hNS ht₀ hE hTail hQ hQR r sx

  let RR : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2
      m R R i hR hR

  let ER : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left
      m hNS ht₀ hE hTail hQ hQR i hx R hR h

  let RE : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right
      m hNS ht₀ hE hTail hQ hQR i hx R hR h

  let EE : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Self
      m hNS ht₀ hE hTail hQ hQR i hx h

  exact
    h • (RR + ER + RE + EE)

/--
The expanded quadratic quotient remainder tends strongly to zero in every
finite radial Fourier `L²` norm.
-/
theorem tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeQuadraticRemainderRadialFourierL2_zero
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocitySpectralSlopeQuadraticRemainderRadialFourierL2
          m hNS ht₀ hE hTail hQ hQR i hx h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  let sx : Set.Icc (Q / 2) Q :=
    ⟨x, hx.1.le, hx.2.le⟩

  let R : H3SpectralFinVectorState :=
    h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
      hNS ht₀ hE hTail hQ hQR sx

  let hR :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (R r) :=
    fun r =>
      h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
        (2 * (m + 1)) (by omega)
        hNS ht₀ hE hTail hQ hQR r sx

  let RR : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2
      m R R i hR hR

  let ER : ℝ → H3FourierComplexL2 :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left
        m hNS ht₀ hE hTail hQ hQR i hx R hR h

  let RE : ℝ → H3FourierComplexL2 :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right
        m hNS ht₀ hE hTail hQ hQR i hx R hR h

  let EE : ℝ → H3FourierComplexL2 :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Self
        m hNS ht₀ hE hTail hQ hQR i hx h

  let Rem : ℝ → H3FourierComplexL2 :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeQuadraticRemainderRadialFourierL2
        m hNS ht₀ hE hTail hQ hQR i hx h

  let Bracket : ℝ → ℝ :=
    fun h =>
      ‖RR‖ + ‖ER h‖ + ‖RE h‖ + ‖EE h‖

  let Major : ℝ → ℝ :=
    fun h => |h| * Bracket h

  have hER0 :=
    tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left_projectedRHS_zero
      m hNS ht₀ hE hTail hQ hQR i hx

  change
    Tendsto
      (fun h : ℝ => ‖ER h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0)
    at hER0

  have hRE0 :=
    tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right_projectedRHS_zero
      m hNS ht₀ hE hTail hQ hQR i hx

  change
    Tendsto
      (fun h : ℝ => ‖RE h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0)
    at hRE0

  have hEE0 :=
    tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Self_zero
      m hNS ht₀ hE hTail hQ hQR i hx

  change
    Tendsto
      (fun h : ℝ => ‖EE h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0)
    at hEE0

  have hRR :
      Tendsto
        (fun _h : ℝ => ‖RR‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 ‖RR‖) :=
    tendsto_const_nhds

  have hBracket :
      Tendsto Bracket
        (𝓝[≠] (0 : ℝ))
        (𝓝 ‖RR‖) := by

    have hSum :=
      ((hRR.add hER0).add hRE0).add hEE0

    simpa only [
      Bracket,
      add_zero
    ] using hSum

  have hhZero :
      Tendsto
        (fun h : ℝ => h)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds

  have hAbsZero :
      Tendsto
        (fun h : ℝ => |h|)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hNorm :=
      (continuous_norm.tendsto (0 : ℝ)).comp hhZero

    change
      Tendsto
        (fun h : ℝ => |h|)
        (𝓝[≠] (0 : ℝ))
        (𝓝 ‖(0 : ℝ)‖)
      at hNorm

    simpa only [
      norm_zero
    ] using hNorm

  have hMajorTend :
      Tendsto Major
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hMul :=
      hAbsZero.mul hBracket

    simpa only [
      Major,
      zero_mul
    ] using hMul

  have hNonneg :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        0 ≤ ‖Rem h‖ :=
    Filter.Eventually.of_forall
      (fun h => norm_nonneg _)

  have hUpper :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        ‖Rem h‖ ≤ Major h := by

    filter_upwards with h

    have hSum :
        ‖RR + ER h + RE h + EE h‖
          ≤
        Bracket h := by

      calc
        ‖RR + ER h + RE h + EE h‖
            ≤
          ‖RR + ER h + RE h‖ + ‖EE h‖ :=
          norm_add_le _ _
        _ ≤
          (‖RR + ER h‖ + ‖RE h‖) + ‖EE h‖ := by
            exact
              add_le_add
                (norm_add_le _ _)
                le_rfl
        _ ≤
          ((‖RR‖ + ‖ER h‖) + ‖RE h‖) + ‖EE h‖ := by
            exact
              add_le_add
                (
                  add_le_add
                    (norm_add_le _ _)
                    le_rfl
                )
                le_rfl
        _ =
          Bracket h := by
            rfl

    dsimp only [Rem]

    unfold
      h3PreterminalSelectedVelocitySpectralSlopeQuadraticRemainderRadialFourierL2

    dsimp only [
      sx,
      R,
      hR,
      RR,
      ER,
      RE,
      EE
    ]

    rw [
      norm_smul,
      Real.norm_eq_abs
    ]

    exact
      mul_le_mul_of_nonneg_left
        hSum
        (abs_nonneg h)

  exact
    squeeze_zero'
      hNonneg
      hUpper
      hMajorTend

end

end Euclidean
end Bridge
end PrimeTensor
