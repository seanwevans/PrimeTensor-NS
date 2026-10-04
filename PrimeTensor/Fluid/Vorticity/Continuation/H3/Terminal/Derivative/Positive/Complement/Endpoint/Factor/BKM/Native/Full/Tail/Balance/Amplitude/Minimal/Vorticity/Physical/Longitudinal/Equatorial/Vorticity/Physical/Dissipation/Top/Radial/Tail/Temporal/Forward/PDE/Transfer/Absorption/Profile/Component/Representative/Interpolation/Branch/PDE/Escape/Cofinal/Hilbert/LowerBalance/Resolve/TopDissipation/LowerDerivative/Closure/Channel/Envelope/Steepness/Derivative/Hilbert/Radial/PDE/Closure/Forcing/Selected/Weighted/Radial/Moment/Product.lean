import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2

/-!
# Radial Fourier L² product-rule candidates for the selected forcing

Let `U(s)` be the selected positive-time mild spectral state and let `R(s)` be
the genuine H³ spectral encoding of its exact raw Fourier time derivative.

The previous checkpoints establish:

* every finite raw Fourier moment of `U(s)`;
* every positive integer raw Fourier moment of `R(s)`;
* exact deweighting of `R(s)` back to the projected RHS `∂ₜ û(s)`.

The generic radial forcing theorem therefore applies to both cross terms

    N(R,U)
and
    N(U,R)

at every finite radial order `m`.  This file packages their sum as the
canonical Fourier `L²` product-rule candidate

    |ξ|^m [N(R,U) + N(U,R)].

In particular, `m = 2` is the candidate derivative for the terminal `q F`
branch and `m = 4` is the candidate derivative for the terminal `q² F`
branch.

No quotient convergence is asserted here.  The next checkpoint can now focus
only on identifying the selected forcing difference quotient with these
already-constructed states.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingProductRuleRadial
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2600000

/-! ## Selected mild moments on the positive slab -/

/--
Every natural raw Fourier moment of the selected mild state at one point of
the positive terminal-half slab.
-/
theorem h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
    (p : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (s : Set.Icc (Q / 2) Q) :
    ∀ k : Fin 3,
      H3RawFourierMomentIntegrable
        (p : ℝ)
        (
          h3PreterminalSelectedUnitSpectralStateOnRadius
            hNS ht₀ hE hTail
            (h3SelectedProjectedRHSSlabRadius hE hQ hQR s)
            k
        ) := by

  intro k

  have hsPos :
      0 < (s : ℝ) := by
    have hhalf :
        0 < Q / 2 := by
      positivity
    exact
      lt_of_lt_of_le
        hhalf
        s.property.1

  have hsR :
      (s : ℝ)
        ≤
      h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    s.property.2.trans hQR.le

  have hNat :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
      p
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      hsPos hsR k

  unfold H3RawFourierMomentIntegrable

  unfold
    h3PreterminalSelectedUnitSpectralStateOnRadius

  simp only [
    h3SelectedProjectedRHSSlabRadius_coe,
    h3FourierMomentWeight_natCast
  ]

  exact hNat

/-! ## Cross-term radial L² packages -/

/--
The radial order-`m` left product-rule cross term `N(R,U)` belongs to Fourier
`L²`.
-/
theorem h3PreterminalSelectedForcingTimeDerivativeLeft_radialWeight_memLp2
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    let U : H3SpectralFinVectorState :=
      h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht₀ hE hTail
        (h3SelectedProjectedRHSSlabRadius hE hQ hQR s)
    let R : H3SpectralFinVectorState :=
      h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
        hNS ht₀ hE hTail hQ hQR s
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence
            R U i ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  dsimp only

  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht₀ hE hTail
      (h3SelectedProjectedRHSSlabRadius hE hQ hQR s)

  let R : H3SpectralFinVectorState :=
    h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
      hNS ht₀ hE hTail hQ hQR s

  let p : ℕ :=
    2 * (m + 1)

  have hp :
      1 ≤ p := by
    dsimp only [p]
    omega

  have hR :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (p : ℝ)
          (R k) := by
    intro k
    dsimp only [R]
    exact
      h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
        p hp
        hNS ht₀ hE hTail hQ hQR k s

  have hU :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (p : ℝ)
          (U k) := by
    dsimp only [U, p]
    exact
      h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
        (2 * (m + 1))
        hNS ht₀ hE hTail hQ hQR s

  exact
    h3RawFinLerayOuterProductDivergence_radialWeight_memLp2
      m R U i
      (by
        simpa only [p] using hR)
      (by
        simpa only [p] using hU)

/--
The radial order-`m` right product-rule cross term `N(U,R)` belongs to Fourier
`L²`.
-/
theorem h3PreterminalSelectedForcingTimeDerivativeRight_radialWeight_memLp2
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    let U : H3SpectralFinVectorState :=
      h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht₀ hE hTail
        (h3SelectedProjectedRHSSlabRadius hE hQ hQR s)
    let R : H3SpectralFinVectorState :=
      h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
        hNS ht₀ hE hTail hQ hQR s
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence
            U R i ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  dsimp only

  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht₀ hE hTail
      (h3SelectedProjectedRHSSlabRadius hE hQ hQR s)

  let R : H3SpectralFinVectorState :=
    h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
      hNS ht₀ hE hTail hQ hQR s

  let p : ℕ :=
    2 * (m + 1)

  have hp :
      1 ≤ p := by
    dsimp only [p]
    omega

  have hR :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (p : ℝ)
          (R k) := by
    intro k
    dsimp only [R]
    exact
      h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
        p hp
        hNS ht₀ hE hTail hQ hQR k s

  have hU :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (p : ℝ)
          (U k) := by
    dsimp only [U, p]
    exact
      h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
        (2 * (m + 1))
        hNS ht₀ hE hTail hQ hQR s

  exact
    h3RawFinLerayOuterProductDivergence_radialWeight_memLp2
      m U R i
      (by
        simpa only [p] using hU)
      (by
        simpa only [p] using hR)

/-! ## Canonical product-rule candidate -/

/--
Radial order-`m` selected forcing-time product-rule candidate

    |ξ|^m [N(R,U) + N(U,R)]

packaged as a genuine Fourier `L²` state.
-/
noncomputable def h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    H3FourierComplexL2 :=

  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht₀ hE hTail
      (h3SelectedProjectedRHSSlabRadius hE hQ hQR s)

  let R : H3SpectralFinVectorState :=
    h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
      hNS ht₀ hE hTail hQ hQR s

  (
    h3PreterminalSelectedForcingTimeDerivativeLeft_radialWeight_memLp2
      m hNS ht₀ hE hTail hQ hQR i s
  ).toLp
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence
          R U i ξ)
  +
  (
    h3PreterminalSelectedForcingTimeDerivativeRight_radialWeight_memLp2
      m hNS ht₀ hE hTail hQ hQR i s
  ).toLp
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence
          U R i ξ)

/--
The packaged product-rule candidate has exactly the expected raw Fourier
representative.
-/
theorem h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab_ae
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    let U : H3SpectralFinVectorState :=
      h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht₀ hE hTail
        (h3SelectedProjectedRHSSlabRadius hE hQ hQR s)
    let R : H3SpectralFinVectorState :=
      h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
        hNS ht₀ hE hTail hQ hQR s
    (
      (
        h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
          m hNS ht₀ hE hTail hQ hQR i s :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (
          h3RawFinLerayOuterProductDivergence
              R U i ξ
            +
          h3RawFinLerayOuterProductDivergence
              U R i ξ
        )) := by

  dsimp only

  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht₀ hE hTail
      (h3SelectedProjectedRHSSlabRadius hE hQ hQR s)

  let R : H3SpectralFinVectorState :=
    h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
      hNS ht₀ hE hTail hQ hQR s

  let L : H3FourierComplexL2 :=
    (
      h3PreterminalSelectedForcingTimeDerivativeLeft_radialWeight_memLp2
        m hNS ht₀ hE hTail hQ hQR i s
    ).toLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence
            R U i ξ)

  let D : H3FourierComplexL2 :=
    (
      h3PreterminalSelectedForcingTimeDerivativeRight_radialWeight_memLp2
        m hNS ht₀ hE hTail hQ hQR i s
    ).toLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence
            U R i ξ)

  have hL :
      ((L : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence
            R U i ξ) := by
    dsimp only [L]
    exact
      MemLp.coeFn_toLp
        (
          h3PreterminalSelectedForcingTimeDerivativeLeft_radialWeight_memLp2
            m hNS ht₀ hE hTail hQ hQR i s
        )

  have hD :
      ((D : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence
            U R i ξ) := by
    dsimp only [D]
    exact
      MemLp.coeFn_toLp
        (
          h3PreterminalSelectedForcingTimeDerivativeRight_radialWeight_memLp2
            m hNS ht₀ hE hTail hQ hQR i s
        )

  have hAdd :=
    MeasureTheory.Lp.coeFn_add
      L D

  unfold
    h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab

  filter_upwards [hL, hD, hAdd]
    with ξ hLξ hDξ hAddξ

  rw [hAddξ]
  simp only [Pi.add_apply]
  rw [hLξ, hDξ]

  ring

/-! ## Endpoint weights -/

/--
Order-two candidate, corresponding to the first weighted terminal forcing
`q F`.
-/
noncomputable def h3PreterminalSelectedForcingTimeDerivativeSecondRadialFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    H3FourierComplexL2 :=
  h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
    2 hNS ht₀ hE hTail hQ hQR i s

/--
Order-four candidate, corresponding to the second weighted terminal forcing
`q² F`.
-/
noncomputable def h3PreterminalSelectedForcingTimeDerivativeFourthRadialFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    H3FourierComplexL2 :=
  h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
    4 hNS ht₀ hE hTail hQ hQR i s

end

end Euclidean
end Bridge
end PrimeTensor
