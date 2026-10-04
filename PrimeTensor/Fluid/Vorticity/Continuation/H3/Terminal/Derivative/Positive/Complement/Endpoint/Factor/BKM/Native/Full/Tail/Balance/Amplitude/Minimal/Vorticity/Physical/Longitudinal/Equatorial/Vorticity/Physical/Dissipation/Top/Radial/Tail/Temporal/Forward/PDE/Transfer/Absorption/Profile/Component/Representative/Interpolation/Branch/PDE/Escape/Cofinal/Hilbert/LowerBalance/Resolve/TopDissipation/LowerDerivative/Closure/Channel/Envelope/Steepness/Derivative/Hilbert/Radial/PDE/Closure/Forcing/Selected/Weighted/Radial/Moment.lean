import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Bridge

/-!
# Arbitrary raw moments of the encoded selected projected RHS

The previous checkpoint packages

    |ξ|^m R̂_j

in Fourier `L²` at every finite radial order, where `R̂` is the exact selected
projected Navier--Stokes right-hand side and hence the raw Fourier time
derivative of the selected velocity.

The radial forcing bilinear theorem used by the final product-rule step asks
for weighted `L¹` moments of its H³ spectral inputs.  Rather than introduce a
new Euclidean Cauchy--Schwarz constant, reuse the exact H³ first-moment
embedding already present in the repository.

For `n ≥ 0`, encode the shifted raw state

    |ξ|^n R̂_j

as a genuine H³ spectral state.  Its H³ weighted amplitude is controlled by

    W₃² |ξ|^(2n) |R̂|²
      ≤
    4 [ |ξ|^(2n) |R̂|²
        + (2π)^8 |ξ|^(2n+8) |R̂|² ],

and both terms are provided by the arbitrary radial `L²` package at orders
`n` and `n+4`.

Applying the existing H³-to-first-Fourier-moment theorem to that shifted state
then gives

    ∫ |ξ|^(n+1) |R̂_j(ξ)| dξ < ∞.

Consequently the genuine H³ derivative carrier `R_H3` has every positive
integer raw Fourier moment.  In particular the sixth and tenth moments needed
by radial forcing orders two and four are now available.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedProjectedRHSMoments
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2800000

/-! ## Shifted H³ encoder -/

/--
The exact H³ weighted amplitude of the shifted raw derivative
`|ξ|^n R̂_i` belongs to Fourier `L²`.
-/
theorem h3PreterminalSelectedProjectedRHSShiftedWeightedH3_memLp2
    (n : ℕ)
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
    let F : H3FourierComplexL2 :=
      h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
        n hNS ht₀ hE hTail hQ hQR i s
    MemLp
      (fun ξ : H3FourierPoint3 =>
        (h3SobolevFrequencyWeight ξ : ℂ) * F ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  dsimp only

  let F : H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      n hNS ht₀ hE hTail hQ hQR i s

  let G : H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      (n + 4) hNS ht₀ hE hTail hQ hQR i s

  let C : ℝ :=
    (2 * Real.pi) ^ 8

  have hC0 :
      0 ≤ C := by
    dsimp only [C]
    positivity

  have hFInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖F ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp F).norm.integrable_sq

  have hGInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖G ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp G).norm.integrable_sq

  have hCGInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * ‖G ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    hGInt.const_mul C

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          4 * (‖F ξ‖ ^ 2 + C * ‖G ξ‖ ^ 2))
        (volume : Measure H3FourierPoint3) :=
    (hFInt.add hCGInt).const_mul 4

  have hWeightedMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          (h3SobolevFrequencyWeight ξ : ℂ) * F ξ)
        (volume : Measure H3FourierPoint3) :=
    (Complex.continuous_ofReal.comp
      continuous_h3SobolevFrequencyWeight).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable F)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖(h3SobolevFrequencyWeight ξ : ℂ) * F ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (
      hWeightedMeas.norm.aemeasurable.pow_const 2
    ).aestronglyMeasurable

  have hFn :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab_ae_eq_radial_projectedRHS
      n hNS ht₀ hE hTail hQ hQR i s

  have hGn :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab_ae_eq_radial_projectedRHS
      (n + 4) hNS ht₀ hE hTail hQ hQR i s

  have hWeightedInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖(h3SobolevFrequencyWeight ξ : ℂ) * F ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    refine
      Integrable.mono
        (f := fun ξ : H3FourierPoint3 =>
          ‖(h3SobolevFrequencyWeight ξ : ℂ) * F ξ‖ ^ 2)
        (g := fun ξ : H3FourierPoint3 =>
          4 * (‖F ξ‖ ^ 2 + C * ‖G ξ‖ ^ 2))
        hMajorInt
        hTargetMeas
        ?_

    filter_upwards [hFn, hGn]
      with ξ hFnξ hGnξ

    have hr0 :
        0 ≤ ‖ξ‖ :=
      norm_nonneg ξ

    have hW0 :
        0 ≤ h3SobolevFrequencyWeight ξ :=
      (h3SobolevFrequencyWeight_pos ξ).le

    have hPow :
        ‖ξ‖ ^ (n + 4)
          =
        ‖ξ‖ ^ 4 * ‖ξ‖ ^ n := by
      rw [pow_add]
      ring

    have hGnorm :
        ‖G ξ‖ ^ 2
          =
        ‖ξ‖ ^ 8 * ‖F ξ‖ ^ 2 := by

      dsimp only [F, G] at hFnξ hGnξ ⊢

      rw [hGnξ, hFnξ]

      simp only [
        norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg hr0 _)
      ]

      rw [hPow]

      ring

    have hPoly :=
      h3SobolevFrequencyWeightSq_le_four_mul_one_add_gradientSquare_fourth
        ξ

    have hQ4 :=
      h3FourierGradientSquare_fourth_eq_two_pi_eight_mul_norm_eight
        ξ

    have hPoint :
        ‖(h3SobolevFrequencyWeight ξ : ℂ) * F ξ‖ ^ 2
          ≤
        4 * (‖F ξ‖ ^ 2 + C * ‖G ξ‖ ^ 2) := by

      rw [
        norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg hW0,
        mul_pow,
        h3SobolevFrequencyWeight_sq
      ]

      have hF0 :
          0 ≤ ‖F ξ‖ ^ 2 :=
        sq_nonneg _

      calc
        h3SobolevFrequencyWeightSq ξ * ‖F ξ‖ ^ 2
            ≤
          (4 * (1 + h3FourierGradientSquare ξ ^ 4)) *
            ‖F ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            hPoly hF0
        _ =
          4 * (‖F ξ‖ ^ 2 + C * ‖G ξ‖ ^ 2) := by
          rw [hQ4, hGnorm]
          dsimp only [C]
          ring

    have hLeft0 :
        0 ≤
          ‖(h3SobolevFrequencyWeight ξ : ℂ) * F ξ‖ ^ 2 :=
      sq_nonneg _

    have hRight0 :
        0 ≤
          4 * (‖F ξ‖ ^ 2 + C * ‖G ξ‖ ^ 2) := by
      positivity

    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hPoint

  rw [
    memLp_two_iff_integrable_sq_norm
      hWeightedMeas
  ]

  exact hWeightedInt

/--
Genuine H³ spectral encoding of `|ξ|^n R̂_i`.
-/
noncomputable def h3PreterminalSelectedProjectedRHSShiftedH3SpectralScalarOnSlab
    (n : ℕ)
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
    H3SpectralScalarState :=
  let F : H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      n hNS ht₀ hE hTail hQ hQR i s
  (
    h3PreterminalSelectedProjectedRHSShiftedWeightedH3_memLp2
      n hNS ht₀ hE hTail hQ hQR i s
  ).toLp
    (fun ξ : H3FourierPoint3 =>
      (h3SobolevFrequencyWeight ξ : ℂ) * F ξ)

/--
The shifted encoder has the literal representative
`W₃(ξ) |ξ|^n R̂_i(ξ)`.
-/
theorem h3PreterminalSelectedProjectedRHSShiftedH3SpectralScalarOnSlab_ae
    (n : ℕ)
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
    let F : H3FourierComplexL2 :=
      h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
        n hNS ht₀ hE hTail hQ hQR i s
    (
      (
        h3PreterminalSelectedProjectedRHSShiftedH3SpectralScalarOnSlab
          n hNS ht₀ hE hTail hQ hQR i s :
        H3SpectralScalarState
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (h3SobolevFrequencyWeight ξ : ℂ) * F ξ) := by

  dsimp only

  unfold
    h3PreterminalSelectedProjectedRHSShiftedH3SpectralScalarOnSlab

  exact
    MemLp.coeFn_toLp
      (
        h3PreterminalSelectedProjectedRHSShiftedWeightedH3_memLp2
          n hNS ht₀ hE hTail hQ hQR i s
      )

/--
Deweighting the shifted H³ encoder recovers exactly the order-`n` radial raw
projected-RHS package.
-/
theorem h3SpectralScalarRawFourierL2_h3PreterminalSelectedProjectedRHSShiftedH3SpectralScalarOnSlab_eq
    (n : ℕ)
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
    h3SpectralScalarRawFourierL2
      (
        h3PreterminalSelectedProjectedRHSShiftedH3SpectralScalarOnSlab
          n hNS ht₀ hE hTail hQ hQR i s
      )
      =
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      n hNS ht₀ hE hTail hQ hQR i s := by

  let F : H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      n hNS ht₀ hE hTail hQ hQR i s

  let R : H3SpectralScalarState :=
    h3PreterminalSelectedProjectedRHSShiftedH3SpectralScalarOnSlab
      n hNS ht₀ hE hTail hQ hQR i s

  have hRaw :=
    h3SpectralScalarRawFourierL2_ae R

  have hEncoded :=
    h3PreterminalSelectedProjectedRHSShiftedH3SpectralScalarOnSlab_ae
      n hNS ht₀ hE hTail hQ hQR i s

  apply MeasureTheory.Lp.ext

  filter_upwards [hRaw, hEncoded]
    with ξ hRawξ hEncodedξ

  rw [hRawξ]

  unfold h3SpectralScalarRawFourier

  rw [hEncodedξ]

  rw [
    ← mul_assoc,
    h3SobolevFrequencyWeightInvComplex_mul_weight,
    one_mul
  ]

/-! ## Arbitrary positive integer moments of the true H³ derivative carrier -/

/--
The genuine H³ projected-RHS carrier has every positive integer raw Fourier
moment.
-/
theorem h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
    (p : ℕ)
    (hp : 1 ≤ p)
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
    H3RawFourierMomentIntegrable
      (p : ℝ)
      (
        h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab
          hNS ht₀ hE hTail hQ hQR i s
      ) := by

  let n : ℕ :=
    p - 1

  have hn :
      n + 1 = p := by
    dsimp only [n]
    omega

  let R0 : H3SpectralScalarState :=
    h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab
      hNS ht₀ hE hTail hQ hQR i s

  let Rn : H3SpectralScalarState :=
    h3PreterminalSelectedProjectedRHSShiftedH3SpectralScalarOnSlab
      n hNS ht₀ hE hTail hQ hQR i s

  let Fn : H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      n hNS ht₀ hE hTail hQ hQR i s

  let F0 : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht₀ hE hTail
      (h3SelectedProjectedRHSSlabRadius hE hQ hQR s)
      i

  have hRnEq :
      h3SpectralScalarRawFourierL2 Rn = Fn := by
    dsimp only [Rn, Fn]
    exact
      h3SpectralScalarRawFourierL2_h3PreterminalSelectedProjectedRHSShiftedH3SpectralScalarOnSlab_eq
        n hNS ht₀ hE hTail hQ hQR i s

  have hR0Eq :
      h3SpectralScalarRawFourierL2 R0 = F0 := by
    dsimp only [R0, F0]
    exact
      h3SpectralScalarRawFourierL2_h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_eq
        hNS ht₀ hE hTail hQ hQR i s

  have hRnRaw :=
    h3SpectralScalarRawFourierL2_ae Rn

  have hR0Raw :=
    h3SpectralScalarRawFourierL2_ae R0

  rw [hRnEq] at hRnRaw
  rw [hR0Eq] at hR0Raw

  have hFn :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab_ae_eq_radial_projectedRHS
      n hNS ht₀ hE hTail hQ hQR i s

  have hRelation :
      (fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier Rn ξ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) *
          h3SpectralScalarRawFourier R0 ξ) := by

    filter_upwards [hRnRaw, hR0Raw, hFn]
      with ξ hRnξ hR0ξ hFnξ

    calc
      h3SpectralScalarRawFourier Rn ξ
          =
        Fn ξ :=
        hRnξ.symm
      _ =
        ((‖ξ‖ ^ n : ℝ) : ℂ) * F0 ξ := by
        dsimp only [Fn, F0] at hFnξ ⊢
        exact hFnξ
      _ =
        ((‖ξ‖ ^ n : ℝ) : ℂ) *
          h3SpectralScalarRawFourier R0 ξ := by
        rw [hR0ξ]

  have hFirst :=
    h3SpectralScalarRawFourier_firstMoment_integrable
      Rn

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ p *
            ‖h3SpectralScalarRawFourier R0 ξ‖)
        (volume : Measure H3FourierPoint3) := by

    refine hFirst.congr ?_

    filter_upwards [hRelation]
      with ξ hRelξ

    rw [hRelξ, norm_mul]

    simp only [
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg ξ) n)
    ]

    rw [← hn, pow_succ']
    ring

  unfold H3RawFourierMomentIntegrable

  dsimp only [R0] at hMoment ⊢

  simpa only [
    h3FourierMomentWeight_natCast
  ] using hMoment

/--
Sixth raw Fourier moment of every coordinate of the genuine H³ projected-RHS
state.
-/
theorem h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab_sixthMoment_integrable
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
        (6 : ℝ)
        (
          h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
            hNS ht₀ hE hTail hQ hQR s k
        ) := by

  intro k

  exact
    h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
      6 (by norm_num)
      hNS ht₀ hE hTail hQ hQR k s

/--
Tenth raw Fourier moment of every coordinate of the genuine H³ projected-RHS
state.
-/
theorem h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab_tenthMoment_integrable
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
        (10 : ℝ)
        (
          h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
            hNS ht₀ hE hTail hQ hQR s k
        ) := by

  intro k

  exact
    h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
      10 (by norm_num)
      hNS ht₀ hE hTail hQ hQR k s

end

end Euclidean
end Bridge
end PrimeTensor
