import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Selected
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Truncation.Selected
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Round.Trip

/-!
# Encode the selected projected RHS as a genuine H³ spectral state

The previous checkpoint exposed the exact raw Fourier vector derivative

    d/dt û = R̂,

where `R̂` is the selected projected Navier--Stokes right-hand side.

The finite nonlinear forcing map, however, takes **weighted H³ spectral
states**, not raw Fourier `L²` carriers.  The two types are definitionally the
same Lean type, so it is especially important not to cross this representation
boundary silently.

Positive-time regularity already supplies exactly the extra information needed
to encode `R̂` honestly:

* `R̂ ∈ L²`;
* `q² R̂ ∈ L²`, because the established derivative of `q² û` is the exact
  weighted PDE right-hand side.

Since the exact H³ spectral weight satisfies

    W₃² = 1 + q + q² + q³

and, for `q ≥ 0`,

    W₃² ≤ 4 (1 + q⁴),

the weighted amplitude `W₃ R̂` belongs to `L²`.

This file therefore constructs the genuine spectral derivative carrier

    R_H3 := W₃ R̂,

proves its literal representative, and proves the exact deweighting round trip

    rawFourierL2(R_H3) = R̂.

After this checkpoint the nonlinear bilinear map may consume the selected
velocity derivative without double-deweighting or any representation abuse.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedProjectedRHSH3Encoder
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2200000

/-! ## Slab-to-radius bookkeeping -/

/--
The elapsed time represented by a point of a positive terminal-half slab,
viewed in the full closed selected restart radius.
-/
def h3SelectedProjectedRHSSlabRadius
    {E Q : ℝ}
    (_hE : 1 ≤ E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (s : Set.Icc (Q / 2) Q) :
    Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
  ⟨
    (s : ℝ),
    (
      lt_of_lt_of_le
        (by positivity : 0 < Q / 2)
        s.property.1
    ).le,
    (
      lt_of_le_of_lt
        s.property.2
        hQR
    ).le
  ⟩

@[simp]
theorem h3SelectedProjectedRHSSlabRadius_coe
    {E Q : ℝ}
    (_hE : 1 ≤ E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (s : Set.Icc (Q / 2) Q) :
    (h3SelectedProjectedRHSSlabRadius _hE hQ hQR s : ℝ)
      =
    (s : ℝ) :=
  rfl

/-! ## Coarse exact-H³ weight domination -/

/--
A coarse but global polynomial ceiling for the exact H³ spectral weight-square:

    W₃² ≤ 4 (1 + q⁴).

The constant is intentionally non-sharp; only finite `L²` control matters.
-/
theorem h3SobolevFrequencyWeightSq_le_four_mul_one_add_gradientSquare_fourth
    (ξ : H3FourierPoint3) :
    h3SobolevFrequencyWeightSq ξ
      ≤
    4 * (1 + h3FourierGradientSquare ξ ^ 4) := by

  let q : ℝ :=
    h3FourierGradientSquare ξ

  have hq0 :
      0 ≤ q := by
    dsimp only [q]
    exact h3FourierGradientSquare_nonneg ξ

  by_cases hq1 : q ≤ 1

  · have hq2 :
        q ^ 2 ≤ 1 := by
      have hprod :
          0 ≤ q * (1 - q) :=
        mul_nonneg hq0 (sub_nonneg.mpr hq1)
      nlinarith

    have hq3 :
        q ^ 3 ≤ 1 := by
      have hprod :
          0 ≤ q ^ 2 * (1 - q) :=
        mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hq1)
      nlinarith

    have hq4 :
        0 ≤ q ^ 4 := by
      positivity

    dsimp only [q] at hq0 hq1 hq2 hq3 hq4 ⊢
    unfold h3SobolevFrequencyWeightSq
    nlinarith

  · have h1q :
        1 ≤ q := by
      exact
        (lt_of_not_ge hq1).le

    have hq_q2 :
        q ≤ q ^ 2 := by
      have hprod :
          0 ≤ q * (q - 1) :=
        mul_nonneg hq0 (sub_nonneg.mpr h1q)
      nlinarith

    have hq2_q3 :
        q ^ 2 ≤ q ^ 3 := by
      have hprod :
          0 ≤ q ^ 2 * (q - 1) :=
        mul_nonneg (sq_nonneg q) (sub_nonneg.mpr h1q)
      nlinarith

    have hq3_0 :
        0 ≤ q ^ 3 := by
      positivity

    have hq3_q4 :
        q ^ 3 ≤ q ^ 4 := by
      have hprod :
          0 ≤ q ^ 3 * (q - 1) :=
        mul_nonneg hq3_0 (sub_nonneg.mpr h1q)
      nlinarith

    dsimp only [q] at hq0 h1q hq_q2 hq2_q3 hq3_q4 ⊢
    unfold h3SobolevFrequencyWeightSq
    nlinarith

/-! ## Weighted projected-RHS scalar encoder -/

/--
The exact weighted amplitude `W₃ R̂_i` belongs to Fourier `L²` on every
positive selected terminal-half slab.
-/
theorem h3PreterminalSelectedProjectedRHSWeightedH3_memLp2
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
    let qRadius :=
      h3SelectedProjectedRHSSlabRadius hE hQ hQR s
    let F : H3FourierComplexL2 :=
      h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
        hNS ht₀ hE hTail qRadius i
    MemLp
      (fun ξ : H3FourierPoint3 =>
        (h3SobolevFrequencyWeight ξ : ℂ) * F ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  dsimp only

  let qRadius :=
    h3SelectedProjectedRHSSlabRadius hE hQ hQR s

  let F : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht₀ hE hTail qRadius i

  let G : H3FourierComplexL2 :=
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR i s

  have hGF :=
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab_ae_eq_qsq_projectedRHS
      hNS ht₀ hE hTail hQ hQR i s

  have hWeightedMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          (h3SobolevFrequencyWeight ξ : ℂ) * F ξ)
        (volume : Measure H3FourierPoint3) :=
    (Complex.continuous_ofReal.comp
      continuous_h3SobolevFrequencyWeight).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable F)

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

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          4 * (‖F ξ‖ ^ 2 + ‖G ξ‖ ^ 2))
        (volume : Measure H3FourierPoint3) :=
    (hFInt.add hGInt).const_mul 4

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖(h3SobolevFrequencyWeight ξ : ℂ) * F ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    exact
      (
        hWeightedMeas.norm.aemeasurable.pow_const 2
      ).aestronglyMeasurable

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
          4 * (‖F ξ‖ ^ 2 + ‖G ξ‖ ^ 2))
        hMajorInt
        hTargetMeas
        ?_

    filter_upwards [hGF] with ξ hGFξ

    let q : ℝ :=
      h3FourierGradientSquare ξ

    have hq0 :
        0 ≤ q := by
      dsimp only [q]
      exact h3FourierGradientSquare_nonneg ξ

    have hW0 :
        0 ≤ h3SobolevFrequencyWeight ξ :=
      le_of_lt
        (h3SobolevFrequencyWeight_pos ξ)

    have hPoly :=
      h3SobolevFrequencyWeightSq_le_four_mul_one_add_gradientSquare_fourth
        ξ

    have hPolyQ :
        h3SobolevFrequencyWeightSq ξ
          ≤
        4 * (1 + q ^ 4) := by
      simpa only [q] using hPoly

    change
      G ξ
        =
      ((q ^ 2 : ℝ) : ℂ) * F ξ
      at hGFξ

    have hGnorm :
        ‖G ξ‖ ^ 2
          =
        q ^ 4 * ‖F ξ‖ ^ 2 := by
      rw [hGFξ, norm_mul]
      simp only [
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg q)
      ]
      ring

    have hPoint :
        ‖(h3SobolevFrequencyWeight ξ : ℂ) * F ξ‖ ^ 2
          ≤
        4 * (‖F ξ‖ ^ 2 + ‖G ξ‖ ^ 2) := by

      rw [
        norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg hW0,
        mul_pow,
        h3SobolevFrequencyWeight_sq,
        hGnorm
      ]

      have hF0 :
          0 ≤ ‖F ξ‖ ^ 2 :=
        sq_nonneg _

      calc
        h3SobolevFrequencyWeightSq ξ * ‖F ξ‖ ^ 2
            ≤
          (4 * (1 + q ^ 4)) * ‖F ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            hPolyQ
            hF0
        _ =
          4 * (‖F ξ‖ ^ 2 + q ^ 4 * ‖F ξ‖ ^ 2) := by
          ring

    have hLeft0 :
        0 ≤
          ‖(h3SobolevFrequencyWeight ξ : ℂ) * F ξ‖ ^ 2 :=
      sq_nonneg _

    have hRight0 :
        0 ≤
          4 * (‖F ξ‖ ^ 2 + ‖G ξ‖ ^ 2) := by
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
Genuine H³ spectral encoding of one selected projected-RHS coordinate:

    `W₃ R̂_i`.
-/
noncomputable def h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab
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
  let qRadius :=
    h3SelectedProjectedRHSSlabRadius hE hQ hQR s
  let F : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht₀ hE hTail qRadius i
  (
    h3PreterminalSelectedProjectedRHSWeightedH3_memLp2
      hNS ht₀ hE hTail hQ hQR i s
  ).toLp
    (fun ξ : H3FourierPoint3 =>
      (h3SobolevFrequencyWeight ξ : ℂ) * F ξ)

/--
The H³-encoded projected RHS has the literal weighted representative
`W₃ R̂_i`.
-/
theorem h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_ae
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
    let qRadius :=
      h3SelectedProjectedRHSSlabRadius hE hQ hQR s
    let F : H3FourierComplexL2 :=
      h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
        hNS ht₀ hE hTail qRadius i
    (
      (
        h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab
          hNS ht₀ hE hTail hQ hQR i s :
        H3SpectralScalarState
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (h3SobolevFrequencyWeight ξ : ℂ) * F ξ) := by

  dsimp only

  unfold
    h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab

  exact
    MemLp.coeFn_toLp
      (
        h3PreterminalSelectedProjectedRHSWeightedH3_memLp2
          hNS ht₀ hE hTail hQ hQR i s
      )

/--
Deweighting the genuine spectral encoding recovers exactly the original raw
selected projected RHS coordinate.
-/
theorem h3SpectralScalarRawFourierL2_h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_eq
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
    let qRadius :=
      h3SelectedProjectedRHSSlabRadius hE hQ hQR s
    h3SpectralScalarRawFourierL2
      (
        h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab
          hNS ht₀ hE hTail hQ hQR i s
      )
      =
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht₀ hE hTail qRadius i := by

  dsimp only

  let qRadius :=
    h3SelectedProjectedRHSSlabRadius hE hQ hQR s

  let F : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht₀ hE hTail qRadius i

  let R : H3SpectralScalarState :=
    h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab
      hNS ht₀ hE hTail hQ hQR i s

  have hRaw :=
    h3SpectralScalarRawFourierL2_ae R

  have hEncoded :=
    h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_ae
      hNS ht₀ hE hTail hQ hQR i s

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

/-! ## Three-component genuine H³ derivative carrier -/

/--
The selected projected RHS encoded coordinatewise as a genuine weighted H³
spectral vector state.
-/
noncomputable def h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
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
    H3SpectralFinVectorState :=
  fun i : Fin 3 =>
    h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab
      hNS ht₀ hE hTail hQ hQR i s

@[simp]
theorem h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab_apply
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (s : Set.Icc (Q / 2) Q)
    (i : Fin 3) :
    h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
        hNS ht₀ hE hTail hQ hQR s i
      =
    h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab
      hNS ht₀ hE hTail hQ hQR i s :=
  rfl

/--
Coordinatewise deweighting of the genuine H³ projected-RHS state is exactly
the raw selected projected-RHS vector.
-/
theorem h3SpectralScalarRawFourierL2_h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab_apply_eq
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (s : Set.Icc (Q / 2) Q)
    (i : Fin 3) :
    h3SpectralScalarRawFourierL2
      (
        h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
          hNS ht₀ hE hTail hQ hQR s i
      )
      =
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht₀ hE hTail
      (h3SelectedProjectedRHSSlabRadius hE hQ hQR s)
      i := by

  exact
    h3SpectralScalarRawFourierL2_h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_eq
      hNS ht₀ hE hTail hQ hQR i s

end

end Euclidean
end Bridge
end PrimeTensor
