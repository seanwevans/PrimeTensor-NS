import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Angular.Vanishing.From.Tightness.Equiintegrability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Fixed.Transverse.Coordinate.Channel

/-!
# Bounded bad-cone volume vanishing

The compactness checkpoint reduced physical H³ dissipation angular vanishing to
one remaining Euclidean statement: after imposing a fixed outer radial cutoff,
the volume of a longitudinal angular bad cone tends to zero with its aperture.

This file proves that geometric input directly.

Inside `h3TerminalRadialFrequencyBelow R`, every Fourier coordinate has
absolute value below `R / (2*pi)`.  On the longitudinal bad cone, the selected
coordinate is sharper by one factor of `kappa`.  Hence the localized cone lies
inside a rectangular box whose selected side length is proportional to
`kappa`, while all transverse side lengths are fixed.  The canonical map from
Euclidean space to the underlying finite product of real coordinates preserves
volume, so the product-box formula gives a volume bound linear in `kappa`.

Consequently the bounded bad-cone volume hypothesis used by the previous
checkpoint is automatic, for every inner radial cutoff.  Combining this with
the preceding compactness theorem leaves only the two analytic hypotheses:
uniform radial-tail tightness and uniform absolute continuity of the physical
H³ dissipation densities.

All continuation conclusions remain conditional.  No singular solution and no
unconditional global-regularity statement is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationBoundedBadConeVolumeVanishing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance axisDecidableEqH3TerminalPhysicalDissipationBoundedBadConeVolumeVanishing
    (d : Depth) :
    DecidableEq (PrimeTensor.Axis d) :=
  Classical.decEq _

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationBoundedBadConeVolumeVanishing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## A rectangular majorant for a bounded bad cone -/

/--
At positive outer radius `R` and positive aperture `κ`, the bounded bad-cone
region has volume at most the volume of the coordinate box with transverse
half-width `R/(2*pi)` and longitudinal half-width `κ R/(2*pi)`.

The finite product over the complementary coordinate axes is left abstract;
only its positivity and finiteness matter for the vanishing argument.
-/
theorem volume_boundedLongitudinalBadCone_le_rectangular_majorant
    (i : Fin 3)
    (ρ : ℝ)
    {R κ : ℝ}
    (hR : 0 < R)
    (hκ : 0 < κ) :
    let r : ℝ := R / (2 * Real.pi)
    let a : PrimeTensor.Axis Depth.three := h3AxisOfFin3 i
    let C : ℝ :=
      ∏ j ∈ Finset.univ.erase a,
        (2 * r)
    volume
        ((h3TerminalLongitudinalAngularBadCone i κ
            \
          h3TerminalRadialFrequencyBelow ρ)
          ∩
        h3TerminalRadialFrequencyBelow R)
      ≤
    ENNReal.ofReal ((2 * κ * r) * C) := by

  dsimp only

  let r : ℝ := R / (2 * Real.pi)
  let a : PrimeTensor.Axis Depth.three := h3AxisOfFin3 i
  let C : ℝ :=
    ∏ j ∈ Finset.univ.erase a,
      (2 * r)

  have hTwoPiPos : 0 < 2 * Real.pi := by
    positivity

  have hr : 0 < r := by
    dsimp only [r]
    exact div_pos hR hTwoPiPos

  let lo : PrimeTensor.Axis Depth.three → ℝ :=
    fun j => if j = a then -(κ * r) else -r

  let hi : PrimeTensor.Axis Depth.three → ℝ :=
    fun j => if j = a then κ * r else r

  let rawBox : Set (PrimeTensor.Axis Depth.three → ℝ) :=
    Set.Icc lo hi

  have hSubset :
      ((h3TerminalLongitudinalAngularBadCone i κ
          \
        h3TerminalRadialFrequencyBelow ρ)
        ∩
      h3TerminalRadialFrequencyBelow R)
        ⊆
      WithLp.ofLp ⁻¹' rawBox := by
    intro ξ hξ

    have hBad :
        ξ ∈ h3TerminalLongitudinalAngularBadCone i κ :=
      hξ.1.1

    have hOuter :
        ξ ∈ h3TerminalRadialFrequencyBelow R :=
      hξ.2

    have hNormLt : ‖ξ‖ < r := by
      change h3FourierGradientMagnitude ξ < R at hOuter
      unfold h3FourierGradientMagnitude at hOuter
      dsimp only [r]
      exact
        (lt_div_iff₀ hTwoPiPos).2
          (by
            simpa only [mul_comm] using hOuter)

    have hCoordAbsLt :
        ∀ j : PrimeTensor.Axis Depth.three,
          |ξ j| < r := by
      intro j
      have hCoordNormLe : ‖ξ j‖ ≤ ‖ξ‖ :=
        PiLp.norm_apply_le ξ j
      have hCoordNormLt : ‖ξ j‖ < r :=
        hCoordNormLe.trans_lt hNormLt
      simpa only [Real.norm_eq_abs] using hCoordNormLt

    have hBadRaw :
        ‖h3FourierDerivativeSymbol i ξ‖
          <
        κ * h3FourierGradientMagnitude ξ := by
      exact hBad

    rw [
      norm_h3FourierDerivativeSymbol_eq_two_pi_mul_abs_coordinate
    ] at hBadRaw

    unfold h3FourierGradientMagnitude at hBadRaw

    have hBadRaw' :
        (2 * Real.pi) * |ξ (h3AxisOfFin3 i)|
          <
        (2 * Real.pi) * (κ * ‖ξ‖) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hBadRaw

    have hSelectedVsNorm :
        |ξ (h3AxisOfFin3 i)| < κ * ‖ξ‖ := by
      by_contra hNot
      have hReverse :
          κ * ‖ξ‖ ≤ |ξ (h3AxisOfFin3 i)| :=
        le_of_not_gt hNot
      have hScaledReverse :
          (2 * Real.pi) * (κ * ‖ξ‖)
            ≤
          (2 * Real.pi) * |ξ (h3AxisOfFin3 i)| :=
        mul_le_mul_of_nonneg_left hReverse hTwoPiPos.le
      exact (not_le_of_gt hBadRaw') hScaledReverse

    have hSelectedAbsLt :
        |ξ a| < κ * r := by
      dsimp only [a]
      exact
        hSelectedVsNorm.trans
          (mul_lt_mul_of_pos_left hNormLt hκ)

    have hSelectedBounds :
        -(κ * r) < ξ a ∧ ξ a < κ * r :=
      (abs_lt).1 hSelectedAbsLt

    have hCoordBounds :
        ∀ j : PrimeTensor.Axis Depth.three,
          -r < ξ j ∧ ξ j < r := by
      intro j
      exact (abs_lt).1 (hCoordAbsLt j)

    change lo ≤ WithLp.ofLp ξ ∧ WithLp.ofLp ξ ≤ hi

    constructor
    · intro j
      by_cases hj : j = a
      · subst j
        dsimp only [lo]
        simp only [if_pos]
        exact hSelectedBounds.1.le
      · dsimp only [lo]
        simp only [if_neg hj]
        exact (hCoordBounds j).1.le
    · intro j
      by_cases hj : j = a
      · subst j
        dsimp only [hi]
        simp only [if_pos]
        exact hSelectedBounds.2.le
      · dsimp only [hi]
        simp only [if_neg hj]
        exact (hCoordBounds j).2.le

  have hRawBoxMeas : MeasurableSet rawBox := by
    dsimp only [rawBox]
    exact measurableSet_Icc

  have hPreimageVolume :
      volume
          ((WithLp.ofLp :
              H3FourierPoint3 →
                (PrimeTensor.Axis Depth.three → ℝ)) ⁻¹' rawBox)
        =
      volume rawBox := by
    exact
      (PiLp.volume_preserving_ofLp
        (PrimeTensor.Axis Depth.three)).measure_preimage
          hRawBoxMeas.nullMeasurableSet

  have hRestBridge :
      ENNReal.ofReal C
        =
      ∏ j ∈ Finset.univ.erase a,
        ENNReal.ofReal (2 * r) := by
    dsimp only [C]
    exact
      ENNReal.ofReal_prod_of_nonneg
        (fun _ _ => by positivity)

  have hRawBoxVolume :
      volume rawBox
        =
      ENNReal.ofReal ((2 * κ * r) * C) := by
    dsimp only [rawBox]
    rw [Real.volume_Icc_pi]
    rw [← Finset.mul_prod_erase
      Finset.univ
      (fun j => ENNReal.ofReal (hi j - lo j))
      (Finset.mem_univ a)]

    have hSelectedLength :
        hi a - lo a = 2 * κ * r := by
      dsimp only [hi, lo]
      simp only [if_pos]
      ring

    have hComplementLengths :
        (∏ j ∈ Finset.univ.erase a,
            ENNReal.ofReal (hi j - lo j))
          =
        ∏ j ∈ Finset.univ.erase a,
          ENNReal.ofReal (2 * r) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hja : j ≠ a :=
        (Finset.mem_erase.mp hj).1
      congr 1
      dsimp only [hi, lo]
      simp only [if_neg hja]
      ring

    rw [hSelectedLength, hComplementLengths]
    rw [← hRestBridge]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * κ * r)]

  calc
    volume
        ((h3TerminalLongitudinalAngularBadCone i κ
            \
          h3TerminalRadialFrequencyBelow ρ)
          ∩
        h3TerminalRadialFrequencyBelow R)
        ≤
      volume (WithLp.ofLp ⁻¹' rawBox) :=
        measure_mono hSubset
    _ = volume rawBox := hPreimageVolume
    _ = ENNReal.ofReal ((2 * κ * r) * C) := hRawBoxVolume

/-! ## Automatic bounded bad-cone volume vanishing -/

/--
For every coordinate and every inner radial cutoff, bounded bad-cone volume
vanishing is automatic.  The proof is independent of the inner cutoff: after
intersecting with the outer radial ball, the bad cone is dominated by a box
whose volume is linear in the aperture.
-/
theorem longitudinalBoundedBadConeVolumeVanishingAtCutoff
    (i : Fin 3)
    (ρ : ℝ) :
    H3TerminalLongitudinalBoundedBadConeVolumeVanishingAtCutoff
      i ρ := by

  intro R α hα

  by_cases hR : 0 < R

  · let r : ℝ := R / (2 * Real.pi)
    let a : PrimeTensor.Axis Depth.three := h3AxisOfFin3 i
    let C : ℝ :=
      ∏ j ∈ Finset.univ.erase a,
        (2 * r)

    have hTwoPiPos : 0 < 2 * Real.pi := by
      positivity

    have hr : 0 < r := by
      dsimp only [r]
      exact div_pos hR hTwoPiPos

    have hC : 0 < C := by
      dsimp only [C]
      positivity

    by_cases hαTop : α = ∞

    · refine ⟨1, by positivity, ?_⟩
      intro κ hκ hκOne

      have hMajorant :=
        volume_boundedLongitudinalBadCone_le_rectangular_majorant
          i ρ hR hκ

      change
        volume
            ((h3TerminalLongitudinalAngularBadCone i κ
                \
              h3TerminalRadialFrequencyBelow ρ)
              ∩
            h3TerminalRadialFrequencyBelow R)
          ≤
        ENNReal.ofReal ((2 * κ * r) * C)
        at hMajorant

      rw [hαTop]
      exact hMajorant.trans_lt (by simp)

    · have hαReal : 0 < α.toReal :=
        ENNReal.toReal_pos hα.ne' hαTop

      let D : ℝ := 2 * r * C

      have hD : 0 < D := by
        dsimp only [D]
        positivity

      let κ₀ : ℝ := α.toReal / D

      have hκ₀ : 0 < κ₀ := by
        dsimp only [κ₀]
        exact div_pos hαReal hD

      refine ⟨κ₀, hκ₀, ?_⟩

      intro κ hκ hκSmall

      have hMajorant :=
        volume_boundedLongitudinalBadCone_le_rectangular_majorant
          i ρ hR hκ

      have hκSmall' : κ < α.toReal / D := by
        simpa only [κ₀] using hκSmall

      have hRealSmall : κ * D < α.toReal :=
        (lt_div_iff₀ hD).1 hκSmall'

      have hMajorantRealSmall :
          (2 * κ * r) * C < α.toReal := by
        dsimp only [D] at hRealSmall
        nlinarith

      have hMajorantNonneg :
          0 ≤ (2 * κ * r) * C := by
        positivity

      have hMajorantENNRealSmall :
          ENNReal.ofReal ((2 * κ * r) * C) < α :=
        (ENNReal.ofReal_lt_iff_lt_toReal
          hMajorantNonneg hαTop).2
          hMajorantRealSmall

      change
        volume
            ((h3TerminalLongitudinalAngularBadCone i κ
                \
              h3TerminalRadialFrequencyBelow ρ)
              ∩
            h3TerminalRadialFrequencyBelow R)
          ≤
        ENNReal.ofReal ((2 * κ * r) * C)
        at hMajorant

      exact hMajorant.trans_lt hMajorantENNRealSmall

  · have hRle : R ≤ 0 := le_of_not_gt hR

    have hOuterEmpty :
        h3TerminalRadialFrequencyBelow R = ∅ := by
      ext ξ
      simp only [
        h3TerminalRadialFrequencyBelow,
        Set.mem_setOf_eq,
        Set.mem_empty_iff_false,
        iff_false
      ]
      exact
        not_lt_of_ge
          (hRle.trans (h3FourierGradientMagnitude_nonneg ξ))

    refine ⟨1, by positivity, ?_⟩
    intro κ hκ hκOne
    rw [hOuterEmpty]
    simp only [Set.inter_empty, measure_empty]
    exact hα

/-! ## Compactness-only continuation criterion -/

/--
The geometric bounded-cone hypothesis in the previous compactness theorem is
automatic.  Thus radial-tail tightness and uniform absolute continuity of the
single-time physical H³ dissipation densities are sufficient, together with
the retained raw-Fourier L² Cauchy hypothesis and one surviving physical
vorticity endpoint, for smooth continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalDissipationTightnessUniformAbsoluteContinuity_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysicalVorticity :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hTail :
      H3TerminalPhysicalDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass)
    (hUniformAbsoluteContinuity :
      H3TerminalPhysicalDissipationSingleTimeUniformAbsoluteContinuityAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalDissipationTightnessEquiintegrability_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysicalVorticity
      hCauchy
      hTail
      hUniformAbsoluteContinuity
      (fun ρ hρ =>
        longitudinalBoundedBadConeVolumeVanishingAtCutoff i ρ)

/-! ## Necessary analytic obstruction under hypothetical nonextension -/

/--
With the Euclidean cone-volume input discharged, hypothetical nonextension
under the retained raw-Fourier L² Cauchy hypothesis and one surviving physical
vorticity endpoint forces failure of at least one of the two genuine analytic
compactness mechanisms: radial-tail tightness or uniform absolute continuity.
-/
theorem radialTailTight_or_uniformAbsoluteContinuity_fails_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    ¬ H3TerminalPhysicalDissipationSingleTimeRadialTailTightAtEndpoint
          hH3 hClass
      ∨
    ¬ H3TerminalPhysicalDissipationSingleTimeUniformAbsoluteContinuityAtEndpoint
          hH3 hClass := by

  by_contra hBoth
  push_neg at hBoth

  exact
    hNoExtension
      (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalDissipationTightnessUniformAbsoluteContinuity_of_actualVorticityStrongH3EndpointPath
        hH3
        hClass
        hPhysical
        hCauchy
        hBoth.1
        hBoth.2)

end

end Euclidean
end Bridge
end PrimeTensor
