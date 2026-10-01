import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Coercive.Radial.Weight.Cascade

/-!
# Coercive radial-weight continuation criterion

The preceding checkpoint showed that hypothetical nonextension forces every
nonnegative monotone coercive radial weight to diverge along one common
terminal sequence.

This file proves the dual sufficient criterion.

Let `w : ℝ → ℝ` be nonnegative, monotone, and coercive:

    w(r) → +∞  as  r → +∞.

Assume that near the terminal time the extended weighted top-order dissipation
moment has one finite uniform ceiling,

    ∫⁻ ofReal (w(|D|) q^4 |û|²) dξ ≤ ofReal C.

For any tail tolerance `δ > 0`, coercivity lets us choose `R > 0` so large that

    C / δ < w(R).

On every measurable set outside radial cutoff `R`, the previous set-level
estimate gives

    ofReal (w(R) * topMass(S))
      ≤
    weightedMoment
      ≤
    ofReal C.

Therefore

    w(R) * topMass(S) ≤ C < w(R) * δ,

and positivity of `w(R)` yields

    topMass(S) < δ.

Thus the physical top-order H³ dissipation density is radially tight near the
endpoint.  The already-proved top-order radial-tail criterion then gives smooth
continuation.

Hence one finite coercive weighted ceiling is sufficient for continuation.
Equivalently, under the retained endpoint assumptions, hypothetical
nonextension rules out every such ceiling.

No converse construction of a coercive weight from radial tightness is claimed
here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalCoerciveRadialWeightCriterion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalCoerciveRadialWeightCriterion :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Uniform finite ceiling for one coercive weighted moment -/

/--
A finite uniform terminal ceiling for the extended top-order dissipation moment
weighted by one radial function `w`.

The moment remains `ℝ≥0∞`-valued; the hypothesis asserts directly that it lies
below the finite quantity `ofReal C` near the endpoint.
-/
def H3TerminalPhysicalRadialWeightedTopDissipationUniformBoundAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (w : ℝ → ℝ) : Prop :=
  ∃ C : ℝ,
    0 ≤ C
      ∧
    ∃ η : ℝ,
      0 < η
        ∧
      ∀ t : ℝ,
        ∀ ht : t ∈ Set.Ioo a T,
          dist t T < η
            →
          h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
              hH3 hClass w t ht
            ≤
          ENNReal.ofReal C

/-! ## One coercive weighted ceiling implies top-order radial tightness -/

/--
A finite uniform ceiling for one nonnegative monotone coercive radial weighted
top-order moment forces uniform radial-tail tightness of the physical top-order
H³ dissipation density.
-/
theorem physicalTopDissipationRadialTailTightAtEndpoint_of_coerciveRadialWeightedTopDissipationUniformBoundAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {w : ℝ → ℝ}
    (hw : H3TerminalCoerciveRadialWeight w)
    (hBound :
      H3TerminalPhysicalRadialWeightedTopDissipationUniformBoundAtEndpoint
        hH3 hClass w) :
    H3TerminalPhysicalTopDissipationSingleTimeRadialTailTightAtEndpoint
      hH3 hClass := by

  obtain
    ⟨
      C,
      hC,
      η,
      hη,
      hMoment
    ⟩ :=
    hBound

  intro δ hδ

  have hCDivNonneg :
      0 ≤ C / δ :=
    div_nonneg
      hC
      hδ.le

  have hWeightLargeEventually :
      ∀ᶠ R : ℝ in atTop,
        C / δ < w R :=
    hw.tendsto_atTop.eventually
      (eventually_gt_atTop
        (C / δ))

  have hRadiusPositiveEventually :
      ∀ᶠ R : ℝ in atTop,
        0 < R :=
    eventually_gt_atTop
      (0 : ℝ)

  obtain
    ⟨
      R,
      hR,
      hWeightLarge
    ⟩ :=
    (
      hRadiusPositiveEventually.and
        hWeightLargeEventually
    ).exists

  have hWeightPos :
      0 < w R :=
    lt_of_le_of_lt
      hCDivNonneg
      hWeightLarge

  have hThresholdScaled :
      C
        <
      w R * δ := by

    have hScaled :=
      mul_lt_mul_of_pos_right
        hWeightLarge
        hδ

    have hCancel :
        (C / δ) * δ
          =
        C := by
      field_simp [ne_of_gt hδ]

    rw [hCancel] at hScaled

    exact
      hScaled

  refine
    ⟨
      R,
      hR,
      η,
      hη,
      ?_
    ⟩

  intro t ht htNear S hS hOutside

  have hSetLower :=
    ofReal_weight_cutoff_mul_topDissipationSetMass_le_extendedRadialWeightedTopDissipationMoment_of_setOutside
      hH3
      hClass
      hw
      ht
      S
      hS
      hOutside

  have hMomentUpper :
      h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
          hH3 hClass w t ht
        ≤
      ENNReal.ofReal C :=
    hMoment
      t
      ht
      htNear

  have hENNRealScaled :
      ENNReal.ofReal
        (
          w R
            *
          h3TerminalPhysicalTopDissipationSetMassAt
            hH3 hClass t ht S
        )
        ≤
      ENNReal.ofReal C :=
    hSetLower.trans
      hMomentUpper

  have hScaledReal :
      w R
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass t ht S
        ≤
      C := by

    exact
      (ENNReal.ofReal_le_ofReal_iff hC).1
        hENNRealScaled

  have hStrictScaled :
      w R
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass t ht S
        <
      w R * δ :=
    lt_of_le_of_lt
      hScaledReal
      hThresholdScaled

  exact
    lt_of_mul_lt_mul_left
      hStrictScaled
      hWeightPos.le

/-! ## Coercive-weight continuation criterion -/

/--
Under the retained raw-Fourier `L²` Cauchy and physical-vorticity endpoint
assumptions, one finite uniform coercive radial weighted top-order moment
ceiling is sufficient for smooth continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_coerciveRadialWeightedTopDissipationUniformBound_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    {w : ℝ → ℝ}
    (hw : H3TerminalCoerciveRadialWeight w)
    (hBound :
      H3TerminalPhysicalRadialWeightedTopDissipationUniformBoundAtEndpoint
        hH3 hClass w) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hTopTail :
      H3TerminalPhysicalTopDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass :=
    physicalTopDissipationRadialTailTightAtEndpoint_of_coerciveRadialWeightedTopDissipationUniformBoundAtEndpoint
      hH3
      hClass
      hw
      hBound

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalTopDissipationRadialTailTightness_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      hTopTail

/--
Existential version: it is enough that there exists at least one coercive
radial weight carrying a finite uniform terminal top-dissipation ceiling.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_exists_coerciveRadialWeightedTopDissipationUniformBound_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hExists :
      ∃ w : ℝ → ℝ,
        H3TerminalCoerciveRadialWeight w
          ∧
        H3TerminalPhysicalRadialWeightedTopDissipationUniformBoundAtEndpoint
          hH3 hClass w) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  obtain
    ⟨
      w,
      hw,
      hBound
    ⟩ :=
    hExists

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_coerciveRadialWeightedTopDissipationUniformBound_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      hw
      hBound

/-! ## Necessary failure of every coercive ceiling under hypothetical nonextension -/

/--
Under the retained endpoint assumptions, hypothetical nonextension rules out
a finite uniform terminal ceiling for every nonnegative monotone coercive
radial top-dissipation weight.
-/
theorem no_coerciveRadialWeightedTopDissipationUniformBound_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    ∀ w : ℝ → ℝ,
      H3TerminalCoerciveRadialWeight w
        →
      ¬ H3TerminalPhysicalRadialWeightedTopDissipationUniformBoundAtEndpoint
          hH3 hClass w := by

  intro w hw hBound

  exact
    hNoExtension
      (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_coerciveRadialWeightedTopDissipationUniformBound_of_actualVorticityStrongH3EndpointPath
        hH3
        hClass
        hPhysical
        hCauchy
        hw
        hBound)

/-! ## Neutral formulation -/

/--
Neutral compactness alternative: either the H³ path extends smoothly through
`T`, or every nonnegative monotone coercive radial top-dissipation weight fails
to have a finite uniform terminal ceiling.

This is the dual criterion corresponding to the universal coercive-weight
escape sequence from the preceding checkpoint.  It does not assert that the
nonextension branch occurs.
-/
theorem smoothContinuationExtension_or_no_coerciveRadialWeightedTopDissipationUniformBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∀ w : ℝ → ℝ,
        H3TerminalCoerciveRadialWeight w
          →
        ¬ H3TerminalPhysicalRadialWeightedTopDissipationUniformBoundAtEndpoint
            hH3 hClass w
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (no_coerciveRadialWeightedTopDissipationUniformBound_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
