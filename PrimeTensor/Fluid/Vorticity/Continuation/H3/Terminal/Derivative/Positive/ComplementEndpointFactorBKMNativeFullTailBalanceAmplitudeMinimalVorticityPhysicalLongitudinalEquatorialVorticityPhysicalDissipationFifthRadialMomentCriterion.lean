import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationTopOrderRadialTailCriterion

/-!
# One-extra-moment continuation criterion

The remaining physical compactness hypothesis is radial-tail tightness of the
top-order H³ dissipation density

    q(ξ)^4 |û(t,ξ)|²,

where `q = h3FourierGradientSquare = |D(ξ)|²`.

A uniform bound for one additional radial moment,

    ∫ q(ξ)^5 |û(t,ξ)|² dξ ≤ C,

automatically supplies that tail tightness.  Indeed, outside radial gradient
cutoff `R`,

    R² ≤ q(ξ),

hence

    R² q(ξ)^4 |û|² ≤ q(ξ)^5 |û|².

After integration,

    R² · topTailMass ≤ fifthMoment ≤ C.

Choosing `R = C / δ + 1` gives `C < δ R²`, so the top-order tail mass is
smaller than `δ`.

Combined with the preceding top-order radial-tail continuation criterion, this
gives a clean one-extra-moment sufficient condition for continuation.

The theorem is deliberately conditional on a terminal uniform fifth-radial
moment bound.  No claim is made here that such a bound follows from the base
H³ hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationFifthRadialMomentCriterion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationFifthRadialMomentCriterion :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Fifth radial density and moment -/

/--
The physical fifth radial raw-Fourier density

    q(ξ)^5 |û(t,ξ)|²

at one strict H³ path time.
-/
noncomputable def h3TerminalPhysicalFifthRadialDensityAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T)
    (ξ : H3FourierPoint3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs
  h3FourierGradientSquare ξ ^ 5
    *
  velocityH3FourierMassDensityAt
    u t hInt hMeas ξ

theorem h3TerminalPhysicalFifthRadialDensityAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T)
    (ξ : H3FourierPoint3) :
    0 ≤
      h3TerminalPhysicalFifthRadialDensityAt
        hH3 hClass t ht ξ := by

  unfold h3TerminalPhysicalFifthRadialDensityAt

  exact
    mul_nonneg
      (pow_nonneg
        (h3FourierGradientSquare_nonneg ξ)
        5)
      (velocityH3FourierMassDensityAt_nonneg
        u
        t
        (hH3.velocity_h3_integrable
          t
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
        (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
          hH3.navier_stokes
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
        ξ)

/--
The corresponding whole-space fifth radial moment.
-/
noncomputable def h3TerminalPhysicalFifthRadialMomentAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3TerminalPhysicalFifthRadialDensityAt
      hH3 hClass t ht ξ
    ∂volume

/-! ## Uniform terminal fifth-moment hypothesis -/

/--
Uniform terminal bound for the physical fifth radial raw-Fourier moment.

Integrability is included explicitly because it is not part of the base H³
energy class.
-/
def H3TerminalPhysicalFifthRadialMomentUniformBoundAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
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
          Integrable
            (h3TerminalPhysicalFifthRadialDensityAt
              hH3 hClass t ht)
            volume
            ∧
          h3TerminalPhysicalFifthRadialMomentAt
              hH3 hClass t ht
            ≤
          C

/-! ## Pointwise fifth-moment domination of the top block -/

/--
Outside radial cutoff `R`, multiplication by `R²` sends the top-order
`q^4 |û|²` density below the fifth radial `q^5 |û|²` density.
-/
theorem radial_sq_mul_topDensity_le_fifthRadialDensity_of_cutoff_le_gradientMagnitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hR : 0 ≤ R)
    {ξ : H3FourierPoint3}
    (hξ :
      R ≤ h3FourierGradientMagnitude ξ) :
    R ^ 2
        *
      (
        h3FourierGradientSquare ξ ^ 4
          *
        velocityH3FourierMassDensityAt
          u
          t
          (hH3.velocity_h3_integrable
            t
            ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
          (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
            hH3.navier_stokes
            ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
          ξ
      )
      ≤
    h3TerminalPhysicalFifthRadialDensityAt
      hH3 hClass t ht ξ := by

  let q : ℝ :=
    h3FourierGradientSquare ξ

  let m : ℝ :=
    velocityH3FourierMassDensityAt
      u
      t
      (hH3.velocity_h3_integrable
        t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
      (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
      ξ

  have hq :
      R ^ 2 ≤ q := by
    dsimp only [q]
    rw [← h3FourierGradientMagnitude_sq]
    exact
      pow_le_pow_left₀
        hR
        hξ
        2

  have hm :
      0 ≤ m := by
    dsimp only [m]
    exact
      velocityH3FourierMassDensityAt_nonneg
        u
        t
        (hH3.velocity_h3_integrable
          t
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
        (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
          hH3.navier_stokes
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
        ξ

  have hq4m :
      0 ≤ q ^ 4 * m := by
    exact
      mul_nonneg
        (by positivity)
        hm

  have hMul :
      R ^ 2 * (q ^ 4 * m)
        ≤
      q * (q ^ 4 * m) :=
    mul_le_mul_of_nonneg_right
      hq
      hq4m

  unfold h3TerminalPhysicalFifthRadialDensityAt

  change
    R ^ 2 * (q ^ 4 * m)
      ≤
    q ^ 5 * m

  calc
    R ^ 2 * (q ^ 4 * m)
        ≤
      q * (q ^ 4 * m) :=
        hMul

    _ =
      q ^ 5 * m := by
        ring

/-! ## Uniform fifth moment implies top-order radial-tail tightness -/

/--
A uniform terminal fifth-radial moment ceiling forces uniform radial-tail
tightness of the top-order physical H³ dissipation density.
-/
theorem physicalTopDissipationRadialTailTightAtEndpoint_of_fifthRadialMomentUniformBoundAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hFifth :
      H3TerminalPhysicalFifthRadialMomentUniformBoundAtEndpoint
        hH3 hClass) :
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
    hFifth

  intro δ hδ

  let R : ℝ :=
    C / δ + 1

  have hCDiv :
      0 ≤ C / δ :=
    div_nonneg
      hC
      hδ.le

  have hR :
      0 < R := by
    dsimp only [R]
    linarith

  have hRNonneg :
      0 ≤ R :=
    hR.le

  have hROne :
      1 ≤ R := by
    dsimp only [R]
    linarith

  have hR2 :
      0 < R ^ 2 := by
    positivity

  have hCR :
      C < δ * R := by

    have hCancel :
        δ * (C / δ)
          =
        C := by
      field_simp [ne_of_gt hδ]

    dsimp only [R]

    rw [
      mul_add,
      hCancel
    ]

    linarith

  have hRLeR2 :
      R ≤ R ^ 2 := by
    simpa only [pow_one] using
      (pow_le_pow_right₀
        hROne
        (by norm_num : (1 : ℕ) ≤ 2))

  have hCR2 :
      C < δ * R ^ 2 := by
    exact
      lt_of_lt_of_le
        hCR
        (mul_le_mul_of_nonneg_left
          hRLeR2
          hδ.le)

  refine
    ⟨
      R,
      hR,
      η,
      hη,
      ?_
    ⟩

  intro t ht htNear S hS hOutside

  obtain
    ⟨hFifthInt, hFifthMomentLe⟩ :=
    hMoment
      t
      ht
      htNear

  let top : H3FourierPoint3 → ℝ :=
    fun ξ =>
      let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      let hInt : VelocityH3IntegrableAt u t :=
        hH3.velocity_h3_integrable t htAbs
      let hMeas : VelocityH3MeasurableAt u t :=
        velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
          hH3.navier_stokes htAbs
      h3FourierGradientSquare ξ ^ 4
        *
      velocityH3FourierMassDensityAt
        u t hInt hMeas ξ

  let fifth : H3FourierPoint3 → ℝ :=
    h3TerminalPhysicalFifthRadialDensityAt
      hH3 hClass t ht

  have hTopInt :
      Integrable top volume := by
    dsimp only [top]
    simpa only using
      (h3TerminalPhysicalTopDissipationDensity_integrable
        hH3 hClass ht)

  have hFifthInt' :
      Integrable fifth volume := by
    simpa only [fifth] using
      hFifthInt

  have hFifthNonneg :
      0 ≤ᵐ[volume] fifth := by
    exact
      Eventually.of_forall
        (fun ξ => by
          dsimp only [fifth]
          exact
            h3TerminalPhysicalFifthRadialDensityAt_nonneg
              hH3 hClass t ht ξ)

  have hPoint :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume.restrict S),
        R ^ 2 * top ξ
          ≤
        fifth ξ := by

    rw [ae_restrict_iff' hS]

    filter_upwards with ξ

    intro hξS

    have hOutsideξ :=
      hOutside hξS

    have hRadial :
        R ≤ h3FourierGradientMagnitude ξ := by

      change
        ¬ h3FourierGradientMagnitude ξ < R
          at hOutsideξ

      exact
        le_of_not_gt
          hOutsideξ

    dsimp only [top, fifth]

    exact
      radial_sq_mul_topDensity_le_fifthRadialDensity_of_cutoff_le_gradientMagnitude
        hH3
        hClass
        ht
        hRNonneg
        hRadial

  have hScaledSetLe :
      R ^ 2
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass t ht S
        ≤
      ∫ ξ in S, fifth ξ ∂volume := by

    unfold
      h3TerminalPhysicalTopDissipationSetMassAt

    change
      R ^ 2
          *
        ∫ ξ : H3FourierPoint3,
          top ξ
          ∂(volume.restrict S)
        ≤
      ∫ ξ : H3FourierPoint3,
        fifth ξ
        ∂(volume.restrict S)

    rw [← integral_const_mul]

    exact
      integral_mono_ae
        ((hTopInt.const_mul (R ^ 2)).mono_measure
          Measure.restrict_le_self)
        (hFifthInt'.mono_measure
          Measure.restrict_le_self)
        hPoint

  have hSetLeWhole :
      (∫ ξ in S, fifth ξ ∂volume)
        ≤
      ∫ ξ : H3FourierPoint3, fifth ξ ∂volume := by

    exact
      integral_mono_measure
        Measure.restrict_le_self
        hFifthNonneg
        hFifthInt'

  have hWholeLe :
      (∫ ξ : H3FourierPoint3, fifth ξ ∂volume)
        ≤
      C := by

    simpa only [
      fifth,
      h3TerminalPhysicalFifthRadialMomentAt
    ] using
      hFifthMomentLe

  have hScaledLe :
      R ^ 2
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass t ht S
        ≤
      C :=
    le_trans
      hScaledSetLe
      (le_trans
        hSetLeWhole
        hWholeLe)

  have hScaledLt :
      R ^ 2
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass t ht S
        <
      R ^ 2 * δ := by

    exact
      lt_of_le_of_lt
        hScaledLe
        (by
          simpa only [mul_comm] using
            hCR2)

  exact
    lt_of_mul_lt_mul_left
      hScaledLt
      hR2.le

/-! ## One-extra-moment continuation theorem -/

/--
A terminal uniform fifth-radial raw-Fourier velocity moment bound is sufficient
for smooth continuation under the retained raw-Fourier `L²` Cauchy and
physical-vorticity endpoint assumptions.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_fifthRadialMomentUniformBound_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hFifth :
      H3TerminalPhysicalFifthRadialMomentUniformBoundAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hTopTail :
      H3TerminalPhysicalTopDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass :=
    physicalTopDissipationRadialTailTightAtEndpoint_of_fifthRadialMomentUniformBoundAtEndpoint
      hH3
      hClass
      hFifth

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalTopDissipationRadialTailTightness_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      hTopTail

/-! ## Necessary fifth-moment obstruction under hypothetical nonextension -/

/--
Under the retained endpoint hypotheses, hypothetical nonextension rules out a
uniform terminal ceiling for the fifth radial raw-Fourier velocity moment.
-/
theorem not_fifthRadialMomentUniformBoundAtEndpoint_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    ¬ H3TerminalPhysicalFifthRadialMomentUniformBoundAtEndpoint
        hH3 hClass := by

  intro hFifth

  exact
    hNoExtension
      (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_fifthRadialMomentUniformBound_of_actualVorticityStrongH3EndpointPath
        hH3
        hClass
        hPhysical
        hCauchy
        hFifth)

/-! ## Neutral formulation -/

/--
Neutral one-extra-moment alternative: either the H³ path extends smoothly
through `T`, or no uniform terminal fifth-radial raw-Fourier moment ceiling is
available.

This does not by itself assert a numerical divergence rate for the fifth
moment.
-/
theorem smoothContinuationExtension_or_not_fifthRadialMomentUniformBoundAtEndpoint
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
    ¬ H3TerminalPhysicalFifthRadialMomentUniformBoundAtEndpoint
        hH3 hClass := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (not_fifthRadialMomentUniformBoundAtEndpoint_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
