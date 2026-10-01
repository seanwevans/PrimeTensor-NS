import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationFifthRadialMomentCriterion

/-!
# Extended fifth-radial moment cascade from top-order radial escape

The preceding checkpoint showed that a uniform finite fifth-radial moment
ceiling would imply continuation.  Here the surviving nonextension obstruction
is sharpened quantitatively without assuming that the fifth moment is finite.

Define the extended fifth radial moment

    M₅⁺(t) = ∫⁻ q(ξ)^5 |û(t,ξ)|² dξ ∈ ℝ≥0∞.

If a measurable set `S` lies outside radial cutoff `R`, then

    R² q⁴ |û|² ≤ q⁵ |û|²

pointwise on `S`.  The top-order escape checkpoint already supplies a fixed
positive mass `δ` of `q⁴ |û|²` on sets outside cutoff `n+1`.  Therefore

    ofReal (((n+1)²) δ) ≤ M₅⁺(τₙ).

The real lower bound tends to `+∞`; hence the extended fifth radial moment tends
to `∞` in `ℝ≥0∞` along the same terminal sequence.

This statement remains valid whether each fifth moment is finite or infinite,
so it does not smuggle in an H⁴/H⁵-type integrability hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalExtendedFifthRadialMomentCascade
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalExtendedFifthRadialMomentCascade :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Extended fifth radial moment -/

/--
Extended fifth radial raw-Fourier moment.  The extended nonnegative codomain is
intentional: one extra radial moment need not be integrable at the base H³
level.
-/
noncomputable def h3TerminalPhysicalExtendedFifthRadialMomentAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T) : ℝ≥0∞ :=
  ∫⁻ ξ : H3FourierPoint3,
    ENNReal.ofReal
      (h3TerminalPhysicalFifthRadialDensityAt
        hH3 hClass t ht ξ)
    ∂volume

/-! ## Set-level radial lower bound -/

/--
If `S` is contained outside radial cutoff `R`, then the extended fifth moment
dominates `R²` times the finite top-order dissipation mass carried by `S`.
-/
theorem ofReal_radial_sq_mul_topDissipationSetMass_le_extendedFifthRadialMoment_of_setOutside
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hR : 0 ≤ R)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hOutside :
      S ⊆ (h3TerminalRadialFrequencyBelow R)ᶜ) :
    ENNReal.ofReal
      (
        R ^ 2
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass t ht S
      )
      ≤
    h3TerminalPhysicalExtendedFifthRadialMomentAt
      hH3 hClass t ht := by

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

  have hTopNonneg :
      0 ≤ᵐ[volume.restrict S] top := by
    filter_upwards with ξ
    dsimp only [top]
    exact
      mul_nonneg
        (pow_nonneg
          (h3FourierGradientSquare_nonneg ξ)
          4)
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

  have hIntegralBridge :
      ENNReal.ofReal
        (∫ ξ in S, top ξ ∂volume)
        =
      ∫⁻ ξ in S,
        ENNReal.ofReal (top ξ)
        ∂volume := by

    exact
      ofReal_integral_eq_lintegral_ofReal
        hTopInt.integrableOn
        hTopNonneg

  have hPointwise :
      ∀ ξ ∈ S,
        R ^ 2 * top ξ
          ≤
        fifth ξ := by

    intro ξ hξ

    have hOutsideξ :=
      hOutside hξ

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
        hR
        hRadial

  have hLIntegral :
      (∫⁻ ξ in S,
        ENNReal.ofReal
          (R ^ 2 * top ξ)
        ∂volume)
        ≤
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (fifth ξ)
        ∂volume := by

    apply
      setLIntegral_mono'
        hS

    intro ξ hξ

    exact
      ENNReal.ofReal_le_ofReal
        (hPointwise ξ hξ)

  have hSetLeWhole :
      (∫⁻ ξ in S,
        ENNReal.ofReal
          (fifth ξ)
        ∂volume)
        ≤
      ∫⁻ ξ : H3FourierPoint3,
        ENNReal.ofReal
          (fifth ξ)
        ∂volume := by

    exact
      lintegral_mono'
        Measure.restrict_le_self
        le_rfl

  unfold
    h3TerminalPhysicalTopDissipationSetMassAt
    h3TerminalPhysicalExtendedFifthRadialMomentAt

  change
    ENNReal.ofReal
      (
        R ^ 2
          *
        (∫ ξ in S, top ξ ∂volume)
      )
      ≤
    ∫⁻ ξ : H3FourierPoint3,
      ENNReal.ofReal
        (fifth ξ)
      ∂volume

  calc
    ENNReal.ofReal
        (
          R ^ 2
            *
          (∫ ξ in S, top ξ ∂volume)
        )
        =
      ENNReal.ofReal (R ^ 2)
        *
      ENNReal.ofReal
        (∫ ξ in S, top ξ ∂volume) := by
          rw [
            ENNReal.ofReal_mul
              (sq_nonneg R)
          ]

    _ =
      ENNReal.ofReal (R ^ 2)
        *
      (∫⁻ ξ in S,
        ENNReal.ofReal (top ξ)
        ∂volume) := by
          rw [
            hIntegralBridge
          ]

    _ =
      ∫⁻ ξ in S,
        ENNReal.ofReal (R ^ 2)
          *
        ENNReal.ofReal (top ξ)
        ∂volume := by
          symm
          exact
            lintegral_const_mul'
              (ENNReal.ofReal (R ^ 2))
              (fun ξ =>
                ENNReal.ofReal (top ξ))
              ENNReal.ofReal_lt_top.ne

    _ =
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (R ^ 2 * top ξ)
        ∂volume := by

          apply
            setLIntegral_congr_fun
              hS

          intro ξ hξ

          change
            ENNReal.ofReal (R ^ 2)
                *
              ENNReal.ofReal (top ξ)
              =
            ENNReal.ofReal
              (R ^ 2 * top ξ)

          exact
            (
              ENNReal.ofReal_mul
                (sq_nonneg R)
            ).symm

    _ ≤
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (fifth ξ)
        ∂volume :=
          hLIntegral

    _ ≤
      ∫⁻ ξ : H3FourierPoint3,
        ENNReal.ofReal
          (fifth ξ)
        ∂volume :=
          hSetLeWhole

/-! ## Quadratic extended fifth-moment escape package -/

/--
A terminal sequence on which the extended fifth radial moment has an explicit
quadratic lower bound and tends to `∞`.
-/
def H3TerminalPhysicalExtendedFifthRadialMomentQuadraticEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ τ : ℕ → ℝ,
      ∃ hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T,
        (
          ∀ n : ℕ,
            dist (τ n) T
              <
            (1 : ℝ) / ((n : ℝ) + 1)
        )
          ∧
        Tendsto τ atTop (𝓝 T)
          ∧
        (
          ∀ n : ℕ,
            ENNReal.ofReal
              (
                ((n : ℝ) + 1) ^ 2
                  *
                δ
              )
              ≤
            h3TerminalPhysicalExtendedFifthRadialMomentAt
              hH3 hClass (τ n) (hτ n)
        )
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalPhysicalExtendedFifthRadialMomentAt
                hH3 hClass (τ n) (hτ n)
          )
          atTop
          (𝓝 ∞)

/-! ## Top-order radial escape implies the extended fifth cascade -/

/--
Every top-order radial escape sequence forces quadratic growth of the extended
fifth radial moment along the same terminal times.
-/
theorem extendedFifthRadialMomentQuadraticEscapeSequence_of_topDissipationRadialEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape :
      H3TerminalPhysicalTopDissipationRadialEscapeSequence
        hH3 hClass) :
    H3TerminalPhysicalExtendedFifthRadialMomentQuadraticEscapeSequence
      hH3 hClass := by

  obtain
    ⟨
      δ,
      hδ,
      τ,
      S,
      hData,
      hτTendsto
    ⟩ :=
    hEscape

  have hChoice :
      ∀ n : ℕ,
        ∃ ht : τ n ∈ Set.Ioo a T,
          dist (τ n) T
              <
            (1 : ℝ) / ((n : ℝ) + 1)
            ∧
          MeasurableSet (S n)
            ∧
          S n
              ⊆
            (h3TerminalRadialFrequencyBelow
              ((n : ℝ) + 1))ᶜ
            ∧
          δ
              ≤
            h3TerminalPhysicalTopDissipationSetMassAt
              hH3 hClass (τ n) ht (S n) := by

    intro n
    exact
      hData n

  choose ht hNear hSMeas hOutside hMass using hChoice

  have hLower :
      ∀ n : ℕ,
        ENNReal.ofReal
          (
            ((n : ℝ) + 1) ^ 2
              *
            δ
          )
          ≤
        h3TerminalPhysicalExtendedFifthRadialMomentAt
          hH3 hClass (τ n) (ht n) := by

    intro n

    let R : ℝ :=
      (n : ℝ) + 1

    have hR :
        0 ≤ R := by
      dsimp only [R]
      positivity

    have hMassScaled :
        R ^ 2 * δ
          ≤
        R ^ 2
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass (τ n) (ht n) (S n) :=
      mul_le_mul_of_nonneg_left
        (hMass n)
        (sq_nonneg R)

    have hOfRealScaled :
        ENNReal.ofReal
          (R ^ 2 * δ)
          ≤
        ENNReal.ofReal
          (
            R ^ 2
              *
            h3TerminalPhysicalTopDissipationSetMassAt
              hH3 hClass (τ n) (ht n) (S n)
          ) :=
      ENNReal.ofReal_le_ofReal
        hMassScaled

    have hExtended :=
      ofReal_radial_sq_mul_topDissipationSetMass_le_extendedFifthRadialMoment_of_setOutside
        hH3
        hClass
        (ht n)
        hR
        (S n)
        (hSMeas n)
        (hOutside n)

    exact
      hOfRealScaled.trans
        hExtended

  have hRadius :
      Tendsto
        (fun n : ℕ => (n : ℝ) + 1)
        atTop
        atTop := by

    exact
      tendsto_atTop_add_const_right
        atTop
        (1 : ℝ)
        tendsto_natCast_atTop_atTop

  have hSquare :
      Tendsto
        (fun n : ℕ =>
          ((n : ℝ) + 1) ^ 2)
        atTop
        atTop := by

    simpa only [pow_two] using
      hRadius.atTop_mul_atTop₀
        hRadius

  have hRealLowerTop :
      Tendsto
        (
          fun n : ℕ =>
            ((n : ℝ) + 1) ^ 2
              *
            δ
        )
        atTop
        atTop := by

    have hScaled :=
      hSquare.const_mul_atTop
        hδ

    simpa only [mul_comm] using
      hScaled

  have hOfRealLowerTop :
      Tendsto
        (
          fun n : ℕ =>
            ENNReal.ofReal
              (
                ((n : ℝ) + 1) ^ 2
                  *
                δ
              )
        )
        atTop
        (𝓝 ∞) := by

    exact
      ENNReal.tendsto_ofReal_atTop.comp
        hRealLowerTop

  have hMomentTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalPhysicalExtendedFifthRadialMomentAt
              hH3 hClass (τ n) (ht n)
        )
        atTop
        (𝓝 ∞) := by

    exact
      tendsto_nhds_top_mono'
        hOfRealLowerTop
        hLower

  exact
    ⟨
      δ,
      hδ,
      τ,
      ht,
      hNear,
      hτTendsto,
      hLower,
      hMomentTop
    ⟩

/-! ## Endpoint consequence -/

/--
Under the retained endpoint hypotheses, hypothetical nonextension forces an
explicit terminal sequence on which the extended fifth radial moment grows at
least quadratically in the escape index and tends to `∞`.
-/
theorem extendedFifthRadialMomentQuadraticEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalPhysicalExtendedFifthRadialMomentQuadraticEscapeSequence
      hH3 hClass := by

  exact
    extendedFifthRadialMomentQuadraticEscapeSequence_of_topDissipationRadialEscapeSequence
      hH3
      hClass
      (physicalTopDissipationRadialEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hCauchy)

/-! ## Neutral formulation -/

/--
Neutral endpoint alternative: either the H³ path extends smoothly through `T`,
or there is a terminal sequence on which the extended fifth radial raw-Fourier
moment tends to infinity with an explicit quadratic lower bound.

No existence claim for the nonextension branch is made.
-/
theorem smoothContinuationExtension_or_extendedFifthRadialMomentQuadraticEscapeSequence
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
    H3TerminalPhysicalExtendedFifthRadialMomentQuadraticEscapeSequence
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
        (extendedFifthRadialMomentQuadraticEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
