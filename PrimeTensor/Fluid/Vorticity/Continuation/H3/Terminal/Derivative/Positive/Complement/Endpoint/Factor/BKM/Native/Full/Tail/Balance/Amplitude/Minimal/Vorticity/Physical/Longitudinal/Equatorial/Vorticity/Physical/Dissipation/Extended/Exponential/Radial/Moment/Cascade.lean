import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Extended.Higher.Radial.Moment.Cascade

/-!
# Extended exponential radial-moment cascade

The polynomial higher-moment hierarchy extracted from top-order radial escape
can be strengthened without any higher Sobolev assumption.

For each fixed `σ > 0`, define the extended exponentially weighted top-order
dissipation moment

    Eσ⁺(t)
      =
    ∫⁻ exp(σ |D(ξ)|) q(ξ)^4 |û(t,ξ)|² dξ,

where `q = |D(ξ)|²`.

If a measurable set `S` lies outside radial cutoff `R`, then

    exp(σ R)
      ≤
    exp(σ |D(ξ)|)

on `S`.  Therefore

    exp(σ R) · topMass(S)
      ≤
    Eσ⁺(t).

The already-established top-order radial escape sequence carries a fixed
positive top-order mass `δ` outside cutoff `n+1`.  Hence the same times and
sets satisfy

    Eσ⁺(τₙ)
      ≥
    δ exp(σ (n+1)),

for every fixed `σ > 0`, and so `Eσ⁺(τₙ) → ∞`.

This is stated only as exponential spectral-weight blowup.  No analyticity
radius equivalence is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalExtendedExponentialRadialMomentCascade
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalExtendedExponentialRadialMomentCascade :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Exponentially weighted top-order density -/

/--
Exponentially weighted physical top-order H³ dissipation density.
-/
noncomputable def h3TerminalPhysicalExponentialTopDissipationDensityAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℝ)
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
  Real.exp
      (σ * h3FourierGradientMagnitude ξ)
    *
  (
    h3FourierGradientSquare ξ ^ 4
      *
    velocityH3FourierMassDensityAt
      u t hInt hMeas ξ
  )

theorem h3TerminalPhysicalExponentialTopDissipationDensityAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℝ)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T)
    (ξ : H3FourierPoint3) :
    0 ≤
      h3TerminalPhysicalExponentialTopDissipationDensityAt
        hH3 hClass σ t ht ξ := by

  unfold h3TerminalPhysicalExponentialTopDissipationDensityAt

  exact
    mul_nonneg
      (Real.exp_pos _).le
      (mul_nonneg
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
          ξ))

/--
Extended exponentially weighted top-order dissipation moment.
-/
noncomputable def h3TerminalPhysicalExtendedExponentialTopDissipationMomentAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℝ)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T) : ℝ≥0∞ :=
  ∫⁻ ξ : H3FourierPoint3,
    ENNReal.ofReal
      (h3TerminalPhysicalExponentialTopDissipationDensityAt
        hH3 hClass σ t ht ξ)
    ∂volume

/-! ## Pointwise high-radial exponential domination -/

/--
Outside radial cutoff `R`, the factor `exp(σ R)` times the top-order density
is bounded by the exponentially weighted top-order density whenever `σ ≥ 0`.
-/
theorem exp_cutoff_mul_topDensity_le_exponentialTopDensity_of_cutoff_le_gradientMagnitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R σ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hσ : 0 ≤ σ)
    {ξ : H3FourierPoint3}
    (hξ :
      R ≤ h3FourierGradientMagnitude ξ) :
    Real.exp (σ * R)
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
    h3TerminalPhysicalExponentialTopDissipationDensityAt
      hH3 hClass σ t ht ξ := by

  let top : ℝ :=
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

  have hExponent :
      σ * R
        ≤
      σ * h3FourierGradientMagnitude ξ :=
    mul_le_mul_of_nonneg_left
      hξ
      hσ

  have hExp :
      Real.exp (σ * R)
        ≤
      Real.exp
        (σ * h3FourierGradientMagnitude ξ) :=
    Real.exp_le_exp.mpr
      hExponent

  have hTop :
      0 ≤ top := by
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

  unfold h3TerminalPhysicalExponentialTopDissipationDensityAt

  change
    Real.exp (σ * R) * top
      ≤
    Real.exp
        (σ * h3FourierGradientMagnitude ξ)
      *
    top

  exact
    mul_le_mul_of_nonneg_right
      hExp
      hTop

/-! ## Set-level exponential lower bound -/

/--
On a measurable set outside cutoff `R`, the extended exponential moment
dominates `exp(σ R)` times the finite top-order dissipation mass on that set.
-/
theorem ofReal_exp_cutoff_mul_topDissipationSetMass_le_extendedExponentialTopDissipationMoment_of_setOutside
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R σ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hσ : 0 ≤ σ)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hOutside :
      S ⊆ (h3TerminalRadialFrequencyBelow R)ᶜ) :
    ENNReal.ofReal
      (
        Real.exp (σ * R)
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass t ht S
      )
      ≤
    h3TerminalPhysicalExtendedExponentialTopDissipationMomentAt
      hH3 hClass σ t ht := by

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

  let exponential : H3FourierPoint3 → ℝ :=
    h3TerminalPhysicalExponentialTopDissipationDensityAt
      hH3 hClass σ t ht

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
        Real.exp (σ * R) * top ξ
          ≤
        exponential ξ := by

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

    dsimp only [top, exponential]

    exact
      exp_cutoff_mul_topDensity_le_exponentialTopDensity_of_cutoff_le_gradientMagnitude
        hH3
        hClass
        ht
        hσ
        hRadial

  have hLIntegral :
      (∫⁻ ξ in S,
        ENNReal.ofReal
          (Real.exp (σ * R) * top ξ)
        ∂volume)
        ≤
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (exponential ξ)
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
          (exponential ξ)
        ∂volume)
        ≤
      ∫⁻ ξ : H3FourierPoint3,
        ENNReal.ofReal
          (exponential ξ)
        ∂volume := by

    exact
      lintegral_mono'
        Measure.restrict_le_self
        le_rfl

  unfold
    h3TerminalPhysicalTopDissipationSetMassAt
    h3TerminalPhysicalExtendedExponentialTopDissipationMomentAt

  change
    ENNReal.ofReal
      (
        Real.exp (σ * R)
          *
        (∫ ξ in S, top ξ ∂volume)
      )
      ≤
    ∫⁻ ξ : H3FourierPoint3,
      ENNReal.ofReal
        (exponential ξ)
      ∂volume

  calc
    ENNReal.ofReal
        (
          Real.exp (σ * R)
            *
          (∫ ξ in S, top ξ ∂volume)
        )
        =
      ENNReal.ofReal
          (Real.exp (σ * R))
        *
      ENNReal.ofReal
        (∫ ξ in S, top ξ ∂volume) := by

          rw [
            ENNReal.ofReal_mul
              (Real.exp_pos _).le
          ]

    _ =
      ENNReal.ofReal
          (Real.exp (σ * R))
        *
      (∫⁻ ξ in S,
        ENNReal.ofReal (top ξ)
        ∂volume) := by

          rw [
            hIntegralBridge
          ]

    _ =
      ∫⁻ ξ in S,
        ENNReal.ofReal
            (Real.exp (σ * R))
          *
        ENNReal.ofReal (top ξ)
        ∂volume := by

          symm

          exact
            lintegral_const_mul'
              (ENNReal.ofReal
                (Real.exp (σ * R)))
              (fun ξ =>
                ENNReal.ofReal (top ξ))
              ENNReal.ofReal_lt_top.ne

    _ =
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (Real.exp (σ * R) * top ξ)
        ∂volume := by

          apply
            setLIntegral_congr_fun
              hS

          intro ξ hξ

          change
            ENNReal.ofReal
                (Real.exp (σ * R))
                *
              ENNReal.ofReal (top ξ)
              =
            ENNReal.ofReal
              (Real.exp (σ * R) * top ξ)

          exact
            (
              ENNReal.ofReal_mul
                (Real.exp_pos _).le
            ).symm

    _ ≤
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (exponential ξ)
        ∂volume :=
          hLIntegral

    _ ≤
      ∫⁻ ξ : H3FourierPoint3,
        ENNReal.ofReal
          (exponential ξ)
        ∂volume :=
          hSetLeWhole

/-! ## One common terminal sequence for all positive exponential weights -/

/--
One terminal sequence simultaneously carries exponential lower bounds and
extended blowup for every fixed positive spectral exponential weight.
-/
def H3TerminalPhysicalExtendedExponentialTopDissipationUniversalEscapeSequence
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
        ∀ σ : ℝ,
          0 < σ
            →
          (
            (
              ∀ n : ℕ,
                ENNReal.ofReal
                  (
                    Real.exp
                        (σ * ((n : ℝ) + 1))
                      *
                    δ
                  )
                  ≤
                h3TerminalPhysicalExtendedExponentialTopDissipationMomentAt
                  hH3 hClass σ (τ n) (hτ n)
            )
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalPhysicalExtendedExponentialTopDissipationMomentAt
                    hH3 hClass σ (τ n) (hτ n)
              )
              atTop
              (𝓝 ∞)
          )

/--
A top-order radial escape sequence forces every fixed positive exponential
top-dissipation weight to diverge along the same terminal sequence.
-/
theorem extendedExponentialTopDissipationUniversalEscapeSequence_of_topDissipationRadialEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape :
      H3TerminalPhysicalTopDissipationRadialEscapeSequence
        hH3 hClass) :
    H3TerminalPhysicalExtendedExponentialTopDissipationUniversalEscapeSequence
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

  refine
    ⟨
      δ,
      hδ,
      τ,
      ht,
      hNear,
      hτTendsto,
      ?_
    ⟩

  intro σ hσ

  have hLower :
      ∀ n : ℕ,
        ENNReal.ofReal
          (
            Real.exp
                (σ * ((n : ℝ) + 1))
              *
            δ
          )
          ≤
        h3TerminalPhysicalExtendedExponentialTopDissipationMomentAt
          hH3 hClass σ (τ n) (ht n) := by

    intro n

    let R : ℝ :=
      (n : ℝ) + 1

    have hExpNonneg :
        0 ≤ Real.exp (σ * R) :=
      (Real.exp_pos _).le

    have hMassScaled :
        Real.exp (σ * R) * δ
          ≤
        Real.exp (σ * R)
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass (τ n) (ht n) (S n) :=
      mul_le_mul_of_nonneg_left
        (hMass n)
        hExpNonneg

    have hOfRealScaled :
        ENNReal.ofReal
          (Real.exp (σ * R) * δ)
          ≤
        ENNReal.ofReal
          (
            Real.exp (σ * R)
              *
            h3TerminalPhysicalTopDissipationSetMassAt
              hH3 hClass (τ n) (ht n) (S n)
          ) :=
      ENNReal.ofReal_le_ofReal
        hMassScaled

    have hExtended :=
      ofReal_exp_cutoff_mul_topDissipationSetMass_le_extendedExponentialTopDissipationMoment_of_setOutside
        hH3
        hClass
        (ht n)
        hσ.le
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

  have hScaledRadius :
      Tendsto
        (
          fun n : ℕ =>
            σ * ((n : ℝ) + 1)
        )
        atTop
        atTop := by

    exact
      hRadius.const_mul_atTop
        hσ

  have hExpTop :
      Tendsto
        (
          fun n : ℕ =>
            Real.exp
              (σ * ((n : ℝ) + 1))
        )
        atTop
        atTop := by

    exact
      Real.tendsto_exp_atTop.comp
        hScaledRadius

  have hRealLowerTop :
      Tendsto
        (
          fun n : ℕ =>
            Real.exp
                (σ * ((n : ℝ) + 1))
              *
            δ
        )
        atTop
        atTop := by

    exact
      hExpTop.atTop_mul_const
        hδ

  have hOfRealLowerTop :
      Tendsto
        (
          fun n : ℕ =>
            ENNReal.ofReal
              (
                Real.exp
                    (σ * ((n : ℝ) + 1))
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
            h3TerminalPhysicalExtendedExponentialTopDissipationMomentAt
              hH3 hClass σ (τ n) (ht n)
        )
        atTop
        (𝓝 ∞) := by

    exact
      tendsto_nhds_top_mono'
        hOfRealLowerTop
        hLower

  exact
    ⟨
      hLower,
      hMomentTop
    ⟩

/-! ## Endpoint consequence -/

/--
Under the retained endpoint hypotheses, hypothetical nonextension forces one
common terminal sequence on which every fixed positive exponentially weighted
top-dissipation moment diverges.
-/
theorem extendedExponentialTopDissipationUniversalEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalPhysicalExtendedExponentialTopDissipationUniversalEscapeSequence
      hH3 hClass := by

  exact
    extendedExponentialTopDissipationUniversalEscapeSequence_of_topDissipationRadialEscapeSequence
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
or one common terminal sequence makes every fixed positive exponential
top-dissipation spectral weight diverge, with the explicit lower bound
`δ exp(σ (n+1))`.

No analyticity-radius equivalence and no existence claim for the nonextension
branch are asserted.
-/
theorem smoothContinuationExtension_or_extendedExponentialTopDissipationUniversalEscapeSequence
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
    H3TerminalPhysicalExtendedExponentialTopDissipationUniversalEscapeSequence
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
        (extendedExponentialTopDissipationUniversalEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
