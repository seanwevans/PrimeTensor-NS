import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Extended.Exponential.Radial.Moment.Cascade

/-!
# Universal coercive radial-weight cascade

The preceding checkpoints lifted top-order radial escape first to every higher
polynomial radial moment and then to every fixed positive exponential radial
weight.  Both are instances of one order-theoretic mechanism.

Let

    w : ℝ → ℝ

be a radial weight which is

* nonnegative,
* monotone, and
* coercive in the sense `w(r) → +∞` as `r → +∞`.

Define the extended weighted top-order dissipation moment

    M_w⁺(t)
      =
    ∫⁻ w(|D(ξ)|) q(ξ)^4 |û(t,ξ)|² dξ.

If `S` lies outside radial cutoff `R`, monotonicity gives

    w(R) ≤ w(|D(ξ)|)

on `S`, and therefore

    w(R) · topMass(S) ≤ M_w⁺(t).

The established top-order radial escape sequence carries a fixed positive mass
`δ` outside cutoff `n+1`.  Hence one common terminal sequence satisfies

    ofReal (w(n+1) δ) ≤ M_w⁺(τₙ)

for every admissible coercive radial weight `w`.  Since `w(n+1) → +∞`, each
such weighted extended moment tends to `∞`.

This is the invariant closure of the polynomial and exponential radial-weight
cascades.  It makes no claim that the nonextension branch is realizable.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalCoerciveRadialWeightCascade
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalCoerciveRadialWeightCascade :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Admissible coercive radial weights -/

/--
A nonnegative monotone radial weight diverging to `+∞`.
-/
def H3TerminalCoerciveRadialWeight
    (w : ℝ → ℝ) : Prop :=
  (∀ r : ℝ, 0 ≤ w r)
    ∧
  Monotone w
    ∧
  Tendsto w atTop atTop

theorem H3TerminalCoerciveRadialWeight.nonneg
    {w : ℝ → ℝ}
    (hw : H3TerminalCoerciveRadialWeight w)
    (r : ℝ) :
    0 ≤ w r :=
  hw.1 r

theorem H3TerminalCoerciveRadialWeight.monotone
    {w : ℝ → ℝ}
    (hw : H3TerminalCoerciveRadialWeight w) :
    Monotone w :=
  hw.2.1

theorem H3TerminalCoerciveRadialWeight.tendsto_atTop
    {w : ℝ → ℝ}
    (hw : H3TerminalCoerciveRadialWeight w) :
    Tendsto w atTop atTop :=
  hw.2.2

/-! ## Generic weighted top-order density -/

/--
Top-order physical H³ dissipation density multiplied by a radial weight
`w(|D|)`.
-/
noncomputable def h3TerminalPhysicalRadialWeightedTopDissipationDensityAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (w : ℝ → ℝ)
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
  w (h3FourierGradientMagnitude ξ)
    *
  (
    h3FourierGradientSquare ξ ^ 4
      *
    velocityH3FourierMassDensityAt
      u t hInt hMeas ξ
  )

theorem h3TerminalPhysicalRadialWeightedTopDissipationDensityAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {w : ℝ → ℝ}
    (hw : H3TerminalCoerciveRadialWeight w)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T)
    (ξ : H3FourierPoint3) :
    0 ≤
      h3TerminalPhysicalRadialWeightedTopDissipationDensityAt
        hH3 hClass w t ht ξ := by

  unfold h3TerminalPhysicalRadialWeightedTopDissipationDensityAt

  exact
    mul_nonneg
      (hw.nonneg _)
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
Extended radial-weighted top-order physical H³ dissipation moment.
-/
noncomputable def h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (w : ℝ → ℝ)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T) : ℝ≥0∞ :=
  ∫⁻ ξ : H3FourierPoint3,
    ENNReal.ofReal
      (h3TerminalPhysicalRadialWeightedTopDissipationDensityAt
        hH3 hClass w t ht ξ)
    ∂volume

/-! ## Pointwise high-radial domination -/

/--
Outside radial cutoff `R`, monotonicity of `w` gives
`w(R) * topDensity ≤ w(|D|) * topDensity`.
-/
theorem weight_cutoff_mul_topDensity_le_radialWeightedTopDensity_of_cutoff_le_gradientMagnitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {w : ℝ → ℝ}
    (hw : H3TerminalCoerciveRadialWeight w)
    (ht : t ∈ Set.Ioo a T)
    {ξ : H3FourierPoint3}
    (hξ :
      R ≤ h3FourierGradientMagnitude ξ) :
    w R
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
    h3TerminalPhysicalRadialWeightedTopDissipationDensityAt
      hH3 hClass w t ht ξ := by

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

  have hWeight :
      w R
        ≤
      w (h3FourierGradientMagnitude ξ) :=
    hw.monotone
      hξ

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

  unfold h3TerminalPhysicalRadialWeightedTopDissipationDensityAt

  change
    w R * top
      ≤
    w (h3FourierGradientMagnitude ξ) * top

  exact
    mul_le_mul_of_nonneg_right
      hWeight
      hTop

/-! ## Set-level radial-weight lower bound -/

/--
On a measurable set outside cutoff `R`, the extended weighted moment dominates
`w(R)` times the finite top-order dissipation mass carried by the set.
-/
theorem ofReal_weight_cutoff_mul_topDissipationSetMass_le_extendedRadialWeightedTopDissipationMoment_of_setOutside
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {w : ℝ → ℝ}
    (hw : H3TerminalCoerciveRadialWeight w)
    (ht : t ∈ Set.Ioo a T)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hOutside :
      S ⊆ (h3TerminalRadialFrequencyBelow R)ᶜ) :
    ENNReal.ofReal
      (
        w R
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass t ht S
      )
      ≤
    h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
      hH3 hClass w t ht := by

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

  let weighted : H3FourierPoint3 → ℝ :=
    h3TerminalPhysicalRadialWeightedTopDissipationDensityAt
      hH3 hClass w t ht

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
        w R * top ξ
          ≤
        weighted ξ := by

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

    dsimp only [top, weighted]

    exact
      weight_cutoff_mul_topDensity_le_radialWeightedTopDensity_of_cutoff_le_gradientMagnitude
        hH3
        hClass
        hw
        ht
        hRadial

  have hLIntegral :
      (∫⁻ ξ in S,
        ENNReal.ofReal
          (w R * top ξ)
        ∂volume)
        ≤
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (weighted ξ)
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
          (weighted ξ)
        ∂volume)
        ≤
      ∫⁻ ξ : H3FourierPoint3,
        ENNReal.ofReal
          (weighted ξ)
        ∂volume := by

    exact
      lintegral_mono'
        Measure.restrict_le_self
        le_rfl

  unfold
    h3TerminalPhysicalTopDissipationSetMassAt
    h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt

  change
    ENNReal.ofReal
      (
        w R
          *
        (∫ ξ in S, top ξ ∂volume)
      )
      ≤
    ∫⁻ ξ : H3FourierPoint3,
      ENNReal.ofReal
        (weighted ξ)
      ∂volume

  calc
    ENNReal.ofReal
        (
          w R
            *
          (∫ ξ in S, top ξ ∂volume)
        )
        =
      ENNReal.ofReal (w R)
        *
      ENNReal.ofReal
        (∫ ξ in S, top ξ ∂volume) := by

          rw [
            ENNReal.ofReal_mul
              (hw.nonneg R)
          ]

    _ =
      ENNReal.ofReal (w R)
        *
      (∫⁻ ξ in S,
        ENNReal.ofReal (top ξ)
        ∂volume) := by

          rw [
            hIntegralBridge
          ]

    _ =
      ∫⁻ ξ in S,
        ENNReal.ofReal (w R)
          *
        ENNReal.ofReal (top ξ)
        ∂volume := by

          symm

          exact
            lintegral_const_mul'
              (ENNReal.ofReal (w R))
              (fun ξ =>
                ENNReal.ofReal (top ξ))
              ENNReal.ofReal_lt_top.ne

    _ =
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (w R * top ξ)
        ∂volume := by

          apply
            setLIntegral_congr_fun
              hS

          intro ξ hξ

          change
            ENNReal.ofReal (w R)
                *
              ENNReal.ofReal (top ξ)
              =
            ENNReal.ofReal
              (w R * top ξ)

          exact
            (
              ENNReal.ofReal_mul
                (hw.nonneg R)
            ).symm

    _ ≤
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (weighted ξ)
        ∂volume :=
          hLIntegral

    _ ≤
      ∫⁻ ξ : H3FourierPoint3,
        ENNReal.ofReal
          (weighted ξ)
        ∂volume :=
          hSetLeWhole

/-! ## Universal coercive-weight escape package -/

/--
One terminal sequence simultaneously forces divergence for every admissible
coercive radial weight.
-/
def H3TerminalPhysicalCoerciveRadialWeightUniversalEscapeSequence
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
        ∀ w : ℝ → ℝ,
          H3TerminalCoerciveRadialWeight w
            →
          (
            (
              ∀ n : ℕ,
                ENNReal.ofReal
                  (
                    w ((n : ℝ) + 1)
                      *
                    δ
                  )
                  ≤
                h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
                  hH3 hClass w (τ n) (hτ n)
            )
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
                    hH3 hClass w (τ n) (hτ n)
              )
              atTop
              (𝓝 ∞)
          )

/--
Top-order radial escape forces every nonnegative monotone coercive radial
weight to diverge along the same terminal sequence.
-/
theorem coerciveRadialWeightUniversalEscapeSequence_of_topDissipationRadialEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape :
      H3TerminalPhysicalTopDissipationRadialEscapeSequence
        hH3 hClass) :
    H3TerminalPhysicalCoerciveRadialWeightUniversalEscapeSequence
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

  intro w hw

  have hLower :
      ∀ n : ℕ,
        ENNReal.ofReal
          (
            w ((n : ℝ) + 1)
              *
            δ
          )
          ≤
        h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
          hH3 hClass w (τ n) (ht n) := by

    intro n

    let R : ℝ :=
      (n : ℝ) + 1

    have hWeightNonneg :
        0 ≤ w R :=
      hw.nonneg R

    have hMassScaled :
        w R * δ
          ≤
        w R
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass (τ n) (ht n) (S n) :=
      mul_le_mul_of_nonneg_left
        (hMass n)
        hWeightNonneg

    have hOfRealScaled :
        ENNReal.ofReal
          (w R * δ)
          ≤
        ENNReal.ofReal
          (
            w R
              *
            h3TerminalPhysicalTopDissipationSetMassAt
              hH3 hClass (τ n) (ht n) (S n)
          ) :=
      ENNReal.ofReal_le_ofReal
        hMassScaled

    have hExtended :=
      ofReal_weight_cutoff_mul_topDissipationSetMass_le_extendedRadialWeightedTopDissipationMoment_of_setOutside
        hH3
        hClass
        hw
        (ht n)
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

  have hWeightTop :
      Tendsto
        (
          fun n : ℕ =>
            w ((n : ℝ) + 1)
        )
        atTop
        atTop :=
    hw.tendsto_atTop.comp
      hRadius

  have hRealLowerTop :
      Tendsto
        (
          fun n : ℕ =>
            w ((n : ℝ) + 1)
              *
            δ
        )
        atTop
        atTop := by

    exact
      hWeightTop.atTop_mul_const
        hδ

  have hOfRealLowerTop :
      Tendsto
        (
          fun n : ℕ =>
            ENNReal.ofReal
              (
                w ((n : ℝ) + 1)
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
            h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
              hH3 hClass w (τ n) (ht n)
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
common terminal sequence on which every nonnegative monotone coercive radial
top-dissipation weight diverges.
-/
theorem coerciveRadialWeightUniversalEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalPhysicalCoerciveRadialWeightUniversalEscapeSequence
      hH3 hClass := by

  exact
    coerciveRadialWeightUniversalEscapeSequence_of_topDissipationRadialEscapeSequence
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
or one common terminal sequence makes every nonnegative monotone coercive
radial top-dissipation weight diverge.

This theorem subsumes the previously packaged polynomial and positive
exponential radial-weight cascades.  It does not assert that the nonextension
branch occurs.
-/
theorem smoothContinuationExtension_or_coerciveRadialWeightUniversalEscapeSequence
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
    H3TerminalPhysicalCoerciveRadialWeightUniversalEscapeSequence
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
        (coerciveRadialWeightUniversalEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
