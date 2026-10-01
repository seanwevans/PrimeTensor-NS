import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Coercive.Radial.Weight.Criterion

/-!
# Coercive radial weights without monotonicity

The preceding coercive-weight criterion used monotonicity only to turn the
single cutoff value `w(R)` into a lower floor for every larger radial
frequency.  That hypothesis is stronger than necessary.

For the arguments here it is enough that

* `w` is globally nonnegative, and
* `w(r) → +∞` as `r → +∞`.

Indeed, for every prescribed floor `L`, coercivity itself supplies a threshold
`R₀` such that

    R₀ ≤ r  ->  L < w(r).

This eventual floor can be used directly on every escaped radial set.

Consequently:

1. a finite uniform terminal ceiling for any one nonnegative coercive radial
   weighted top-dissipation moment implies top-order radial-tail tightness and
   hence continuation;
2. top-order radial escape forces the corresponding extended weighted moment
   to diverge for every nonnegative coercive radial weight, even if the weight
   oscillates and is not monotone.

Thus monotonicity is not part of the true compactness mechanism.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalNonmonotoneCoerciveRadialWeight
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalNonmonotoneCoerciveRadialWeight :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Nonnegative coercive radial weights -/

/--
A globally nonnegative radial weight tending to `+∞`.

No monotonicity is required.
-/
def H3TerminalNonnegativeCoerciveRadialWeight
    (w : ℝ → ℝ) : Prop :=
  (∀ r : ℝ, 0 ≤ w r)
    ∧
  Tendsto w atTop atTop

theorem H3TerminalNonnegativeCoerciveRadialWeight.nonneg
    {w : ℝ → ℝ}
    (hw : H3TerminalNonnegativeCoerciveRadialWeight w)
    (r : ℝ) :
    0 ≤ w r :=
  hw.1 r

theorem H3TerminalNonnegativeCoerciveRadialWeight.tendsto_atTop
    {w : ℝ → ℝ}
    (hw : H3TerminalNonnegativeCoerciveRadialWeight w) :
    Tendsto w atTop atTop :=
  hw.2

/--
Every previously admissible monotone coercive radial weight is admissible in
the weaker nonmonotone sense.
-/
theorem H3TerminalCoerciveRadialWeight.toNonnegativeCoercive
    {w : ℝ → ℝ}
    (hw : H3TerminalCoerciveRadialWeight w) :
    H3TerminalNonnegativeCoerciveRadialWeight w :=
  ⟨hw.nonneg, hw.tendsto_atTop⟩

/-! ## Weighted density nonnegativity under the weaker hypothesis -/

theorem h3TerminalPhysicalRadialWeightedTopDissipationDensityAt_nonneg_of_nonnegativeCoercive
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {w : ℝ → ℝ}
    (hw : H3TerminalNonnegativeCoerciveRadialWeight w)
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

/-! ## Eventual-floor set estimate -/

/--
If the radial weight is bounded below by a nonnegative floor `L` on every
radius at least `R`, then its extended top-dissipation moment dominates `L`
times the finite top-order mass of any measurable set outside cutoff `R`.

This is the set-level estimate needed once monotonicity has been removed.
-/
theorem ofReal_floor_mul_topDissipationSetMass_le_extendedRadialWeightedTopDissipationMoment_of_setOutside
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R L : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {w : ℝ → ℝ}
    (hw : H3TerminalNonnegativeCoerciveRadialWeight w)
    (ht : t ∈ Set.Ioo a T)
    (hL : 0 ≤ L)
    (hFloor :
      ∀ r : ℝ,
        R ≤ r
          →
        L ≤ w r)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hOutside :
      S ⊆ (h3TerminalRadialFrequencyBelow R)ᶜ) :
    ENNReal.ofReal
      (
        L
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
        L * top ξ
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

    have hWeightFloor :
        L
          ≤
        w (h3FourierGradientMagnitude ξ) :=
      hFloor
        _
        hRadial

    have hTop :
        0 ≤ top ξ := by

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

    dsimp only [weighted]

    unfold
      h3TerminalPhysicalRadialWeightedTopDissipationDensityAt

    change
      L * top ξ
        ≤
      w (h3FourierGradientMagnitude ξ)
        *
      top ξ

    exact
      mul_le_mul_of_nonneg_right
        hWeightFloor
        hTop

  have hLIntegral :
      (∫⁻ ξ in S,
        ENNReal.ofReal
          (L * top ξ)
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
        L
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
          L
            *
          (∫ ξ in S, top ξ ∂volume)
        )
        =
      ENNReal.ofReal L
        *
      ENNReal.ofReal
        (∫ ξ in S, top ξ ∂volume) := by

          rw [
            ENNReal.ofReal_mul
              hL
          ]

    _ =
      ENNReal.ofReal L
        *
      (∫⁻ ξ in S,
        ENNReal.ofReal (top ξ)
        ∂volume) := by

          rw [
            hIntegralBridge
          ]

    _ =
      ∫⁻ ξ in S,
        ENNReal.ofReal L
          *
        ENNReal.ofReal (top ξ)
        ∂volume := by

          symm

          exact
            lintegral_const_mul'
              (ENNReal.ofReal L)
              (fun ξ =>
                ENNReal.ofReal (top ξ))
              ENNReal.ofReal_lt_top.ne

    _ =
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (L * top ξ)
        ∂volume := by

          apply
            setLIntegral_congr_fun
              hS

          intro ξ hξ

          change
            ENNReal.ofReal L
                *
              ENNReal.ofReal (top ξ)
              =
            ENNReal.ofReal
              (L * top ξ)

          exact
            (
              ENNReal.ofReal_mul
                hL
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

/-! ## A single nonmonotone coercive ceiling still gives tightness -/

/--
A finite uniform terminal ceiling for one nonnegative coercive radial weighted
top-order moment forces physical top-order radial-tail tightness.

Monotonicity of the weight is not needed.
-/
theorem physicalTopDissipationRadialTailTightAtEndpoint_of_nonnegativeCoerciveRadialWeightedTopDissipationUniformBoundAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {w : ℝ → ℝ}
    (hw : H3TerminalNonnegativeCoerciveRadialWeight w)
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

  let L : ℝ :=
    C / δ + 1

  have hL :
      0 < L := by

    dsimp only [L]

    have hDiv :
        0 ≤ C / δ :=
      div_nonneg
        hC
        hδ.le

    linarith

  have hWeightEventually :
      ∀ᶠ r : ℝ in atTop,
        L < w r :=
    hw.tendsto_atTop.eventually
      (eventually_gt_atTop L)

  obtain
    ⟨R₀, hR₀⟩ :=
    eventually_atTop.1
      hWeightEventually

  let R : ℝ :=
    max R₀ 1

  have hR :
      0 < R := by

    dsimp only [R]

    exact
      lt_of_lt_of_le
        zero_lt_one
        (le_max_right R₀ 1)

  have hR₀Le :
      R₀ ≤ R := by

    dsimp only [R]

    exact
      le_max_left R₀ 1

  have hFloor :
      ∀ r : ℝ,
        R ≤ r
          →
        L ≤ w r := by

    intro r hr

    exact
      le_of_lt
        (hR₀ r
          (hR₀Le.trans hr))

  have hCancel :
      (C / δ) * δ
        =
      C := by
    field_simp [ne_of_gt hδ]

  have hThreshold :
      C
        <
      L * δ := by

    dsimp only [L]

    rw [
      add_mul,
      hCancel,
      one_mul
    ]

    linarith

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
    ofReal_floor_mul_topDissipationSetMass_le_extendedRadialWeightedTopDissipationMoment_of_setOutside
      hH3
      hClass
      hw
      ht
      hL.le
      hFloor
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
          L
            *
          h3TerminalPhysicalTopDissipationSetMassAt
            hH3 hClass t ht S
        )
        ≤
      ENNReal.ofReal C :=
    hSetLower.trans
      hMomentUpper

  have hScaledReal :
      L
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass t ht S
        ≤
      C := by

    exact
      (ENNReal.ofReal_le_ofReal_iff hC).1
        hENNRealScaled

  have hStrictScaled :
      L
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass t ht S
        <
      L * δ :=
    lt_of_le_of_lt
      hScaledReal
      hThreshold

  exact
    lt_of_mul_lt_mul_left
      hStrictScaled
      hL.le

/-! ## Continuation from one arbitrary coercive weight -/

/--
Under the retained endpoint assumptions, a finite uniform ceiling for any one
nonnegative coercive radial top-dissipation weight is sufficient for smooth
continuation.  The weight need not be monotone.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_nonnegativeCoerciveRadialWeightedTopDissipationUniformBound_of_actualVorticityStrongH3EndpointPath
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
    (hw : H3TerminalNonnegativeCoerciveRadialWeight w)
    (hBound :
      H3TerminalPhysicalRadialWeightedTopDissipationUniformBoundAtEndpoint
        hH3 hClass w) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hTopTail :
      H3TerminalPhysicalTopDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass :=
    physicalTopDissipationRadialTailTightAtEndpoint_of_nonnegativeCoerciveRadialWeightedTopDissipationUniformBoundAtEndpoint
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

/-! ## Escape forces every nonmonotone coercive weighted moment to infinity -/

/--
One terminal radial-escape sequence forces the extended weighted top-order
moment to tend to `∞` for every nonnegative coercive radial weight, without
monotonicity.
-/
def H3TerminalPhysicalNonnegativeCoerciveRadialWeightUniversalEscapeSequence
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
          H3TerminalNonnegativeCoerciveRadialWeight w
            →
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
                  hH3 hClass w (τ n) (hτ n)
            )
            atTop
            (𝓝 ∞)

/--
Top-order radial escape forces every nonnegative coercive radial weighted
top-dissipation moment to diverge along one common terminal sequence.
-/
theorem nonnegativeCoerciveRadialWeightUniversalEscapeSequence_of_topDissipationRadialEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape :
      H3TerminalPhysicalTopDissipationRadialEscapeSequence
        hH3 hClass) :
    H3TerminalPhysicalNonnegativeCoerciveRadialWeightUniversalEscapeSequence
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

  apply
    ENNReal.tendsto_nhds_top_iff_nat.2

  intro k

  let L : ℝ :=
    ((k : ℝ) + 1) / δ

  have hL :
      0 < L := by

    dsimp only [L]

    exact
      div_pos
        (by positivity)
        hδ

  have hWeightEventually :
      ∀ᶠ r : ℝ in atTop,
        L < w r :=
    hw.tendsto_atTop.eventually
      (eventually_gt_atTop L)

  obtain
    ⟨R₀, hR₀⟩ :=
    eventually_atTop.1
      hWeightEventually

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

  have hCutoffPast :
      ∀ᶠ n : ℕ in atTop,
        R₀ ≤ (n : ℝ) + 1 :=
    hRadius.eventually
      (eventually_ge_atTop R₀)

  filter_upwards [hCutoffPast] with n hn

  have hFloor :
      ∀ r : ℝ,
        (n : ℝ) + 1 ≤ r
          →
        L ≤ w r := by

    intro r hr

    exact
      le_of_lt
        (hR₀ r
          (hn.trans hr))

  have hSetLower :=
    ofReal_floor_mul_topDissipationSetMass_le_extendedRadialWeightedTopDissipationMoment_of_setOutside
      hH3
      hClass
      hw
      (ht n)
      hL.le
      hFloor
      (S n)
      (hSMeas n)
      (hOutside n)

  have hMassScaled :
      L * δ
        ≤
      L
        *
      h3TerminalPhysicalTopDissipationSetMassAt
        hH3 hClass (τ n) (ht n) (S n) :=
    mul_le_mul_of_nonneg_left
      (hMass n)
      hL.le

  have hOfRealMassScaled :
      ENNReal.ofReal
        (L * δ)
        ≤
      ENNReal.ofReal
        (
          L
            *
          h3TerminalPhysicalTopDissipationSetMassAt
            hH3 hClass (τ n) (ht n) (S n)
        ) :=
    ENNReal.ofReal_le_ofReal
      hMassScaled

  have hLower :
      ENNReal.ofReal
        (L * δ)
        ≤
      h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
        hH3 hClass w (τ n) (ht n) :=
    hOfRealMassScaled.trans
      hSetLower

  have hCancel :
      L * δ
        =
      (k : ℝ) + 1 := by

    dsimp only [L]

    field_simp [ne_of_gt hδ]

  have hNatStrict :
      (k : ℝ≥0∞)
        <
      ENNReal.ofReal
        ((k : ℝ) + 1) := by

    simpa only [
      ENNReal.ofReal_natCast
    ] using
      (
        (
          ENNReal.ofReal_lt_ofReal_iff
            (by positivity :
              0 < (k : ℝ) + 1)
        ).2
          (by linarith :
            (k : ℝ) < (k : ℝ) + 1)
      )

  rw [hCancel] at hLower

  exact
    hNatStrict.trans_le
      hLower

/-! ## Endpoint consequences -/

/--
Under the retained endpoint hypotheses, hypothetical nonextension forces one
common terminal sequence on which every nonnegative coercive radial
top-dissipation weighted moment diverges, with no monotonicity assumption on
the weight.
-/
theorem nonnegativeCoerciveRadialWeightUniversalEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalPhysicalNonnegativeCoerciveRadialWeightUniversalEscapeSequence
      hH3 hClass := by

  exact
    nonnegativeCoerciveRadialWeightUniversalEscapeSequence_of_topDissipationRadialEscapeSequence
      hH3
      hClass
      (physicalTopDissipationRadialEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hCauchy)

/--
Under the retained endpoint assumptions, hypothetical nonextension rules out a
finite uniform terminal ceiling for every nonnegative coercive radial
top-dissipation weight, even when the weight is not monotone.
-/
theorem no_nonnegativeCoerciveRadialWeightedTopDissipationUniformBound_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
      H3TerminalNonnegativeCoerciveRadialWeight w
        →
      ¬ H3TerminalPhysicalRadialWeightedTopDissipationUniformBoundAtEndpoint
          hH3 hClass w := by

  intro w hw hBound

  exact
    hNoExtension
      (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_nonnegativeCoerciveRadialWeightedTopDissipationUniformBound_of_actualVorticityStrongH3EndpointPath
        hH3
        hClass
        hPhysical
        hCauchy
        hw
        hBound)

/-! ## Neutral formulation -/

/--
Neutral endpoint alternative: either the H³ path extends smoothly through `T`,
or one common terminal sequence makes every globally nonnegative radial weight
tending to `+∞` produce a divergent extended top-dissipation moment.

This strictly generalizes the earlier monotone coercive-weight cascade.
-/
theorem smoothContinuationExtension_or_nonnegativeCoerciveRadialWeightUniversalEscapeSequence
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
    H3TerminalPhysicalNonnegativeCoerciveRadialWeightUniversalEscapeSequence
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
        (nonnegativeCoerciveRadialWeightUniversalEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
