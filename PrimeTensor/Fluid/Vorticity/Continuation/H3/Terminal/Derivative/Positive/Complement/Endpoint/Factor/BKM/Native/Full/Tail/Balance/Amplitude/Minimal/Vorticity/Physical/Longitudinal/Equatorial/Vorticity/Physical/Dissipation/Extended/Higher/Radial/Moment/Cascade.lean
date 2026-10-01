import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Extended.Fifth.Radial.Moment.Cascade

/-!
# Universal extended higher-radial moment cascade

The preceding checkpoint extracted a quadratic blowup sequence for the extended
fifth radial moment from top-order physical dissipation radial escape.

The same escaped top-order mass forces an entire hierarchy simultaneously.

For a natural shift `m`, define the extended radial moment

    M_{4+m}⁺(t)
      =
    ∫⁻ q(ξ)^(4+m) |û(t,ξ)|² dξ,

where `q = |D(ξ)|²`.

On a set outside radial cutoff `R`,

    R² ≤ q,

so

    (R²)^m q⁴ |û|²
      ≤
    q^m q⁴ |û|²
      =
    q^(4+m) |û|².

The top-order radial escape sequence carries a fixed positive `q⁴` mass `δ`
outside cutoff `n+1`. Hence, on the same terminal times and the same measurable
sets,

    M_{4+m}⁺(τₙ)
      ≥
    δ * (((n+1)²)^m).

For every fixed `m ≠ 0`, that lower bound tends to infinity.  Thus hypothetical
nonextension forces all strictly higher radial moments above the top H³
dissipation block to diverge along one common terminal sequence.

No finite higher-moment integrability is assumed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalExtendedHigherRadialMomentCascade
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalExtendedHigherRadialMomentCascade :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Generic higher radial density and extended moment -/

/--
The `m`-shifted radial density above the physical top-order H³ dissipation
block:

    q^(4+m) |û|².
-/
noncomputable def h3TerminalPhysicalHigherRadialDensityAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (m : ℕ)
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
  h3FourierGradientSquare ξ ^ (4 + m)
    *
  velocityH3FourierMassDensityAt
    u t hInt hMeas ξ

theorem h3TerminalPhysicalHigherRadialDensityAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (m : ℕ)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T)
    (ξ : H3FourierPoint3) :
    0 ≤
      h3TerminalPhysicalHigherRadialDensityAt
        hH3 hClass m t ht ξ := by

  unfold h3TerminalPhysicalHigherRadialDensityAt

  exact
    mul_nonneg
      (pow_nonneg
        (h3FourierGradientSquare_nonneg ξ)
        (4 + m))
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
Extended `m`-shifted radial moment above the top H³ dissipation block.
-/
noncomputable def h3TerminalPhysicalExtendedHigherRadialMomentAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (m : ℕ)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T) : ℝ≥0∞ :=
  ∫⁻ ξ : H3FourierPoint3,
    ENNReal.ofReal
      (h3TerminalPhysicalHigherRadialDensityAt
        hH3 hClass m t ht ξ)
    ∂volume

/--
The generic `m = 1` density is exactly the fifth-radial density.
-/
theorem h3TerminalPhysicalHigherRadialDensityAt_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T)
    (ξ : H3FourierPoint3) :
    h3TerminalPhysicalHigherRadialDensityAt
        hH3 hClass 1 t ht ξ
      =
    h3TerminalPhysicalFifthRadialDensityAt
      hH3 hClass t ht ξ := by

  unfold
    h3TerminalPhysicalHigherRadialDensityAt
    h3TerminalPhysicalFifthRadialDensityAt

  norm_num

/--
The generic `m = 1` extended moment is the already-defined extended fifth
radial moment.
-/
theorem h3TerminalPhysicalExtendedHigherRadialMomentAt_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalExtendedHigherRadialMomentAt
        hH3 hClass 1 t ht
      =
    h3TerminalPhysicalExtendedFifthRadialMomentAt
      hH3 hClass t ht := by

  unfold
    h3TerminalPhysicalExtendedHigherRadialMomentAt
    h3TerminalPhysicalExtendedFifthRadialMomentAt

  apply lintegral_congr

  intro ξ

  rw [
    h3TerminalPhysicalHigherRadialDensityAt_one
      hH3 hClass t ht ξ
  ]

/-! ## Pointwise generic radial domination -/

/--
Outside radial cutoff `R`, the `m`th power of `R²` times the top-order density
is bounded by the `m`-shifted higher radial density.
-/
theorem radial_sq_pow_mul_topDensity_le_higherRadialDensity_of_cutoff_le_gradientMagnitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (m : ℕ)
    (ht : t ∈ Set.Ioo a T)
    (hR : 0 ≤ R)
    {ξ : H3FourierPoint3}
    (hξ :
      R ≤ h3FourierGradientMagnitude ξ) :
    (R ^ 2) ^ m
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
    h3TerminalPhysicalHigherRadialDensityAt
      hH3 hClass m t ht ξ := by

  let q : ℝ :=
    h3FourierGradientSquare ξ

  let mass : ℝ :=
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

  have hq0 :
      0 ≤ q := by
    dsimp only [q]
    exact
      h3FourierGradientSquare_nonneg ξ

  have hPow :
      (R ^ 2) ^ m
        ≤
      q ^ m :=
    pow_le_pow_left₀
      (sq_nonneg R)
      hq
      m

  have hMass :
      0 ≤ mass := by
    dsimp only [mass]
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

  have hTopNonneg :
      0 ≤ q ^ 4 * mass :=
    mul_nonneg
      (pow_nonneg hq0 4)
      hMass

  have hMul :
      (R ^ 2) ^ m
          *
        (q ^ 4 * mass)
        ≤
      q ^ m
          *
        (q ^ 4 * mass) :=
    mul_le_mul_of_nonneg_right
      hPow
      hTopNonneg

  unfold h3TerminalPhysicalHigherRadialDensityAt

  change
    (R ^ 2) ^ m
        *
      (q ^ 4 * mass)
      ≤
    q ^ (4 + m) * mass

  calc
    (R ^ 2) ^ m
        *
      (q ^ 4 * mass)
        ≤
      q ^ m
        *
      (q ^ 4 * mass) :=
        hMul

    _ =
      q ^ (4 + m) * mass := by
        rw [pow_add]
        ring

/-! ## Set-level generic radial domination -/

/--
On a measurable set outside cutoff `R`, the extended `m`-shifted radial moment
dominates `(R²)^m` times the finite top-order dissipation mass on that set.
-/
theorem ofReal_radial_sq_pow_mul_topDissipationSetMass_le_extendedHigherRadialMoment_of_setOutside
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (m : ℕ)
    (ht : t ∈ Set.Ioo a T)
    (hR : 0 ≤ R)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hOutside :
      S ⊆ (h3TerminalRadialFrequencyBelow R)ᶜ) :
    ENNReal.ofReal
      (
        (R ^ 2) ^ m
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass t ht S
      )
      ≤
    h3TerminalPhysicalExtendedHigherRadialMomentAt
      hH3 hClass m t ht := by

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

  let higher : H3FourierPoint3 → ℝ :=
    h3TerminalPhysicalHigherRadialDensityAt
      hH3 hClass m t ht

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
        (R ^ 2) ^ m * top ξ
          ≤
        higher ξ := by

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

    dsimp only [top, higher]

    exact
      radial_sq_pow_mul_topDensity_le_higherRadialDensity_of_cutoff_le_gradientMagnitude
        hH3
        hClass
        m
        ht
        hR
        hRadial

  have hLIntegral :
      (∫⁻ ξ in S,
        ENNReal.ofReal
          ((R ^ 2) ^ m * top ξ)
        ∂volume)
        ≤
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (higher ξ)
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
          (higher ξ)
        ∂volume)
        ≤
      ∫⁻ ξ : H3FourierPoint3,
        ENNReal.ofReal
          (higher ξ)
        ∂volume := by

    exact
      lintegral_mono'
        Measure.restrict_le_self
        le_rfl

  unfold
    h3TerminalPhysicalTopDissipationSetMassAt
    h3TerminalPhysicalExtendedHigherRadialMomentAt

  change
    ENNReal.ofReal
      (
        (R ^ 2) ^ m
          *
        (∫ ξ in S, top ξ ∂volume)
      )
      ≤
    ∫⁻ ξ : H3FourierPoint3,
      ENNReal.ofReal
        (higher ξ)
      ∂volume

  calc
    ENNReal.ofReal
        (
          (R ^ 2) ^ m
            *
          (∫ ξ in S, top ξ ∂volume)
        )
        =
      ENNReal.ofReal ((R ^ 2) ^ m)
        *
      ENNReal.ofReal
        (∫ ξ in S, top ξ ∂volume) := by

          rw [
            ENNReal.ofReal_mul
              (pow_nonneg (sq_nonneg R) m)
          ]

    _ =
      ENNReal.ofReal ((R ^ 2) ^ m)
        *
      (∫⁻ ξ in S,
        ENNReal.ofReal (top ξ)
        ∂volume) := by

          rw [
            hIntegralBridge
          ]

    _ =
      ∫⁻ ξ in S,
        ENNReal.ofReal ((R ^ 2) ^ m)
          *
        ENNReal.ofReal (top ξ)
        ∂volume := by

          symm

          exact
            lintegral_const_mul'
              (ENNReal.ofReal ((R ^ 2) ^ m))
              (fun ξ =>
                ENNReal.ofReal (top ξ))
              ENNReal.ofReal_lt_top.ne

    _ =
      ∫⁻ ξ in S,
        ENNReal.ofReal
          ((R ^ 2) ^ m * top ξ)
        ∂volume := by

          apply
            setLIntegral_congr_fun
              hS

          intro ξ hξ

          change
            ENNReal.ofReal ((R ^ 2) ^ m)
                *
              ENNReal.ofReal (top ξ)
              =
            ENNReal.ofReal
              ((R ^ 2) ^ m * top ξ)

          exact
            (
              ENNReal.ofReal_mul
                (pow_nonneg (sq_nonneg R) m)
            ).symm

    _ ≤
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (higher ξ)
        ∂volume :=
          hLIntegral

    _ ≤
      ∫⁻ ξ : H3FourierPoint3,
        ENNReal.ofReal
          (higher ξ)
        ∂volume :=
          hSetLeWhole

/-! ## One common terminal sequence for every higher moment -/

/--
One terminal sequence simultaneously carries polynomial lower bounds and
extended blowup for every radial moment strictly above the top H³ dissipation
block.
-/
def H3TerminalPhysicalExtendedHigherRadialMomentUniversalEscapeSequence
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
        ∀ m : ℕ,
          m ≠ 0
            →
          (
            (
              ∀ n : ℕ,
                ENNReal.ofReal
                  (
                    (((n : ℝ) + 1) ^ 2) ^ m
                      *
                    δ
                  )
                  ≤
                h3TerminalPhysicalExtendedHigherRadialMomentAt
                  hH3 hClass m (τ n) (hτ n)
            )
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalPhysicalExtendedHigherRadialMomentAt
                    hH3 hClass m (τ n) (hτ n)
              )
              atTop
              (𝓝 ∞)
          )

/--
A top-order radial escape sequence forces the whole extended higher-moment
hierarchy to diverge along one common terminal sequence.
-/
theorem extendedHigherRadialMomentUniversalEscapeSequence_of_topDissipationRadialEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape :
      H3TerminalPhysicalTopDissipationRadialEscapeSequence
        hH3 hClass) :
    H3TerminalPhysicalExtendedHigherRadialMomentUniversalEscapeSequence
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

  intro m hm

  have hLower :
      ∀ n : ℕ,
        ENNReal.ofReal
          (
            (((n : ℝ) + 1) ^ 2) ^ m
              *
            δ
          )
          ≤
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass m (τ n) (ht n) := by

    intro n

    let R : ℝ :=
      (n : ℝ) + 1

    have hR :
        0 ≤ R := by
      dsimp only [R]
      positivity

    have hFactorNonneg :
        0 ≤ (R ^ 2) ^ m :=
      pow_nonneg
        (sq_nonneg R)
        m

    have hMassScaled :
        (R ^ 2) ^ m * δ
          ≤
        (R ^ 2) ^ m
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass (τ n) (ht n) (S n) :=
      mul_le_mul_of_nonneg_left
        (hMass n)
        hFactorNonneg

    have hOfRealScaled :
        ENNReal.ofReal
          ((R ^ 2) ^ m * δ)
          ≤
        ENNReal.ofReal
          (
            (R ^ 2) ^ m
              *
            h3TerminalPhysicalTopDissipationSetMassAt
              hH3 hClass (τ n) (ht n) (S n)
          ) :=
      ENNReal.ofReal_le_ofReal
        hMassScaled

    have hExtended :=
      ofReal_radial_sq_pow_mul_topDissipationSetMass_le_extendedHigherRadialMoment_of_setOutside
        hH3
        hClass
        m
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

  have hPowerMap :
      Tendsto
        (fun x : ℝ => x ^ m)
        atTop
        atTop :=
    tendsto_pow_atTop
      hm

  have hPower :
      Tendsto
        (
          fun n : ℕ =>
            (((n : ℝ) + 1) ^ 2) ^ m
        )
        atTop
        atTop :=
    hPowerMap.comp
      hSquare

  have hRealLowerTop :
      Tendsto
        (
          fun n : ℕ =>
            (((n : ℝ) + 1) ^ 2) ^ m
              *
            δ
        )
        atTop
        atTop := by

    have hScaled :=
      hPower.const_mul_atTop
        hδ

    simpa only [mul_comm] using
      hScaled

  have hOfRealLowerTop :
      Tendsto
        (
          fun n : ℕ =>
            ENNReal.ofReal
              (
                (((n : ℝ) + 1) ^ 2) ^ m
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
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass m (τ n) (ht n)
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
common terminal sequence on which every strictly higher extended radial moment
diverges, with the explicit `2m`-degree indexed lower bound.
-/
theorem extendedHigherRadialMomentUniversalEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalPhysicalExtendedHigherRadialMomentUniversalEscapeSequence
      hH3 hClass := by

  exact
    extendedHigherRadialMomentUniversalEscapeSequence_of_topDissipationRadialEscapeSequence
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
Neutral endpoint alternative: either the path extends smoothly through `T`, or
there is one terminal sequence on which every extended radial moment strictly
above the top H³ dissipation block tends to infinity with its natural
polynomial indexed lower bound.

No existence claim for the nonextension branch is made.
-/
theorem smoothContinuationExtension_or_extendedHigherRadialMomentUniversalEscapeSequence
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
    H3TerminalPhysicalExtendedHigherRadialMomentUniversalEscapeSequence
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
        (extendedHigherRadialMomentUniversalEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
