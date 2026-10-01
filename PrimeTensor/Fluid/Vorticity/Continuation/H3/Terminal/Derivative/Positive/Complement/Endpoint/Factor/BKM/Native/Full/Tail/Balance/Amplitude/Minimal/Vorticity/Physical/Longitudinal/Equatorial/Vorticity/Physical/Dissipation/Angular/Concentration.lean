import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Fourier.Identification

/-!
# Physical H³ dissipation concentration on shrinking equatorial cones

The preceding checkpoints isolate a high-radial angular obstruction in the
pair-difference weighted H³ dissipation density and identify the full physical
H³ dissipation exactly with its radial Fourier moment.

This file connects those two statements.

For one weighted spectral state `G`, define the single-time dissipation density

    q(ξ) * Σⱼ |Gⱼ(ξ)|².

For a genuine strict-time H³ state `G = W₃ û`, this is exactly

    (q + q² + q³ + q⁴) * Σⱼ |ûⱼ|²,

so its whole-space mass is precisely `velocityH3DissipationAt`.

For two states, the elementary estimate

    |G - H|² ≤ 2 |G|² + 2 |H|²

shows that the fourfold pair-difference control mass from the previous file is
bounded by an eightfold localized sum of the two single-time dissipation
densities.

Therefore every surviving high-radial raw-vorticity branch produces a genuine
localized physical-dissipation concentration branch on shrinking equatorial
cones.  This is still a necessary condition for hypothetical nonextension; no
claim that such a branch exists is made.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationAngularConcentration
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationAngularConcentration :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Single-time spectral dissipation density -/

/-- Full H³ dissipation density of one weighted three-component spectral state. -/
def h3TerminalSpectralDissipationSingleDensity
    (G : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) : ℝ :=
  h3FourierGradientSquare ξ
    *
  (
    norm (G 0 ξ) ^ 2
      +
    norm (G 1 ξ) ^ 2
      +
    norm (G 2 ξ) ^ 2
  )

/-- The single-time spectral dissipation density is nonnegative. -/
theorem h3TerminalSpectralDissipationSingleDensity_nonneg
    (G : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) :
    0 ≤ h3TerminalSpectralDissipationSingleDensity G ξ := by
  unfold h3TerminalSpectralDissipationSingleDensity
  exact
    mul_nonneg
      (h3FourierGradientSquare_nonneg ξ)
      (by positivity)

/-! ## Physical raw Fourier dissipation density -/

/-- The full radial dissipation density of one genuine physical H³ slice. -/
noncomputable def velocityH3FourierFullDissipationDensityAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (ξ : H3FourierPoint3) : ℝ :=
  h3FourierGradientSquare ξ
      * velocityH3FourierMassDensityAt u t hInt hMeas ξ
    +
  h3FourierGradientSquare ξ ^ 2
      * velocityH3FourierMassDensityAt u t hInt hMeas ξ
    +
  h3FourierGradientSquare ξ ^ 3
      * velocityH3FourierMassDensityAt u t hInt hMeas ξ
    +
  h3FourierGradientSquare ξ ^ 4
      * velocityH3FourierMassDensityAt u t hInt hMeas ξ

/-- The aggregate first radial density is integrable. -/
theorem velocityH3FourierFirstAggregateDensity_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ
          * velocityH3FourierMassDensityAt u t hInt hMeas ξ)
      volume := by
  unfold velocityH3FourierMassDensityAt
  simp_rw [Finset.mul_sum]
  apply integrable_finsetSum
  intro j hj
  exact
    integrable_h3FourierGradientSquare_mul_base_norm_sq
      hInt hMeas hFourier j

/-- Collapse the first radial component sum into one aggregate integral. -/
theorem velocityH3FourierFirstRadialMomentAt_eq_integral_massDensity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3FourierFirstRadialMomentAt u t hInt hMeas
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ
        * velocityH3FourierMassDensityAt u t hInt hMeas ξ := by
  unfold
    velocityH3FourierFirstRadialMomentAt
    velocityH3FourierMassDensityAt
  calc
    (∑ j : Fin 3,
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ
          * ‖velocityH3BaseFourierAt u t hInt hMeas j ξ‖ ^ 2)
        =
      ∫ ξ : H3FourierPoint3,
        ∑ j : Fin 3,
          h3FourierGradientSquare ξ
            * ‖velocityH3BaseFourierAt u t hInt hMeas j ξ‖ ^ 2
        ∂volume := by
      symm
      simpa using
        (integral_finsetSum
          (μ := volume)
          Finset.univ
          (fun j _ =>
            integrable_h3FourierGradientSquare_mul_base_norm_sq
              hInt hMeas hFourier j))
    _ =
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ
          * ∑ j : Fin 3,
              ‖velocityH3BaseFourierAt u t hInt hMeas j ξ‖ ^ 2
        ∂volume := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [Finset.mul_sum]

/-- The complete physical radial dissipation density is integrable on every
strict H³ energy-class slice. -/
theorem velocityH3FourierFullDissipationDensityAt_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    Integrable
      (velocityH3FourierFullDissipationDensityAt u t hInt hMeas)
      volume := by
  have h1 :=
    velocityH3FourierFirstAggregateDensity_integrable
      hInt hMeas hFourier
  have h2 :=
    velocityH3FourierSecondAggregateDensity_integrable
      hInt hMeas hFourier
  have h3 :=
    velocityH3FourierThirdAggregateDensity_integrable
      hInt hMeas hFourier
  have h4 :=
    h3Path_velocityH3FourierFourthAggregateDensity_integrable
      hH3 hClass ht hInt hMeas hFourier
  unfold velocityH3FourierFullDissipationDensityAt
  exact ((h1.add h2).add h3).add h4

/-- The integral of the complete physical radial density is exactly the full
physical H³ dissipation. -/
theorem integral_velocityH3FourierFullDissipationDensityAt_eq_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    (∫ ξ : H3FourierPoint3,
      velocityH3FourierFullDissipationDensityAt u t hInt hMeas ξ
      ∂volume)
      =
    velocityH3DissipationAt u t := by
  let f1 : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ
        * velocityH3FourierMassDensityAt u t hInt hMeas ξ
  let f2 : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 2
        * velocityH3FourierMassDensityAt u t hInt hMeas ξ
  let f3 : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 3
        * velocityH3FourierMassDensityAt u t hInt hMeas ξ
  let f4 : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 4
        * velocityH3FourierMassDensityAt u t hInt hMeas ξ

  have hf1 : Integrable f1 volume := by
    simpa only [f1] using
      velocityH3FourierFirstAggregateDensity_integrable
        hInt hMeas hFourier
  have hf2 : Integrable f2 volume := by
    simpa only [f2] using
      velocityH3FourierSecondAggregateDensity_integrable
        hInt hMeas hFourier
  have hf3 : Integrable f3 volume := by
    simpa only [f3] using
      velocityH3FourierThirdAggregateDensity_integrable
        hInt hMeas hFourier
  have hf4 : Integrable f4 volume := by
    simpa only [f4] using
      h3Path_velocityH3FourierFourthAggregateDensity_integrable
        hH3 hClass ht hInt hMeas hFourier

  change
    (∫ ξ : H3FourierPoint3,
      ((f1 ξ + f2 ξ) + f3 ξ) + f4 ξ ∂volume)
      =
    velocityH3DissipationAt u t

  calc
    (∫ ξ : H3FourierPoint3,
      ((f1 ξ + f2 ξ) + f3 ξ) + f4 ξ ∂volume)
        =
      (∫ ξ : H3FourierPoint3,
        (f1 ξ + f2 ξ) + f3 ξ ∂volume)
        +
      ∫ ξ : H3FourierPoint3, f4 ξ ∂volume := by

      simpa only [Pi.add_apply] using
        (integral_add ((hf1.add hf2).add hf3) hf4)

    _ =
      ((∫ ξ : H3FourierPoint3, f1 ξ ∂volume)
          +
        (∫ ξ : H3FourierPoint3, f2 ξ ∂volume)
          +
        (∫ ξ : H3FourierPoint3, f3 ξ ∂volume))
        +
      ∫ ξ : H3FourierPoint3, f4 ξ ∂volume := by

      have h12 :
          (∫ ξ : H3FourierPoint3, f1 ξ + f2 ξ ∂volume)
            =
          (∫ ξ : H3FourierPoint3, f1 ξ ∂volume)
            +
          ∫ ξ : H3FourierPoint3, f2 ξ ∂volume := by
        simpa only [Pi.add_apply] using
          (integral_add hf1 hf2)

      have h123 :
          (∫ ξ : H3FourierPoint3, (f1 ξ + f2 ξ) + f3 ξ ∂volume)
            =
          ((∫ ξ : H3FourierPoint3, f1 ξ ∂volume)
              +
            (∫ ξ : H3FourierPoint3, f2 ξ ∂volume))
              +
            ∫ ξ : H3FourierPoint3, f3 ξ ∂volume := by
        calc
          (∫ ξ : H3FourierPoint3, (f1 ξ + f2 ξ) + f3 ξ ∂volume)
              =
            (∫ ξ : H3FourierPoint3, f1 ξ + f2 ξ ∂volume)
              +
            ∫ ξ : H3FourierPoint3, f3 ξ ∂volume := by
              simpa only [Pi.add_apply] using
                (integral_add (hf1.add hf2) hf3)
          _ = _ := by rw [h12]

      exact
        congrArg
          (fun z : ℝ => z + ∫ ξ : H3FourierPoint3, f4 ξ ∂volume)
          h123

    _ =
      velocityH3FourierFullDissipationRadialMomentAt
        u t hInt hMeas := by

      unfold
        f1 f2 f3 f4
        velocityH3FourierFullDissipationRadialMomentAt

      rw [
        ← velocityH3FourierFirstRadialMomentAt_eq_integral_massDensity
          hInt hMeas hFourier,
        ← velocityH3FourierSecondRadialMomentAt_eq_integral_massDensity
          hInt hMeas hFourier,
        ← velocityH3FourierThirdRadialMomentAt_eq_integral_massDensity
          hInt hMeas hFourier,
        ← h3Path_velocityH3FourierFourthRadialMomentAt_eq_integral_massDensity
          hH3 hClass ht hInt hMeas hFourier
      ]

    _ = velocityH3DissipationAt u t := by

      exact
        (velocityH3DissipationAt_eq_fourierFullDissipationRadialMoment
          hH3 hClass ht hInt hMeas hFourier).symm

/-! ## Identify the canonical weighted state with the physical density -/

/-- The canonical strict-time spectral coordinate has the expected weighted raw
Fourier representative. -/
theorem h3TerminalVelocitySpectralStateAt_ae_weightedBaseFourierRaw
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      h3TerminalVelocitySpectralStateAt hH3 t ht j ξ)
      =ᵐ[volume]
    velocityH3WeightedBaseFourierRaw
      u t
      (hH3.velocity_h3_integrable t ht)
      (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes ht)
      j := by
  unfold h3TerminalVelocitySpectralStateAt
  exact
    velocityH3SpectralScalarAt_ae
      (velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes
        ht
        (hH3.velocity_h3_integrable t ht))
      j

/-- At a genuine physical slice, the one-state weighted spectral dissipation
density is almost everywhere the complete radial physical dissipation density. -/
theorem h3TerminalSpectralDissipationSingleDensity_ae_eq_physicalFullDensity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    (fun ξ : H3FourierPoint3 =>
      h3TerminalSpectralDissipationSingleDensity
        (h3TerminalVelocitySpectralStateAt hH3 t ht) ξ)
      =ᵐ[volume]
    velocityH3FourierFullDissipationDensityAt
      u t
      (hH3.velocity_h3_integrable t ht)
      (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes ht) := by
  have h0 :=
    h3TerminalVelocitySpectralStateAt_ae_weightedBaseFourierRaw
      hH3 ht (0 : Fin 3)
  have h1 :=
    h3TerminalVelocitySpectralStateAt_ae_weightedBaseFourierRaw
      hH3 ht (1 : Fin 3)
  have h2 :=
    h3TerminalVelocitySpectralStateAt_ae_weightedBaseFourierRaw
      hH3 ht (2 : Fin 3)

  filter_upwards [h0, h1, h2] with ξ h0ξ h1ξ h2ξ

  unfold h3TerminalSpectralDissipationSingleDensity

  rw [h0ξ, h1ξ, h2ξ]

  unfold
    velocityH3FourierFullDissipationDensityAt
    velocityH3FourierMassDensityAt
    velocityH3WeightedBaseFourierRaw

  simp only [Fin.sum_univ_three]

  have hW : 0 ≤ h3SobolevFrequencyWeight ξ :=
    le_of_lt (h3SobolevFrequencyWeight_pos ξ)

  simp only [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hW,
    mul_pow
  ]

  have hFactor (q w a b c : ℝ) :
      q * (w * a + w * b + w * c)
        =
      (q * w) * (a + b + c) := by
    ring

  rw [hFactor]
  rw [h3FourierGradientSquare_mul_h3SobolevFrequencyWeight_sq]
  ring

/-- The canonical one-state spectral dissipation density is integrable on a
strict H³ energy-class slice. -/
theorem h3TerminalSpectralDissipationSingleDensity_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    Integrable
      (h3TerminalSpectralDissipationSingleDensity
        (h3TerminalVelocitySpectralStateAt hH3 t htAbs))
      volume := by
  dsimp only
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt
  have hPhysical :
      Integrable
        (velocityH3FourierFullDissipationDensityAt u t hInt hMeas)
        volume :=
    velocityH3FourierFullDissipationDensityAt_integrable
      hH3 hClass ht hInt hMeas hFourier
  refine hPhysical.congr ?_
  exact
    (h3TerminalSpectralDissipationSingleDensity_ae_eq_physicalFullDensity
      hH3 htAbs).symm

/-- Whole-space mass of the one-state canonical weighted dissipation density is
exactly the physical `velocityH3DissipationAt`. -/
theorem integral_h3TerminalSpectralDissipationSingleDensity_eq_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    (∫ ξ : H3FourierPoint3,
      h3TerminalSpectralDissipationSingleDensity
        (h3TerminalVelocitySpectralStateAt hH3 t htAbs) ξ
      ∂volume)
      =
    velocityH3DissipationAt u t := by
  dsimp only
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt

  calc
    (∫ ξ : H3FourierPoint3,
      h3TerminalSpectralDissipationSingleDensity
        (h3TerminalVelocitySpectralStateAt hH3 t htAbs) ξ
      ∂volume)
        =
      ∫ ξ : H3FourierPoint3,
        velocityH3FourierFullDissipationDensityAt u t hInt hMeas ξ
        ∂volume := by
      apply integral_congr_ae
      exact
        h3TerminalSpectralDissipationSingleDensity_ae_eq_physicalFullDensity
          hH3 htAbs
    _ = velocityH3DissipationAt u t :=
      integral_velocityH3FourierFullDissipationDensityAt_eq_dissipation
        hH3 hClass ht hInt hMeas hFourier

/-! ## Localized physical dissipation masses -/

/-- Localized one-time physical H³ dissipation mass on the high-radial bad cone. -/
noncomputable def h3TerminalPhysicalDissipationBadConeHighRadialMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (i : Fin 3)
    (κ ρ t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) : ℝ≥0∞ :=
  ∫⁻ ξ in
      h3TerminalLongitudinalAngularBadCone i κ
        \
      h3TerminalRadialFrequencyBelow ρ,
    ENNReal.ofReal
      (h3TerminalSpectralDissipationSingleDensity
        (h3TerminalVelocitySpectralStateAt hH3 t ht) ξ)

/-- Whole-space extended mass of the canonical one-time dissipation density is
exactly the `ENNReal` lift of the physical H³ dissipation. -/
theorem lintegral_h3TerminalSpectralDissipationSingleDensity_eq_ofReal_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    (∫⁻ ξ : H3FourierPoint3,
      ENNReal.ofReal
        (h3TerminalSpectralDissipationSingleDensity
          (h3TerminalVelocitySpectralStateAt hH3 t htAbs) ξ)
      ∂volume)
      =
    ENNReal.ofReal (velocityH3DissipationAt u t) := by
  dsimp only
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hInt :=
    h3TerminalSpectralDissipationSingleDensity_integrable
      hH3 hClass ht
  have hNonneg :
      0 ≤ᵐ[volume]
        h3TerminalSpectralDissipationSingleDensity
          (h3TerminalVelocitySpectralStateAt hH3 t htAbs) := by
    filter_upwards with ξ
    exact
      h3TerminalSpectralDissipationSingleDensity_nonneg
        (h3TerminalVelocitySpectralStateAt hH3 t htAbs)
        ξ
  calc
    (∫⁻ ξ : H3FourierPoint3,
      ENNReal.ofReal
        (h3TerminalSpectralDissipationSingleDensity
          (h3TerminalVelocitySpectralStateAt hH3 t htAbs) ξ)
      ∂volume)
        =
      ENNReal.ofReal
        (∫ ξ : H3FourierPoint3,
          h3TerminalSpectralDissipationSingleDensity
            (h3TerminalVelocitySpectralStateAt hH3 t htAbs) ξ
          ∂volume) := by
      symm
      exact
        ofReal_integral_eq_lintegral_ofReal
          hInt
          hNonneg
    _ = ENNReal.ofReal (velocityH3DissipationAt u t) := by
      rw [
        integral_h3TerminalSpectralDissipationSingleDensity_eq_dissipation
          hH3 hClass ht
      ]

/-! ## Two-time defect dominated by two physical snapshots -/

private theorem norm_sub_sq_le_two_mul_sum_sq_physicalDissipation
    (a b : ℂ) :
    ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hTri : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have hSq :
      ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    (sq_le_sq₀
      (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hTri
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- The pair-difference dissipation density is bounded by twice the sum of the
two single-time dissipation densities. -/
theorem h3TerminalSpectralDissipationDifferenceDensity_le_two_mul_singleDensity_add
    (G H : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) :
    h3TerminalSpectralDissipationDifferenceDensity G H ξ
      ≤
    2 *
      (h3TerminalSpectralDissipationSingleDensity G ξ
        + h3TerminalSpectralDissipationSingleDensity H ξ) := by
  have h0 :=
    norm_sub_sq_le_two_mul_sum_sq_physicalDissipation
      (G 0 ξ) (H 0 ξ)
  have h1 :=
    norm_sub_sq_le_two_mul_sum_sq_physicalDissipation
      (G 1 ξ) (H 1 ξ)
  have h2 :=
    norm_sub_sq_le_two_mul_sum_sq_physicalDissipation
      (G 2 ξ) (H 2 ξ)
  have hSum :
      norm (G 0 ξ - H 0 ξ) ^ 2
          + norm (G 1 ξ - H 1 ξ) ^ 2
          + norm (G 2 ξ - H 2 ξ) ^ 2
        ≤
      2 *
        ((norm (G 0 ξ) ^ 2 + norm (G 1 ξ) ^ 2 + norm (G 2 ξ) ^ 2)
          +
         (norm (H 0 ξ) ^ 2 + norm (H 1 ξ) ^ 2 + norm (H 2 ξ) ^ 2)) := by
    nlinarith

  have hMul :=
    mul_le_mul_of_nonneg_left
      hSum
      (h3FourierGradientSquare_nonneg ξ)

  unfold
    h3TerminalSpectralDissipationDifferenceDensity
    h3TerminalSpectralDifferenceAt
    h3TerminalSpectralDissipationSingleDensity

  nlinarith

/-- After the factor four built into the pair control mass, the pointwise
majorant is eight times the sum of the two one-state physical densities. -/
theorem four_mul_dissipationDifferenceDensity_le_eight_mul_singleDensity_add
    (G H : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) :
    4 * h3TerminalSpectralDissipationDifferenceDensity G H ξ
      ≤
    8 *
      (h3TerminalSpectralDissipationSingleDensity G ξ
        + h3TerminalSpectralDissipationSingleDensity H ξ) := by
  have h :=
    h3TerminalSpectralDissipationDifferenceDensity_le_two_mul_singleDensity_add
      G H ξ
  nlinarith

/-- Eightfold localized physical two-snapshot majorant on the same bad-cone
high-radial region as the terminal obstruction. -/
noncomputable def h3TerminalPhysicalDissipationPairBadConeHighRadialMajorantMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (i : Fin 3)
    (κ ρ s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) : ℝ≥0∞ :=
  ∫⁻ ξ in
      h3TerminalLongitudinalAngularBadCone i κ
        \
      h3TerminalRadialFrequencyBelow ρ,
    ENNReal.ofReal
      (8 *
        (h3TerminalSpectralDissipationSingleDensity
            (h3TerminalVelocitySpectralStateAt hH3 s hs) ξ
          +
         h3TerminalSpectralDissipationSingleDensity
            (h3TerminalVelocitySpectralStateAt hH3 t ht) ξ))

/-- The abstract pair-difference control mass is bounded by the localized
physical two-snapshot dissipation majorant. -/
theorem spectralDissipationDifferenceControlMass_le_physicalDissipationPairMajorantMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (i : Fin 3)
    (κ ρ s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
        i κ ρ
        (h3TerminalVelocitySpectralStateAt hH3 s hs)
        (h3TerminalVelocitySpectralStateAt hH3 t ht)
      ≤
    h3TerminalPhysicalDissipationPairBadConeHighRadialMajorantMass
      hH3 i κ ρ s t hs ht := by
  let S : Set H3FourierPoint3 :=
    h3TerminalLongitudinalAngularBadCone i κ
      \
    h3TerminalRadialFrequencyBelow ρ

  have hSMeas : MeasurableSet S :=
    (measurableSet_h3TerminalLongitudinalAngularBadCone i κ).diff
      (measurableSet_h3TerminalRadialFrequencyBelow ρ)

  unfold
    h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
    h3TerminalPhysicalDissipationPairBadConeHighRadialMajorantMass

  change
    (∫⁻ ξ in S,
      ENNReal.ofReal
        (4 *
          h3TerminalSpectralDissipationDifferenceDensity
            (h3TerminalVelocitySpectralStateAt hH3 s hs)
            (h3TerminalVelocitySpectralStateAt hH3 t ht)
            ξ)
      ∂volume)
      ≤
    ∫⁻ ξ in S,
      ENNReal.ofReal
        (8 *
          (h3TerminalSpectralDissipationSingleDensity
              (h3TerminalVelocitySpectralStateAt hH3 s hs) ξ
            +
           h3TerminalSpectralDissipationSingleDensity
              (h3TerminalVelocitySpectralStateAt hH3 t ht) ξ))
      ∂volume

  apply setLIntegral_mono' hSMeas
  intro ξ hξ

  exact
    ENNReal.ofReal_le_ofReal
      (four_mul_dissipationDifferenceDensity_le_eight_mul_singleDensity_add
        (h3TerminalVelocitySpectralStateAt hH3 s hs)
        (h3TerminalVelocitySpectralStateAt hH3 t ht)
        ξ)

/-! ## Physical dissipation concentration branch -/

/-- A fixed positive radial cutoff carries physical H³ dissipation mass in
shrinking equatorial cones along one terminal two-time sequence. -/
def H3TerminalPhysicalDissipationAngularConcentrationBranchAtCutoff
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (i : Fin 3)
    (ε ρ : ℝ) : Prop :=
  ∃ s t : ℕ → ℝ,
    ∃ hs : ∀ n, s n ∈ Ioo (0 : ℝ) T,
      ∃ ht : ∀ n, t n ∈ Ioo (0 : ℝ) T,
        ∃ p : ℕ → ℕ,
          StrictMono p ∧
          Tendsto (fun n => s (p n)) atTop (𝓝 T) ∧
          Tendsto (fun n => t (p n)) atTop (𝓝 T) ∧
          Tendsto
            (fun n => (1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
            atTop (𝓝 0) ∧
          ∀ n,
            ENNReal.ofReal (ρ ^ 2 * (ε ^ 2 / 64))
              <
            h3TerminalPhysicalDissipationPairBadConeHighRadialMajorantMass
              hH3 i
              ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
              ρ
              (s (p n))
              (t (p n))
              (hs (p n))
              (ht (p n))

/-- Every high-radial raw-vorticity branch forces a physical H³ dissipation
angular concentration branch at the same radial cutoff. -/
theorem physicalDissipationAngularConcentrationBranchAtCutoff_of_highRadialRawVorticityBranchAtCutoff
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (i q : Fin 3)
    {ε ρ : ℝ}
    (hBranch :
      H3TerminalHighRadialRawVorticityBranchAtCutoff
        hH3 i q ε ρ) :
    H3TerminalPhysicalDissipationAngularConcentrationBranchAtCutoff
      hH3 i ε ρ := by
  unfold H3TerminalHighRadialRawVorticityBranchAtCutoff at hBranch
  obtain
    ⟨s, t, hs, ht, p, hPMono, hSTendsto, hTTendsto, hKappaTendsto, hMass⟩ :=
    hBranch

  refine
    ⟨s, t, hs, ht, p,
      hPMono,
      hSTendsto,
      hTTendsto,
      hKappaTendsto,
      ?_⟩

  intro n

  have hRawLe :
      h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
          i q
          ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
          ρ
          (h3TerminalVelocitySpectralStateAt hH3 (s (p n)) (hs (p n)))
          (h3TerminalVelocitySpectralStateAt hH3 (t (p n)) (ht (p n)))
        ≤
      h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
          i
          ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
          ρ
          (h3TerminalVelocitySpectralStateAt hH3 (s (p n)) (hs (p n)))
          (h3TerminalVelocitySpectralStateAt hH3 (t (p n)) (ht (p n))) :=
    rawVorticityComponentBadConeHighRadialSquareMass_le_spectralDissipationDifferenceControlMass
      i q
      ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
      ρ
      (h3TerminalVelocitySpectralStateAt hH3 (s (p n)) (hs (p n)))
      (h3TerminalVelocitySpectralStateAt hH3 (t (p n)) (ht (p n)))

  have hPairLe :
      h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
          i
          ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
          ρ
          (h3TerminalVelocitySpectralStateAt hH3 (s (p n)) (hs (p n)))
          (h3TerminalVelocitySpectralStateAt hH3 (t (p n)) (ht (p n)))
        ≤
      h3TerminalPhysicalDissipationPairBadConeHighRadialMajorantMass
        hH3 i
        ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
        ρ
        (s (p n))
        (t (p n))
        (hs (p n))
        (ht (p n)) :=
    spectralDissipationDifferenceControlMass_le_physicalDissipationPairMajorantMass
      hH3 i
      ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
      ρ
      (s (p n))
      (t (p n))
      (hs (p n))
      (ht (p n))

  exact
    (hMass n).trans_le
      (hRawLe.trans hPairLe)

/-- Under the retained raw-Fourier L² Cauchy hypothesis, hypothetical
nonextension and one surviving physical-vorticity endpoint force a localized
physical H³ dissipation concentration branch for a complementary component. -/
theorem exists_failing_complementary_vorticityComponent_physicalDissipationAngularConcentration_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ : ℝ,
      0 < ρ ∧
      ∃ q : Fin 3,
        q ≠ i ∧
        ¬ H3TerminalActualVorticityStrongH3EndpointPath hH3 q ∧
        H3TerminalHighRadialRawVorticityBranchAtCutoff hH3 i q ε ρ ∧
        H3TerminalPhysicalDissipationAngularConcentrationBranchAtCutoff
          hH3 i ε ρ := by
  obtain
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch⟩ :=
    exists_failing_complementary_vorticityComponent_highRadialRaw_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3 hNoExtension hClass hPhysical hCauchy hε

  refine
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, ?_⟩

  exact
    physicalDissipationAngularConcentrationBranchAtCutoff_of_highRadialRawVorticityBranchAtCutoff
      hH3 i q hRawBranch

end

end Euclidean
end Bridge
end PrimeTensor
