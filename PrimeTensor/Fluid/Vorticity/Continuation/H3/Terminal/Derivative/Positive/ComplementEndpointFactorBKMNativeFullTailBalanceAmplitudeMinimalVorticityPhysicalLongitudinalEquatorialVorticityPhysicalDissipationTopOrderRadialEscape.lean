import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationRadialTailCriterion
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationFourierIdentification

/-!
# Full dissipation radial escape forces top-order radial escape

The previous compactness reduction shows that, under the retained endpoint
hypotheses, hypothetical nonextension forces a fixed positive amount of the
full physical H³ dissipation mass to escape beyond arbitrarily large radial
Fourier cutoffs.

The full physical radial density is

    (q + q² + q³ + q⁴) |û|²,

where

    q = |D(ξ)|².

The top-order H³ viscous block is exactly

    q⁴ |û|².

On the region `1 ≤ |D(ξ)|`, hence `1 ≤ q`, each of `q`, `q²`, and `q³` is
bounded by `q⁴`. Therefore

    (q + q² + q³ + q⁴) |û|² ≤ 4 q⁴ |û|².

Consequently every full-dissipation radial escape sequence contains, on the
same times and measurable sets, a top-order dissipation radial escape sequence
with one quarter of the fixed mass.

This is a spectral concentration statement for the already-existing physical
top-order dissipation `velocityH3Dissipation3At`; it introduces no higher
regularity hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationTopOrderRadialEscape
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationTopOrderRadialEscape :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Localized physical top-order dissipation mass -/

/--
Localized fourth-radial-moment mass, i.e. the spectral density whose whole
integral is the physical top-order H³ dissipation block
`velocityH3Dissipation3At`.
-/
noncomputable def h3TerminalPhysicalTopDissipationSetMassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T)
    (S : Set H3FourierPoint3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs
  ∫ ξ in S,
    h3FourierGradientSquare ξ ^ 4
      *
    velocityH3FourierMassDensityAt
      u t hInt hMeas ξ
    ∂volume

/--
The fourth-radial-moment density is integrable at every strict energy-class
time.
-/
theorem h3TerminalPhysicalTopDissipationDensity_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let hInt : VelocityH3IntegrableAt u t :=
      hH3.velocity_h3_integrable t htAbs
    let hMeas : VelocityH3MeasurableAt u t :=
      velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes htAbs
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 4
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ)
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

  exact
    h3Path_velocityH3FourierFourthAggregateDensity_integrable
      hH3 hClass ht hInt hMeas hFourier

/-! ## Pointwise high-frequency dominance by the top block -/

/--
Once the radial gradient magnitude is at least one, the full physical H³
dissipation density is bounded by four times its top-order fourth-radial block.
-/
theorem velocityH3FourierFullDissipationDensityAt_le_four_mul_topDensity_of_one_le_gradientMagnitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    {ξ : H3FourierPoint3}
    (hGrad :
      1 ≤ h3FourierGradientMagnitude ξ) :
    velocityH3FourierFullDissipationDensityAt
        u t hInt hMeas ξ
      ≤
    4
      *
    (
      h3FourierGradientSquare ξ ^ 4
        *
      velocityH3FourierMassDensityAt
        u t hInt hMeas ξ
    ) := by

  let q : ℝ :=
    h3FourierGradientSquare ξ

  let m : ℝ :=
    velocityH3FourierMassDensityAt
      u t hInt hMeas ξ

  have hMagnitudeNonneg :
      0 ≤ h3FourierGradientMagnitude ξ :=
    h3FourierGradientMagnitude_nonneg ξ

  have hq :
      q
        =
      h3FourierGradientMagnitude ξ ^ 2 := by
    dsimp only [q]
    exact
      (h3FourierGradientMagnitude_sq ξ).symm

  have hqOne :
      1 ≤ q := by
    rw [hq]
    nlinarith

  have hm :
      0 ≤ m := by
    dsimp only [m]
    exact
      velocityH3FourierMassDensityAt_nonneg
        u t hInt hMeas ξ

  have hq1 :
      q ≤ q ^ 4 := by
    simpa only [pow_one] using
      (pow_le_pow_right₀
        hqOne
        (by norm_num : (1 : ℕ) ≤ 4))

  have hq2 :
      q ^ 2 ≤ q ^ 4 :=
    pow_le_pow_right₀
      hqOne
      (by norm_num : (2 : ℕ) ≤ 4)

  have hq3 :
      q ^ 3 ≤ q ^ 4 :=
    pow_le_pow_right₀
      hqOne
      (by norm_num : (3 : ℕ) ≤ 4)

  have h1 :
      q * m ≤ q ^ 4 * m :=
    mul_le_mul_of_nonneg_right
      hq1
      hm

  have h2 :
      q ^ 2 * m ≤ q ^ 4 * m :=
    mul_le_mul_of_nonneg_right
      hq2
      hm

  have h3 :
      q ^ 3 * m ≤ q ^ 4 * m :=
    mul_le_mul_of_nonneg_right
      hq3
      hm

  unfold
    velocityH3FourierFullDissipationDensityAt

  change
    q * m
        +
      q ^ 2 * m
        +
      q ^ 3 * m
        +
      q ^ 4 * m
      ≤
    4 * (q ^ 4 * m)

  linarith

/-! ## Localized comparison -/

/--
On any measurable set contained in `1 ≤ |D|`, full physical H³ dissipation
mass is bounded by four times the localized top-order dissipation mass.
-/
theorem physicalDissipationSetMass_le_four_mul_topDissipationSetMass_of_one_le_gradientMagnitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hOne :
      ∀ ξ ∈ S,
        1 ≤ h3FourierGradientMagnitude ξ) :
    h3TerminalPhysicalDissipationSetMassAt
        hH3 hClass t ht S
      ≤
    4
      *
    h3TerminalPhysicalTopDissipationSetMassAt
      hH3 hClass t ht S := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let fullSpectral : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3TerminalSpectralDissipationSingleDensity
        (h3TerminalVelocitySpectralStateAt
          hH3 t htAbs)
        ξ

  let topPhysical : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 4
        *
      velocityH3FourierMassDensityAt
        u t hInt hMeas ξ

  have hFullInt :
      Integrable fullSpectral volume := by
    dsimp only [fullSpectral, htAbs]
    simpa only using
      (h3TerminalSpectralDissipationSingleDensity_integrable
        hH3 hClass ht)

  have hTopInt :
      Integrable topPhysical volume := by
    dsimp only [topPhysical, hInt, hMeas, htAbs]
    simpa only using
      (h3TerminalPhysicalTopDissipationDensity_integrable
        hH3 hClass ht)

  have hPhysicalAE :
      fullSpectral
        =ᵐ[volume]
      velocityH3FourierFullDissipationDensityAt
        u t hInt hMeas := by
    dsimp only [fullSpectral, hInt, hMeas, htAbs]
    exact
      h3TerminalSpectralDissipationSingleDensity_ae_eq_physicalFullDensity
        hH3
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  have hPoint :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume.restrict S),
        fullSpectral ξ
          ≤
        4 * topPhysical ξ := by

    rw [ae_restrict_iff' hS]

    filter_upwards [hPhysicalAE] with ξ hEq

    intro hξ

    rw [hEq]

    dsimp only [topPhysical, hInt, hMeas]

    exact
      velocityH3FourierFullDissipationDensityAt_le_four_mul_topDensity_of_one_le_gradientMagnitude
        (hInt :=
          hH3.velocity_h3_integrable
            t
            ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
        (hMeas :=
          velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
            hH3.navier_stokes
            ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
        (hOne ξ hξ)

  have hIntegralLe :
      (∫ ξ : H3FourierPoint3,
          fullSpectral ξ
          ∂(volume.restrict S))
        ≤
      ∫ ξ : H3FourierPoint3,
        4 * topPhysical ξ
        ∂(volume.restrict S) := by

    exact
      integral_mono_ae
        (hFullInt.mono_measure Measure.restrict_le_self)
        ((hTopInt.const_mul 4).mono_measure Measure.restrict_le_self)
        hPoint

  unfold
    h3TerminalPhysicalDissipationSetMassAt
    h3TerminalPhysicalTopDissipationSetMassAt

  change
    (∫ ξ : H3FourierPoint3,
        fullSpectral ξ
        ∂(volume.restrict S))
      ≤
    4
      *
    ∫ ξ : H3FourierPoint3,
      topPhysical ξ
      ∂(volume.restrict S)

  calc
    (∫ ξ : H3FourierPoint3,
        fullSpectral ξ
        ∂(volume.restrict S))
        ≤
      ∫ ξ : H3FourierPoint3,
        4 * topPhysical ξ
        ∂(volume.restrict S) :=
          hIntegralLe

    _ =
      4
        *
      ∫ ξ : H3FourierPoint3,
        topPhysical ξ
        ∂(volume.restrict S) := by
          rw [integral_const_mul]

/-! ## Explicit top-order radial escape package -/

/--
A fixed positive amount of the physical top-order H³ dissipation mass survives
on measurable sets outside radial cutoff `n+1`, at terminal times converging
to `T`.
-/
def H3TerminalPhysicalTopDissipationRadialEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ τ : ℕ → ℝ,
      ∃ S : ℕ → Set H3FourierPoint3,
        (
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
                  hH3 hClass (τ n) ht (S n)
        )
          ∧
        Tendsto τ atTop (𝓝 T)

/--
Every full physical dissipation radial-escape sequence yields a top-order
radial-escape sequence on the same terminal times and sets.  The retained mass
is reduced only by the universal factor four.
-/
theorem physicalTopDissipationRadialEscapeSequence_of_physicalDissipationRadialEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape :
      H3TerminalPhysicalDissipationRadialEscapeSequence
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationRadialEscapeSequence
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

  refine
    ⟨
      δ / 4,
      by positivity,
      τ,
      S,
      ?_,
      hτTendsto
    ⟩

  intro n

  obtain
    ⟨
      ht,
      hNear,
      hSMeas,
      hSSubset,
      hMass
    ⟩ :=
    hData n

  have hOne :
      ∀ ξ ∈ S n,
        1 ≤ h3FourierGradientMagnitude ξ := by

    intro ξ hξ

    have hOutside :=
      hSSubset hξ

    have hRadial :
        (n : ℝ) + 1
          ≤
        h3FourierGradientMagnitude ξ := by

      change
        ¬
          h3FourierGradientMagnitude ξ
            <
          (n : ℝ) + 1
        at hOutside

      exact
        le_of_not_gt
          hOutside

    have hOneLe :
        1 ≤ (n : ℝ) + 1 := by
      have hn0 :
          0 ≤ (n : ℝ) := by
        exact_mod_cast Nat.zero_le n
      linarith

    exact
      hOneLe.trans
        hRadial

  have hCompare :
      h3TerminalPhysicalDissipationSetMassAt
          hH3 hClass (τ n) ht (S n)
        ≤
      4
        *
      h3TerminalPhysicalTopDissipationSetMassAt
        hH3 hClass (τ n) ht (S n) :=
    physicalDissipationSetMass_le_four_mul_topDissipationSetMass_of_one_le_gradientMagnitude
      hH3
      hClass
      ht
      (S n)
      hSMeas
      hOne

  have hTopMass :
      δ / 4
        ≤
      h3TerminalPhysicalTopDissipationSetMassAt
        hH3 hClass (τ n) ht (S n) := by
    linarith

  exact
    ⟨
      ht,
      hNear,
      hSMeas,
      hSSubset,
      hTopMass
    ⟩

/-! ## Endpoint consequence -/

/--
Under the retained raw-Fourier `L²` Cauchy and surviving physical-vorticity
endpoint hypotheses, hypothetical nonextension forces top-order physical H³
dissipation mass to escape to arbitrarily large radial frequencies.
-/
theorem physicalTopDissipationRadialEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalPhysicalTopDissipationRadialEscapeSequence
      hH3 hClass := by

  exact
    physicalTopDissipationRadialEscapeSequence_of_physicalDissipationRadialEscapeSequence
      hH3
      hClass
      (physicalDissipationRadialEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hCauchy)

/-!
## Neutral formulation
-/

/--
Neutral endpoint alternative: either there is a smooth continuation through
`T`, or a fixed positive amount of the physical top-order H³ dissipation
escapes beyond arbitrarily large radial Fourier cutoffs along terminal times.
-/
theorem smoothContinuationExtension_or_physicalTopDissipationRadialEscapeSequence
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
    H3TerminalPhysicalTopDissipationRadialEscapeSequence
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
        (physicalTopDissipationRadialEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
