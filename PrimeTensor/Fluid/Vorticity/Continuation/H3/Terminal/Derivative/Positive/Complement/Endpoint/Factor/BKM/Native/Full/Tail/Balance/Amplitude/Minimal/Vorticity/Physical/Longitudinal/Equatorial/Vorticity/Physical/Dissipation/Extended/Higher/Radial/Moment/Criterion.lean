import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Extended.Higher.Radial.Moment.Cascade
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Arbitrary.Coercive.Radial.Weight

/-!
# Higher radial moment continuation criterion

For every nonzero natural shift `m`, the extended higher-radial moment

    ∫ q(ξ)^(4+m) |û(t,ξ)|² dξ

is exactly the top-order physical H³ dissipation moment weighted by the real
radial polynomial

    r ↦ r^(2m),

because `r = |D(ξ)|` and `r² = q(ξ)`.

That polynomial tends to `+∞` whenever `m ≠ 0`.  Therefore the arbitrary
coercive radial-weight criterion applies directly: a finite uniform terminal
ceiling for any one nonzero extended higher-radial moment implies smooth
continuation under the retained endpoint hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

set_option maxHeartbeats 1800000

/--
The radial polynomial whose weighted top-order density is the `m`-shifted
higher-radial density.
-/
noncomputable def h3TerminalHigherRadialPolynomialWeight
    (m : ℕ)
    (r : ℝ) : ℝ :=
  r ^ (2 * m)

/--
For every nonzero shift, the corresponding radial polynomial is coercive in
the minimal arbitrary-weight sense.
-/
theorem h3TerminalHigherRadialPolynomialWeight_coercive
    (m : ℕ)
    (hm : m ≠ 0) :
    H3TerminalArbitraryCoerciveRadialWeight
      (h3TerminalHigherRadialPolynomialWeight m) := by

  unfold
    H3TerminalArbitraryCoerciveRadialWeight
    h3TerminalHigherRadialPolynomialWeight

  have hExp :
      2 * m ≠ 0 :=
    Nat.mul_ne_zero
      (by norm_num)
      hm

  exact
    tendsto_pow_atTop hExp

/--
At every strict terminal time, the polynomial-weighted top-order density is
exactly the existing `m`-shifted higher-radial density.
-/
theorem h3TerminalPhysicalRadialWeightedTopDissipationDensityAt_polynomial_eq_higherRadialDensity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (m : ℕ)
    (ht : t ∈ Set.Ioo a T)
    (ξ : H3FourierPoint3) :
    h3TerminalPhysicalRadialWeightedTopDissipationDensityAt
        hH3 hClass
        (h3TerminalHigherRadialPolynomialWeight m)
        t ht ξ
      =
    h3TerminalPhysicalHigherRadialDensityAt
      hH3 hClass m t ht ξ := by

  unfold
    h3TerminalPhysicalRadialWeightedTopDissipationDensityAt
    h3TerminalHigherRadialPolynomialWeight
    h3TerminalPhysicalHigherRadialDensityAt

  rw [pow_mul]
  rw [h3FourierGradientMagnitude_sq]
  rw [pow_add]

  ring

/--
The extended polynomial-weighted top-order moment is exactly the existing
extended `m`-shifted higher-radial moment.
-/
theorem h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt_polynomial_eq_extendedHigherRadialMoment
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (m : ℕ)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
        hH3 hClass
        (h3TerminalHigherRadialPolynomialWeight m)
        t ht
      =
    h3TerminalPhysicalExtendedHigherRadialMomentAt
      hH3 hClass m t ht := by

  unfold
    h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
    h3TerminalPhysicalExtendedHigherRadialMomentAt

  apply lintegral_congr

  intro ξ

  rw [
    h3TerminalPhysicalRadialWeightedTopDissipationDensityAt_polynomial_eq_higherRadialDensity
      hH3 hClass m ht ξ
  ]

/--
A finite uniform terminal ceiling for one fixed `m`-shifted higher-radial
moment.
-/
def H3TerminalPhysicalExtendedHigherRadialMomentUniformBoundAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (m : ℕ) : Prop :=
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
          h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass m t ht
            ≤
          ENNReal.ofReal C

/--
A uniform ceiling for the `m`-shifted higher-radial moment is exactly a
uniform ceiling for its polynomial-weighted top-order realization.
-/
theorem radialWeightedTopDissipationUniformBoundAtEndpoint_of_extendedHigherRadialMomentUniformBoundAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (m : ℕ)
    (hBound :
      H3TerminalPhysicalExtendedHigherRadialMomentUniformBoundAtEndpoint
        hH3 hClass m) :
    H3TerminalPhysicalRadialWeightedTopDissipationUniformBoundAtEndpoint
      hH3 hClass
      (h3TerminalHigherRadialPolynomialWeight m) := by

  obtain
    ⟨
      C,
      hC,
      η,
      hη,
      hMoment
    ⟩ :=
    hBound

  refine
    ⟨
      C,
      hC,
      η,
      hη,
      ?_
    ⟩

  intro t ht htNear

  rw [
    h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt_polynomial_eq_extendedHigherRadialMoment
      hH3 hClass m ht
  ]

  exact
    hMoment
      t
      ht
      htNear

/--
Under the retained raw-Fourier `L²` Cauchy and physical-vorticity endpoint
hypotheses, a finite uniform ceiling for any one nonzero extended
higher-radial moment is sufficient for smooth continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_extendedHigherRadialMomentUniformBound_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (m : ℕ)
    (hm : m ≠ 0)
    (hBound :
      H3TerminalPhysicalExtendedHigherRadialMomentUniformBoundAtEndpoint
        hH3 hClass m) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hw :
      H3TerminalArbitraryCoerciveRadialWeight
        (h3TerminalHigherRadialPolynomialWeight m) :=
    h3TerminalHigherRadialPolynomialWeight_coercive
      m
      hm

  have hWeighted :
      H3TerminalPhysicalRadialWeightedTopDissipationUniformBoundAtEndpoint
        hH3 hClass
        (h3TerminalHigherRadialPolynomialWeight m) :=
    radialWeightedTopDissipationUniformBoundAtEndpoint_of_extendedHigherRadialMomentUniformBoundAtEndpoint
      hH3
      hClass
      m
      hBound

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_arbitraryCoerciveRadialWeightedTopDissipationUniformBound_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      hw
      hWeighted

/--
Consequently, hypothetical nonextension excludes a finite uniform terminal
ceiling for every fixed nonzero higher-radial shift.
-/
theorem not_extendedHigherRadialMomentUniformBoundAtEndpoint_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    (m : ℕ)
    (hm : m ≠ 0) :
    ¬ H3TerminalPhysicalExtendedHigherRadialMomentUniformBoundAtEndpoint
        hH3 hClass m := by

  intro hBound

  exact
    hNoExtension
      (
        smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_extendedHigherRadialMomentUniformBound_of_actualVorticityStrongH3EndpointPath
          hH3
          hClass
          hPhysical
          hCauchy
          m
          hm
          hBound
      )

end

end Euclidean
end Bridge
end PrimeTensor
