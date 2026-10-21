import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientCanonicalClosure244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedTopTransport
import Mathlib.Tactic

/-!
# Exact physical-to-spectral H³ signed energy rate

The old physical top-order H³ transport has now been proved to equal the
choice-independent weighted H³ 972-gradient + 3×243-interpolation
Schwartz completion.  Apply this equality to the actual H³ energy balance,
without taking an absolute value of the signed cubic.

The spectral state below is obtained from the original H³-path integrability,
measurability, and Fourier compatibility at EVERY strict preterminal time.
The state is assigned zero outside the physical interval only so that we may
write globally defined scalar functions and an actual time-integrability
criterion. No measurable spectral-path claim is made or required.

The scalar rate is exactly the pre-existing signed physical rate. Its positive
excess above the existing 4422 continuation baseline is therefore integrable
if and only if the old signed physical remainder is integrable on a tail.
Consequently a bound on the *canonical signed cubic*, including both the
972-gradient and all 243 interpolation slots, yields continuation. Under
hypothetical nonextension the canonical adverse cubic corridor is visited
arbitrarily late. Neither alternative asserts an unconditional cubic bound.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

/-- The genuine spectral H³ state of an admissible physical path, not an
independently chosen spectral family. Off the strict physical interval it is
zero; all analytic claims are made only inside the interval. -/
noncomputable def h3PathWeightedSpectralState244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : H3SpectralVelocityState :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    let hInt : VelocityH3IntegrableAt u t :=
      hH3.velocity_h3_integrable t ht
    let hMeas : VelocityH3MeasurableAt u t :=
      velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes ht
    let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
      velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes ht hInt
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  else 0

/-- The H³-path encoder is precisely the original physical Fourier encoder
at every admissible slice. Proof irrelevance removes choices of evidence
for integrability, measurability, and Fourier compatibility. -/
theorem h3PathWeightedSpectralState_eq_actual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    h3PathWeightedSpectralState244 u T hH3 t =
      velocityH3SpectralStateAt u t hInt hMeas hFourier := by
  simp only [h3PathWeightedSpectralState244, dif_pos ht]

/-- At every strict H³ energy-class time the canonical full-third scalar
IS the original signed physical third-order transport. No new snapshot
Fourier hypothesis is added: it is derived from the genuine NS path. -/
theorem h3Path_weightedFullThird_eq_physical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3TransportDerivative3At u t =
      weightedH3CanonicalFullThirdCommutator244
        (h3PathWeightedSpectralState244 u T hH3 t) := by
  have htNS : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htNS
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS hInt
  have hOld := h3PhysicalFullThird_eq_weightedCanonical244
    hH3.navier_stokes htNS hH3 hClass ht hFourier
  change velocityH3TransportDerivative3At u t =
    weightedH3CanonicalFullThirdCommutator244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier) at hOld
  rw [h3PathWeightedSpectralState_eq_actual244 hH3 htNS hFourier]
  exact hOld

/-- The dissipative physical H³ balance with its FULL canonical signed
third-order spectral cubic substituted exactly. The sign is not discarded. -/
theorem h3Path_deriv_add_dissipation_le_weightedFullThird244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t +
        2 * velocityH3DissipationAt u t ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t -
      weightedH3CanonicalFullThirdCommutator244
        (h3PathWeightedSpectralState244 u T hH3 t) := by
  have hBound := h3PathCanonical_deriv_add_dissipation_le_signedTopTransport
    hH3 hClass ht
  rw [h3Path_weightedFullThird_eq_physical244 hH3 hClass ht] at hBound
  exact hBound

/-- The exact signed top-order rate built from the WEIGHTED spectral cubic.
This is the old physical rate rewritten, not a separately estimated rate. -/
noncomputable def h3PathWeightedSignedTopRate244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : ℝ :=
  24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) -
    (weightedH3CanonicalFullThirdCommutator244
      (h3PathWeightedSpectralState244 u T hH3 t) +
      2 * velocityH3DissipationAt u t) / velocityH3EnergyAt u t

/-- Canonical and old physical signed transport rates are identical at
every strict H³ energy-class time. -/
theorem h3Path_weightedSignedTopRate_eq_physical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathWeightedSignedTopRate244 u T hH3 t =
      h3PathCanonicalSignedTopTransportRate u t := by
  unfold h3PathWeightedSignedTopRate244 h3PathCanonicalSignedTopTransportRate
  rw [h3Path_weightedFullThird_eq_physical244 hH3 hClass ht]

/-- The canonical rate bounds actual normalized H³ energy growth with
its physical dissipation coefficient still exactly two. -/
theorem h3Path_normalizedSlope_le_weightedSignedTopRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t ≤
      h3PathWeightedSignedTopRate244 u T hH3 t := by
  have h := h3PathCanonical_normalizedSlope_le_signedTopTransportRate
    hH3 hClass ht
  rwa [h3Path_weightedSignedTopRate_eq_physical244 hH3 hClass ht]

/-- The canonical signed excess above the existing continuation threshold. -/
noncomputable def h3PathWeightedSignedTopRemainder244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T) : ℝ → ℝ :=
  fun t => max 0 (h3PathWeightedSignedTopRate244 u T hH3 t - 4422)

/-- The canonical and old physical positive remainders agree POINTWISE on
the original energy-class tail, not just at almost every time. -/
theorem h3Path_weightedSignedTopRemainder_eq_physical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathWeightedSignedTopRemainder244 u T hH3 t =
      h3PathCanonicalSignedTopTransportRemainder u t := by
  unfold h3PathWeightedSignedTopRemainder244
    h3PathCanonicalSignedTopTransportRemainder
  rw [h3Path_weightedSignedTopRate_eq_physical244 hH3 hClass ht]

/-- The old physical continuation criterion and the NEW canonical weighted
spectral criterion have exactly the same temporal integrability content. -/
theorem h3Path_weightedSignedTopRemainder_integrable_iff244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    IntegrableOn (h3PathWeightedSignedTopRemainder244 u T hH3)
        (Set.Ioo a T) ↔
      IntegrableOn (h3PathCanonicalSignedTopTransportRemainder u)
        (Set.Ioo a T) := by
  exact integrableOn_congr_fun
    (fun t ht => h3Path_weightedSignedTopRemainder_eq_physical244
      hH3 hClass ht) measurableSet_Ioo

/-- Time integrability of the actual canonical spectral signed cubic excess
suffices for continuation. This does not assert that the excess is integrable. -/
theorem h3Path_extension_of_integrable_weightedSignedTopRemainder244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hInt : IntegrableOn (h3PathWeightedSignedTopRemainder244 u T hH3)
      (Set.Ioo a T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  apply h3PathCanonical_extension_of_integrable_signedTopTransportRemainder
    hH3 hClass
  exact (h3Path_weightedSignedTopRemainder_integrable_iff244 hH3 hClass).1 hInt

/-- Conversely, hypothetical nonextension makes the canonical signed
spectral remainder nonintegrable on EVERY strict terminal subtail. -/
theorem h3Path_weightedSignedTopRemainder_nonintegrable_on_subtail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T) :
    ¬ IntegrableOn (h3PathWeightedSignedTopRemainder244 u T hH3)
      (Set.Ioo d T) := by
  intro hInt
  have hOld : IntegrableOn (h3PathCanonicalSignedTopTransportRemainder u)
      (Set.Ioo d T) := by
    exact (integrableOn_congr_fun
      (fun t ht => h3Path_weightedSignedTopRemainder_eq_physical244
        hH3 hClass ⟨lt_trans hd.1 ht.1, ht.2⟩)
      measurableSet_Ioo).1 hInt
  exact (h3PathCanonical_signedTopRemainder_nonintegrable_on_subtail
    hH3 hNoExtension hClass hd) hOld

/-- On every terminal subtail, hypothetical nonextension produces a genuine
adverse weighted-Schwartz top-order cubic event beyond ANY prescribed
nonnegative normalized threshold. This is a necessary condition only. -/
theorem h3Path_weightedFullThird_adverse_witness_of_noExtension244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hM : 0 ≤ M) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      (4422 + M) * velocityH3EnergyAt u t +
          2 * velocityH3DissipationAt u t <
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t -
          weightedH3CanonicalFullThirdCommutator244
            (h3PathWeightedSpectralState244 u T hH3 t) := by
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_signedTopAdversity_witness_of_noExtension
      hH3 hNoExtension hClass hd hM
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  rw [h3Path_weightedFullThird_eq_physical244 hH3 hClass htClass] at hAdverse
  exact ⟨t, ht, hAdverse⟩


/-- A direct spectral sufficiency criterion: if the complete signed 972+243
weighted third-order cubic and physical dissipation together offset the
24 h E lower-order allowance beyond the existing 4422 baseline throughout
one preterminal tail, then the original H³ path extends smoothly.

This does NOT prove the spectral inequality itself; it makes that precise
quantitative inequality the remaining task. -/
theorem h3Path_extension_of_weightedFullThird_dominance244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDom : ∀ t : ℝ, t ∈ Set.Ioo a T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t ≤
        4422 * velocityH3EnergyAt u t +
          (weightedH3CanonicalFullThirdCommutator244
            (h3PathWeightedSpectralState244 u T hH3 t) +
            2 * velocityH3DissipationAt u t)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hZero : ∀ t : ℝ, t ∈ Set.Ioo a T →
      h3PathWeightedSignedTopRemainder244 u T hH3 t = 0 := by
    intro t ht
    have hEPos : 0 < velocityH3EnergyAt u t :=
      lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
    have hMul :
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t)) - 4422) *
            velocityH3EnergyAt u t ≤
          weightedH3CanonicalFullThirdCommutator244
            (h3PathWeightedSpectralState244 u T hH3 t) +
            2 * velocityH3DissipationAt u t := by
      calc
        _ = 24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
              Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t -
            4422 * velocityH3EnergyAt u t := by ring
        _ ≤ _ := by linarith only [hDom t ht]
    have hDiv := (le_div_iff₀ hEPos).2 hMul
    have hRate : h3PathWeightedSignedTopRate244 u T hH3 t ≤ 4422 := by
      unfold h3PathWeightedSignedTopRate244
      linarith only [hDiv]
    change max 0 (h3PathWeightedSignedTopRate244 u T hH3 t - 4422) = 0
    exact max_eq_left (sub_nonpos.mpr hRate)
  have hIntegrable : IntegrableOn
      (h3PathWeightedSignedTopRemainder244 u T hH3)
      (Set.Ioo a T) := by
    have hEq : Set.EqOn
        (h3PathWeightedSignedTopRemainder244 u T hH3)
        (fun _ : ℝ => (0 : ℝ)) (Set.Ioo a T) :=
      fun t ht => hZero t ht
    exact (integrableOn_congr_fun hEq measurableSet_Ioo).2 integrableOn_zero
  exact h3Path_extension_of_integrable_weightedSignedTopRemainder244
    hH3 hClass hIntegrable

end
end PrimeTensor.FirstMonomialTriad
