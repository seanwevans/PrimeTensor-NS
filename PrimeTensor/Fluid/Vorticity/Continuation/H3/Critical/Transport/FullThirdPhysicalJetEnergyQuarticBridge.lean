import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdRealSolenoidalSchwartzPhysicalPDETransportLimit
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3WeightedCanonicalQuarticBound244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzActualThirdJetIdentification244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Bridge.Energy
import Mathlib.Tactic

/-!
# Exact physical 27/81 jet energies and the signed H³ quartic barrier

The real solenoidal Schwartz recovery now represents the actual physical
third-order Navier--Stokes transport. Its canonical E₂/E₃ energy limits
still use the weighted spectral reconstruction names. Here we identify
those *canonical* finite sums with the original velocityH3Energy2At and
velocityH3Energy3At at every Fourier-compatible physical H³ slice.

Each identification uses the existing EXACT old L² jet theorem and the
PrimeTensor.Depth finite axis/Fin 3 reindexing lemmas. No Sobolev-norm
equivalence is substituted, so neither energy acquires a multiplicative
constant. The previously compiled canonical signed quartic bound then
becomes an unconditional physical-snapshot inequality:

  |M_phys|^4 <= K^4 E₂_phys (E₃_phys)^5.

The physical 243-slot interpolation has multiplicity three, yielding the
precise factor 3^4. These are necessary inequalities, not a favorable-sign
result, a closed continuation estimate, or a singularity exclusion.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Filter Topology PrimeTensor.Bridge.Euclidean
open scoped BigOperators ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 1400000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev J2 := A3 × (A3 × A3)
private abbrev J3 := A3 × (A3 × (A3 × A3))

noncomputable local instance axisFintypePhysicalJetQuartic244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact, constant-one identification of canonical second-order H³
spectral mass with the original 27-term physical spatial energy. -/
theorem thirdFullPhysical_canonicalSecondJetEnergy_eq244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    weightedH3CanonicalSecondJetEnergy244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier) =
    velocityH3Energy2At u t := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  have hJet (j a b : A3) :
      matchedSpectralSecondFourierJets244 U (j, (a, b)) =
        h3ToFourierRealL2
          (velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot2 (h3ClassicalizationFinOfAxis j)
              (h3ClassicalizationFinOfAxis a)
              (h3ClassicalizationFinOfAxis b))) := by
    have hActual := h3SpectralVelocitySecondPhysicalJetFamily_actualJet244
      hFourier
    have hCoord := congrFun (congrFun
      (congrFun hActual (h3ClassicalizationFinOfAxis j)) a) b
    exact congrArg h3ToFourierRealL2 hCoord
  have hReindex :
      (∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
        ‖velocityH3L2JetAt u t hInt hMeas (h3JetSlot2 j a b)‖ ^ 2) =
      (∑ j : A3, ∑ a : A3, ∑ b : A3,
        ‖velocityH3L2JetAt u t hInt hMeas
          (h3JetSlot2 (h3ClassicalizationFinOfAxis j)
            (h3ClassicalizationFinOfAxis a)
            (h3ClassicalizationFinOfAxis b))‖ ^ 2) := by
    have h := sum_fin3_comp_h3AxisOfFin3_three
      (fun j a b : A3 =>
        ‖velocityH3L2JetAt u t hInt hMeas
          (h3JetSlot2 (h3ClassicalizationFinOfAxis j)
            (h3ClassicalizationFinOfAxis a)
            (h3ClassicalizationFinOfAxis b))‖ ^ 2)
    simpa only [h3ClassicalizationFinOfAxis_h3AxisOfFin3] using h
  have hOld :
      (∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
        ‖velocityH3L2JetAt u t hInt hMeas (h3JetSlot2 j a b)‖ ^ 2) =
      velocityH3Energy2At u t := by
    simpa only [h3JetSlot2, Fintype.sum_prod_type] using
      (velocityH3L2JetAt_squareEnergy2_eq hInt hMeas)
  calc
    weightedH3CanonicalSecondJetEnergy244 U =
        ∑ j : A3, ∑ a : A3, ∑ b : A3,
          ‖h3ToFourierRealL2
            (velocityH3L2JetAt u t hInt hMeas
              (h3JetSlot2 (h3ClassicalizationFinOfAxis j)
                (h3ClassicalizationFinOfAxis a)
                (h3ClassicalizationFinOfAxis b)))‖ ^ 2 := by
      unfold weightedH3CanonicalSecondJetEnergy244
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact congrArg (fun x : H3FourierRealL2 => ‖x‖ ^ 2) (hJet j a b)
    _ = ∑ j : A3, ∑ a : A3, ∑ b : A3,
          ‖velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot2 (h3ClassicalizationFinOfAxis j)
              (h3ClassicalizationFinOfAxis a)
              (h3ClassicalizationFinOfAxis b))‖ ^ 2 := by
      simp only [norm_h3ToFourierRealL2]
    _ = ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
          ‖velocityH3L2JetAt u t hInt hMeas (h3JetSlot2 j a b)‖ ^ 2 :=
      hReindex.symm
    _ = velocityH3Energy2At u t := hOld

/-- Exact, constant-one identification of canonical third-order H³
spectral mass with the original 81-term physical spatial energy. -/
theorem thirdFullPhysical_canonicalThirdJetEnergy_eq244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    weightedH3CanonicalThirdJetEnergy244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier) =
    velocityH3Energy3At u t := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  have hJet (j a b c : A3) :
      matchedSpectralThirdFourierJets244 U (j, (a, (b, c))) =
        h3ToFourierRealL2
          (velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot3 (h3ClassicalizationFinOfAxis j)
              (h3ClassicalizationFinOfAxis a)
              (h3ClassicalizationFinOfAxis b)
              (h3ClassicalizationFinOfAxis c))) := by
    have hActual := h3SpectralVelocityThirdPhysicalJetFamily_actualJet244
      hFourier
    have hCoord := congrFun (congrFun (congrFun
      (congrFun hActual (h3ClassicalizationFinOfAxis j)) a) b) c
    exact congrArg h3ToFourierRealL2 hCoord
  have hReindex :
      (∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        ‖velocityH3L2JetAt u t hInt hMeas (h3JetSlot3 j a b c)‖ ^ 2) =
      (∑ j : A3, ∑ a : A3, ∑ b : A3, ∑ c : A3,
        ‖velocityH3L2JetAt u t hInt hMeas
          (h3JetSlot3 (h3ClassicalizationFinOfAxis j)
            (h3ClassicalizationFinOfAxis a)
            (h3ClassicalizationFinOfAxis b)
            (h3ClassicalizationFinOfAxis c))‖ ^ 2) := by
    have h := sum_fin3_comp_h3AxisOfFin3_four
      (fun j a b c : A3 =>
        ‖velocityH3L2JetAt u t hInt hMeas
          (h3JetSlot3 (h3ClassicalizationFinOfAxis j)
            (h3ClassicalizationFinOfAxis a)
            (h3ClassicalizationFinOfAxis b)
            (h3ClassicalizationFinOfAxis c))‖ ^ 2)
    simpa only [h3ClassicalizationFinOfAxis_h3AxisOfFin3] using h
  have hOld :
      (∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        ‖velocityH3L2JetAt u t hInt hMeas (h3JetSlot3 j a b c)‖ ^ 2) =
      velocityH3Energy3At u t := by
    simpa only [h3JetSlot3, Fintype.sum_prod_type] using
      (velocityH3L2JetAt_squareEnergy3_eq hInt hMeas)
  calc
    weightedH3CanonicalThirdJetEnergy244 U =
        ∑ j : A3, ∑ a : A3, ∑ b : A3, ∑ c : A3,
          ‖h3ToFourierRealL2
            (velocityH3L2JetAt u t hInt hMeas
              (h3JetSlot3 (h3ClassicalizationFinOfAxis j)
                (h3ClassicalizationFinOfAxis a)
                (h3ClassicalizationFinOfAxis b)
                (h3ClassicalizationFinOfAxis c)))‖ ^ 2 := by
      unfold weightedH3CanonicalThirdJetEnergy244
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      exact congrArg (fun x : H3FourierRealL2 => ‖x‖ ^ 2) (hJet j a b c)
    _ = ∑ j : A3, ∑ a : A3, ∑ b : A3, ∑ c : A3,
          ‖velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot3 (h3ClassicalizationFinOfAxis j)
              (h3ClassicalizationFinOfAxis a)
              (h3ClassicalizationFinOfAxis b)
              (h3ClassicalizationFinOfAxis c))‖ ^ 2 := by
      simp only [norm_h3ToFourierRealL2]
    _ = ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          ‖velocityH3L2JetAt u t hInt hMeas (h3JetSlot3 j a b c)‖ ^ 2 :=
      hReindex.symm
    _ = velocityH3Energy3At u t := hOld

/-- The signed physical 243-slot H³ interpolation obeys the native
canonical quartic bound in the ORIGINAL E₂/E₃ energies, with no extra
Schwartz-realization premise and no norm conversion constant. -/
theorem thirdFullPhysical_signedMonomial_quarticEnergyBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    |h3PathCanonicalFirstMonomialAggregateAt u t| ^ 4 ≤
      lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
        (velocityH3Energy2At u t * (velocityH3Energy3At u t) ^ 5) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  have h := weightedH3CanonicalSignedFirstMonomial_quarticBound244 U
  rw [← h3PathCanonicalFirstMonomialAggregate_eq_weightedCanonicalSigned244 hFourier,
    thirdFullPhysical_canonicalSecondJetEnergy_eq244 hFourier,
    thirdFullPhysical_canonicalThirdJetEnergy_eq244 hFourier] at h
  exact h

/-- Exact physical cyclic multiplicity three gives factor 3^4 in the
quartic barrier for the full top-order interpolation block. -/
theorem thirdFullPhysical_interpolationTransport_quarticEnergyBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    |thirdOrderInterpolationTransportSum u t| ^ 4 ≤
      (3 : ℝ) ^ 4 *
        (lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
          (velocityH3Energy2At u t * (velocityH3Energy3At u t) ^ 5)) := by
  have hIdentity :=
    h3PathCanonical_interpolation_eq_three_firstMonomialAggregate
      hH3 hClass ht
  have hSigned := thirdFullPhysical_signedMonomial_quarticEnergyBound244
    hFourier
  calc
    |thirdOrderInterpolationTransportSum u t| ^ 4 =
        (3 : ℝ) ^ 4 * |h3PathCanonicalFirstMonomialAggregateAt u t| ^ 4 := by
      rw [hIdentity, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), mul_pow]
    _ ≤ (3 : ℝ) ^ 4 *
          (lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
            (velocityH3Energy2At u t * (velocityH3Energy3At u t) ^ 5)) :=
      mul_le_mul_of_nonneg_left hSigned (by norm_num)

end
end PrimeTensor.FirstMonomialTriad
