import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedInterpolationCoordinate

/-!
# Isolate a genuinely signed D³u · (D²u D²u) monomial

The full third-order interpolation commutator contains 81 derivative-coordinate
pairings. Each coordinate pairing has three velocity axes, with three genuine
D²u·D²u monomials per axis. Its exact signed expansion thus has 729 pairings.

The existing H³ Landau analytic package supplies integrability of every
triple-product pairing. Consequently an adverse physical coordinate witness
can be passed to an actual monomial without taking absolute values.

Without extra hypotheses, each high-growth signed witness yields a monomial
below one 729th of the remaining gradient/dissipation budget. Under the
explicit terminal gradient-absorption hypothesis, hypothetical nonextension
forces monomials of arbitrarily negative normalized size. Conversely a
uniform lower bound on all monomials together with that absorption condition
implies continuation. No new cancellation or gradient absorption is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable local instance axisFintypeH3SignedInterpolationMonomial
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One genuine signed triple-product spatial pairing; the three values of
`n : Fin 3` select the three pre-existing interpolation monomials. -/
noncomputable def h3PathCanonicalInterpolationMonomialPairing
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (j i k l r : PrimeTensor.Axis Depth.three)
    (n : Fin 3) : ℝ :=
  let f := spatial3.d i
    (spatial3.d k (spatial3.d l (loggedVelocityComponent u t j)))
  if n = 0 then
    spatialEnergyPairing f (thirdOrderInterpolationMonomial1 u t i k l j r)
  else if n = 1 then
    spatialEnergyPairing f (thirdOrderInterpolationMonomial2 u t i k l j r)
  else
    spatialEnergyPairing f (thirdOrderInterpolationMonomial3 u t i k l j r)

/-- One velocity-axis subpairing of the physical coordinate interpolation. -/
noncomputable def h3PathCanonicalInterpolationAxisPairing
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (j i k l r : PrimeTensor.Axis Depth.three) : ℝ :=
  spatialEnergyPairing
    (spatial3.d i (spatial3.d k (spatial3.d l (loggedVelocityComponent u t j))))
    (thirdTransportCommutatorAxisInterpolationBlock
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r)

/-- Exact decomposition of an axis subpairing into its three actual signed
second-derivative-product monomials. -/
theorem h3PathCanonical_axisPairing_eq_threeMonomials
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : H3OrderThreeInterpolationMonomialPairingIntegrableAt u t)
    (j i k l r : PrimeTensor.Axis Depth.three) :
    h3PathCanonicalInterpolationAxisPairing u t j i k l r =
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 +
        (h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1 +
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2) := by
  let f : ScalarField3 := spatial3.d i
    (spatial3.d k (spatial3.d l (loggedVelocityComponent u t j)))
  let m1 := thirdOrderInterpolationMonomial1 u t i k l j r
  let m2 := thirdOrderInterpolationMonomial2 u t i k l j r
  let m3 := thirdOrderInterpolationMonomial3 u t i k l j r
  have hr := hInt i k l j r
  dsimp only at hr
  have h1 : Integrable (fun x : Point3 => f x * m1 x) := by
    simpa only [f, m1] using hr.1
  have h2 : Integrable (fun x : Point3 => f x * m2 x) := by
    simpa only [f, m2] using hr.2.1
  have h3 : Integrable (fun x : Point3 => f x * m3 x) := by
    simpa only [f, m3] using hr.2.2
  have h23 : Integrable (fun x : Point3 => f x * (m2 x + m3 x)) := by
    have hFun :
        (fun x : Point3 => f x * (m2 x + m3 x)) =
          (fun x : Point3 => f x * m2 x) +
            (fun x : Point3 => f x * m3 x) := by
      funext x
      simp only [Pi.add_apply, mul_add]
    rw [hFun]
    exact h2.add h3
  have hPair23 : spatialEnergyPairing f (fun x => m2 x + m3 x) =
      spatialEnergyPairing f m2 + spatialEnergyPairing f m3 :=
    spatialEnergyPairing_add_of_integrable h2 h3
  have hPair123 :
      spatialEnergyPairing f (fun x => m1 x + (m2 x + m3 x)) =
        spatialEnergyPairing f m1 +
          (spatialEnergyPairing f m2 + spatialEnergyPairing f m3) := by
    rw [spatialEnergyPairing_add_of_integrable h1 h23, hPair23]
  unfold h3PathCanonicalInterpolationAxisPairing
  rw [thirdTransportCommutatorAxisInterpolationBlock_logged_eq_monomials
    u t i k l j r]
  change spatialEnergyPairing f (fun x => m1 x + (m2 x + m3 x)) =
    spatialEnergyPairing f m1 +
      (spatialEnergyPairing f m2 + spatialEnergyPairing f m3)
  exact hPair123

/-- The coordinate interpolation splits into its three signed velocity-axis
subpairings. This uses only the already-proved monomial integrability. -/
theorem h3PathCanonical_coordinatePairing_eq_threeAxes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : H3OrderThreeInterpolationMonomialPairingIntegrableAt u t)
    (j i k l : PrimeTensor.Axis Depth.three) :
    h3PathCanonicalInterpolationCoordinatePairing u t j i k l =
      h3PathCanonicalInterpolationAxisPairing u t j i k l xAxis +
        (h3PathCanonicalInterpolationAxisPairing u t j i k l yAxis +
          h3PathCanonicalInterpolationAxisPairing u t j i k l zAxis) := by
  let f : ScalarField3 := spatial3.d i
    (spatial3.d k (spatial3.d l (loggedVelocityComponent u t j)))
  let ax : PrimeTensor.Axis Depth.three → ScalarField3 := fun r =>
    thirdTransportCommutatorAxisInterpolationBlock
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r
  have hAxisInt (r : PrimeTensor.Axis Depth.three) :
      Integrable (fun x : Point3 => f x * ax r x) := by
    have hr := hInt i k l j r
    dsimp only at hr
    have h1 : Integrable (fun x : Point3 =>
        f x * thirdOrderInterpolationMonomial1 u t i k l j r x) := by
      simpa only [f] using hr.1
    have h2 : Integrable (fun x : Point3 =>
        f x * thirdOrderInterpolationMonomial2 u t i k l j r x) := by
      simpa only [f] using hr.2.1
    have h3 : Integrable (fun x : Point3 =>
        f x * thirdOrderInterpolationMonomial3 u t i k l j r x) := by
      simpa only [f] using hr.2.2
    change Integrable (fun x : Point3 => f x *
      thirdTransportCommutatorAxisInterpolationBlock
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r x)
    rw [thirdTransportCommutatorAxisInterpolationBlock_logged_eq_monomials
      u t i k l j r]
    have hFun :
        (fun x : Point3 =>
          f x *
            (thirdOrderInterpolationMonomial1 u t i k l j r x +
              (thirdOrderInterpolationMonomial2 u t i k l j r x +
                thirdOrderInterpolationMonomial3 u t i k l j r x))) =
          (fun x : Point3 => f x * thirdOrderInterpolationMonomial1 u t i k l j r x) +
            ((fun x : Point3 => f x * thirdOrderInterpolationMonomial2 u t i k l j r x) +
              (fun x : Point3 => f x * thirdOrderInterpolationMonomial3 u t i k l j r x)) := by
      funext x
      simp only [Pi.add_apply, mul_add]
    rw [hFun]
    exact h1.add (h2.add h3)
  have hYZ : Integrable (fun x : Point3 =>
      f x * (ax yAxis x + ax zAxis x)) := by
    have hFun :
        (fun x : Point3 => f x * (ax yAxis x + ax zAxis x)) =
          (fun x : Point3 => f x * ax yAxis x) +
            (fun x : Point3 => f x * ax zAxis x) := by
      funext x
      simp only [Pi.add_apply, mul_add]
    rw [hFun]
    exact (hAxisInt yAxis).add (hAxisInt zAxis)
  have hSplitYZ : spatialEnergyPairing f (fun x => ax yAxis x + ax zAxis x) =
      spatialEnergyPairing f (ax yAxis) +
        spatialEnergyPairing f (ax zAxis) :=
    spatialEnergyPairing_add_of_integrable (hAxisInt yAxis) (hAxisInt zAxis)
  have hSplitXYZ :
      spatialEnergyPairing f (fun x => ax xAxis x + (ax yAxis x + ax zAxis x)) =
        spatialEnergyPairing f (ax xAxis) +
          (spatialEnergyPairing f (ax yAxis) +
            spatialEnergyPairing f (ax zAxis)) := by
    rw [spatialEnergyPairing_add_of_integrable (hAxisInt xAxis) hYZ, hSplitYZ]
  unfold h3PathCanonicalInterpolationCoordinatePairing
  unfold thirdTransportCommutatorInterpolationBlock
  change spatialEnergyPairing f (fun x => ax xAxis x + (ax yAxis x + ax zAxis x)) =
      spatialEnergyPairing f (ax xAxis) +
        (spatialEnergyPairing f (ax yAxis) +
          spatialEnergyPairing f (ax zAxis))
  exact hSplitXYZ

/-- Signed nine-term pigeonhole lemma for three axes and three monomials,
without replacing any term by an absolute value. -/
theorem h3PathCanonical_nine_signed_exists_lt
    (f g h : PrimeTensor.Axis Depth.three → ℝ)
    (B : ℝ)
    (hSum :
      (f xAxis + (g xAxis + h xAxis)) +
        ((f yAxis + (g yAxis + h yAxis)) +
          (f zAxis + (g zAxis + h zAxis))) < 9 * B) :
    ∃ r : PrimeTensor.Axis Depth.three,
      f r < B ∨ g r < B ∨ h r < B := by
  by_contra hNone
  have hAll (r : PrimeTensor.Axis Depth.three) :
      B ≤ f r ∧ B ≤ g r ∧ B ≤ h r := by
    have hf : B ≤ f r := by
      apply le_of_not_gt
      intro hBad
      exact hNone ⟨r, Or.inl hBad⟩
    have hg : B ≤ g r := by
      apply le_of_not_gt
      intro hBad
      exact hNone ⟨r, Or.inr (Or.inl hBad)⟩
    have hh : B ≤ h r := by
      apply le_of_not_gt
      intro hBad
      exact hNone ⟨r, Or.inr (Or.inr hBad)⟩
    exact ⟨hf, hg, hh⟩
  rcases hAll xAxis with ⟨hx1, hx2, hx3⟩
  rcases hAll yAxis with ⟨hy1, hy2, hy3⟩
  rcases hAll zAxis with ⟨hz1, hz2, hz3⟩
  linarith only [hSum, hx1, hx2, hx3, hy1, hy2, hy3, hz1, hz2, hz3]

/-- A signed adverse coordinate forces one of its actual nine monomial
pairings below one ninth of that coordinate budget. -/
theorem h3PathCanonical_coordinate_forces_signedMonomial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t B : ℝ}
    (hInt : H3OrderThreeInterpolationMonomialPairingIntegrableAt u t)
    (j i k l : PrimeTensor.Axis Depth.three)
    (hCoordinate :
      h3PathCanonicalInterpolationCoordinatePairing u t j i k l < 9 * B) :
    ∃ r : PrimeTensor.Axis Depth.three,
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 < B ∨
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1 < B ∨
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2 < B := by
  rw [h3PathCanonical_coordinatePairing_eq_threeAxes hInt j i k l] at hCoordinate
  rw [h3PathCanonical_axisPairing_eq_threeMonomials hInt j i k l xAxis,
    h3PathCanonical_axisPairing_eq_threeMonomials hInt j i k l yAxis,
    h3PathCanonical_axisPairing_eq_threeMonomials hInt j i k l zAxis] at hCoordinate
  exact h3PathCanonical_nine_signed_exists_lt
    (fun r => h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0)
    (fun r => h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1)
    (fun r => h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2)
    B hCoordinate

/-- Monomial pairings are genuinely integrable at all H³ energy-class
slices; no new hypothesis is required beyond the proved Landau package. -/
theorem h3PathCanonical_monomialIntegrable_on_h3Slice
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    H3OrderThreeInterpolationMonomialPairingIntegrableAt u t := by
  let h : ℝ → ℝ := h3PathCanonicalSqrtEnergyGradientEnvelope u
  have hGradient : VelocityGradientEnvelope u h t := by
    simpa only [h] using
      h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass ht
  have hT : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hH3At : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t hT
  have hSobolev6 : WholeSpaceC1H1ToL6 :=
    wholeSpaceC1H1ToL6_of_fderiv wholeSpaceC1FDerivL2ToL6_cutoff
  have hSobolev : WholeSpaceC1H1ToL4 :=
    wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6 hSobolev6
  have hCore : H3OrderThreeInterpolationLandauCoreAnalyticDataAt u h t := by
    simpa [H3OrderThreeInterpolationLandauCoreAnalyticDataAt] using hGradient
  have hAnalytic : H3OrderThreeInterpolationLandauAnalyticDataAt u h t :=
    h3OrderThreeInterpolationLandauAnalyticDataAt_of_core
      hSobolev wholeSpaceQuarticDerivativeIntegrationByParts_cutoff
      hClass ht hH3At hCore
  exact h3OrderThreeInterpolationMonomialPairingIntegrableAt_of_landauAnalyticData
    hAnalytic

/-- Each physical signed top-order transport witness forces an actual
D³u · (D²u D²u) monomial to carry one 729th of the residual deficit. -/
theorem h3PathCanonical_signedAdversity_forces_explicitMonomial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t) :
    ∃ j i k l r : PrimeTensor.Axis Depth.three,
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 <
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
          velocityH3DissipationAt u t - M * velocityH3EnergyAt u t) / 729 ∨
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1 <
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
          velocityH3DissipationAt u t - M * velocityH3EnergyAt u t) / 729 ∨
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2 <
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
          velocityH3DissipationAt u t - M * velocityH3EnergyAt u t) / 729 := by
  let Q : ℝ :=
    24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
      velocityH3DissipationAt u t - M * velocityH3EnergyAt u t
  obtain ⟨j, i, k, l, hCoordinate⟩ :=
    h3PathCanonical_signedAdversity_forces_explicit_coordinateDeficit
      hH3 hClass ht hAdverse
  have hBudget :
      h3PathCanonicalInterpolationCoordinatePairing u t j i k l <
        9 * (Q / 729) := by
    change 81 * h3PathCanonicalInterpolationCoordinatePairing u t j i k l < Q at hCoordinate
    linarith only [hCoordinate]
  obtain ⟨r, hBad⟩ :=
    h3PathCanonical_coordinate_forces_signedMonomial
      (h3PathCanonical_monomialIntegrable_on_h3Slice hH3 hClass ht)
      j i k l hBudget
  exact ⟨j, i, k, l, r, by simpa only [Q] using hBad⟩

/-- Under eventual gradient absorption, nonextension forces arbitrarily
negative individual triple-product pairings on every strict subtail. -/
theorem h3PathCanonical_signedMonomial_witness_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hR : 0 ≤ R)
    (hAbsorption : ∀ t : ℝ, t ∈ Set.Ioo d T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ≤
          velocityH3DissipationAt u t) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      ∃ j i k l r : PrimeTensor.Axis Depth.three,
        h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 <
          -R * velocityH3EnergyAt u t ∨
        h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1 <
          -R * velocityH3EnergyAt u t ∨
        h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2 <
          -R * velocityH3EnergyAt u t := by
  have hNine : 0 ≤ 9 * R := mul_nonneg (by norm_num) hR
  obtain ⟨t, ht, j, i, k, l, hCoordinate⟩ :=
    h3PathCanonical_interpolation_coordinate_witness_of_noExtension
      hH3 hNoExtension hClass hb hd hNine hAbsorption
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have hBudget :
      h3PathCanonicalInterpolationCoordinatePairing u t j i k l <
        9 * (-R * velocityH3EnergyAt u t) := by
    nlinarith only [hCoordinate]
  obtain ⟨r, hBad⟩ :=
    h3PathCanonical_coordinate_forces_signedMonomial
      (h3PathCanonical_monomialIntegrable_on_h3Slice hH3 hClass htClass)
      j i k l hBudget
  exact ⟨t, ht, j, i, k, l, r, hBad⟩

/-- A uniform lower bound for all actual signed interpolation monomials,
plus explicit gradient absorption, excludes the monomial nonextension witness. -/
theorem h3PathCanonical_extension_of_signedMonomialLowerBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hR : 0 ≤ R)
    (hAbsorption : ∀ t : ℝ, t ∈ Set.Ioo d T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ≤
          velocityH3DissipationAt u t)
    (hLower : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∀ j i k l r : PrimeTensor.Axis Depth.three,
        ∀ n : Fin 3,
          -R * velocityH3EnergyAt u t ≤
            h3PathCanonicalInterpolationMonomialPairing u t j i k l r n) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨t, ht, j, i, k, l, r, hBad⟩ :=
    h3PathCanonical_signedMonomial_witness_of_noExtension
      hH3 hNoExtension hClass hb hd hR hAbsorption
  rcases hBad with hFirst | hSecond | hThird
  · exact (not_lt_of_ge (hLower t ht j i k l r 0)) hFirst
  · exact (not_lt_of_ge (hLower t ht j i k l r 1)) hSecond
  · exact (not_lt_of_ge (hLower t ht j i k l r 2)) hThird

end Euclidean
end Bridge
end PrimeTensor
