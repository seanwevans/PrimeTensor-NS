import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentRealFractionalL2

/-!
# Fourier-multiplier homogeneous H^(3/2) domain for genuine physical velocities

The preceding audit constructs an actual real-valued L² fractional derivative
of every strict preterminal H³ velocity component, and proves its exact
Plancherel norm. This module no longer defines regularity in terms of a
weighted *solver* state.

Instead it defines a physical scalar L² Fourier-Sobolev criterion: there must
exist a real Euclidean-space L² derivative whose Fourier transform equals
(2π|ξ|)^(3/2) times the Fourier transform of the physical scalar field.
The criterion involves only the physical input and output L² fields.

The multiplier witness is unique (Fourier injectivity and real
complexification), and the already-constructed derivative of an actual
preterminal component is precisely its witness. Under one physical
curl-component strong H³ endpoint, both transverse velocity components
satisfy this criterion, with their real fractional-derivative norms in
L² time on a common strict terminal interval.

This is an explicit Fourier-multiplier domain, not yet an equivalence theorem
for an independently supplied distributional homogeneous Sobolev space or
a formal import of an external Navier--Stokes continuation criterion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3AuditPhysicalHomogeneousSobolev
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact `(2π|ξ|)^(3/2)` multiplier in the project's Fourier convention.
A nested real square root avoids any branch choices for the fractional power. -/
noncomputable def h3AuditPhysicalHomogeneousThreeHalvesWeight
    (ξ : H3FourierPoint3) : ℝ :=
  Real.sqrt (Real.sqrt (h3FourierGradientSquare ξ ^ 3))

/-- An intrinsically physical `Ḣ^(3/2)` derivative relation:
`D` is a real L² field, and its complexified Fourier transform is the
homogeneous 3/2 multiplier of the *physical* real scalar field `f`. -/
def H3AuditPhysicalHomogeneousThreeHalvesDerivativeSpec
    (f : H3ScalarL2) (D : H3FourierRealL2) : Prop :=
  ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
    ((MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3ComplexifyFourierL2 D)) ξ =
      (h3AuditPhysicalHomogeneousThreeHalvesWeight ξ : ℂ) *
        (h3ScalarFourierL2 f) ξ

/-- The physical scalar real L² homogeneous 3/2 Fourier-Sobolev domain,
specified without reference to any weighted H³ solver state. -/
def H3AuditPhysicalHomogeneousThreeHalvesSobolev
    (f : H3ScalarL2) : Prop :=
  ∃ D : H3FourierRealL2,
    H3AuditPhysicalHomogeneousThreeHalvesDerivativeSpec f D

/-- The real physical homogeneous derivative is unique whenever it exists.
The proof uses Fourier injectivity, followed by the exact inverse of
complexification via the real-part projection. -/
theorem h3Audit_physicalHomogeneousThreeHalvesDerivative_unique
    {f : H3ScalarL2} {D₁ D₂ : H3FourierRealL2}
    (h₁ : H3AuditPhysicalHomogeneousThreeHalvesDerivativeSpec f D₁)
    (h₂ : H3AuditPhysicalHomogeneousThreeHalvesDerivativeSpec f D₂) :
    D₁ = D₂ := by
  let FT := MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ
  have hEqFT :
      FT (h3ComplexifyFourierL2 D₁) =
        FT (h3ComplexifyFourierL2 D₂) := by
    apply MeasureTheory.Lp.ext
    filter_upwards [h₁, h₂] with ξ ha hb
    exact ha.trans hb.symm
  have hEqComplex :
      h3ComplexifyFourierL2 D₁ = h3ComplexifyFourierL2 D₂ :=
    FT.injective hEqFT
  simpa only [h3RealPartFourierL2_complexify_eq] using
    congrArg h3RealPartFourierL2 hEqComplex

/-- At each strict preterminal time the *actual real physical velocity*
satisfies the intrinsic homogeneous Fourier derivative relation, with the
real fractional derivative already constructed in the preceding module. -/
theorem h3Audit_actualVelocity_physicalHomogeneousThreeHalves_derivativeSpec
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    H3AuditPhysicalHomogeneousThreeHalvesDerivativeSpec
      (velocityH3L2JetAt u t
        (hH3.velocity_h3_integrable t ht)
        (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
          hH3.navier_stokes ht)
        (h3JetSlot0
          (h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair p))))
      (h3AuditActualVelocityThreeHalvesRealDerivativeAt hH3 p t ht) := by
  let G := h3TerminalComplementSpectralStateAt hH3 p t ht
  let FT := MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ
  have hFourier :
      FT (h3ComplexifyFourierL2
        (h3AuditActualVelocityThreeHalvesRealDerivativeAt hH3 p t ht)) =
      h3AuditThreeHalvesMultiplierCLM G := by
    calc
      FT (h3ComplexifyFourierL2
        (h3AuditActualVelocityThreeHalvesRealDerivativeAt hH3 p t ht)) =
        FT (h3AuditActualVelocityThreeHalvesPhysicalDerivativeAt
          hH3 p t ht) := by
            rw [h3Audit_actualVelocityThreeHalvesPhysicalDerivativeAt_eq_complexify_real
              hH3 p t ht]
      _ = h3AuditThreeHalvesMultiplierCLM G :=
        h3Audit_fourier_threeHalvesPhysicalFractionalL2 G
  have hMul := h3Audit_threeHalvesMultiplierCLM_ae_raw G
  have hPhysical :=
    h3Audit_complementRawFourier_ae_actualVelocityFourier hH3 p t ht
  unfold H3AuditPhysicalHomogeneousThreeHalvesDerivativeSpec
  rw [show h3AuditPhysicalHomogeneousThreeHalvesWeight =
      (fun ξ : H3FourierPoint3 =>
        Real.sqrt (Real.sqrt (h3FourierGradientSquare ξ ^ 3))) from rfl]
  change
    (fun ξ : H3FourierPoint3 =>
      (FT (h3ComplexifyFourierL2
        (h3AuditActualVelocityThreeHalvesRealDerivativeAt hH3 p t ht))) ξ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (Real.sqrt (Real.sqrt (h3FourierGradientSquare ξ ^ 3)) : ℂ) *
      (h3ScalarFourierL2
        (velocityH3L2JetAt u t
          (hH3.velocity_h3_integrable t ht)
          (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
            hH3.navier_stokes ht)
          (h3JetSlot0
            (h3ClassicalizationFinOfAxis
              (h3TerminalComplementComponentAxisForPair p))))) ξ)
  rw [hFourier]
  filter_upwards [hMul, hPhysical] with ξ hAt hVelocity
  rw [hAt, hVelocity]

/-- The real selected velocity snapshot therefore belongs to the intrinsic
Fourier homogeneous 3/2 Sobolev domain at every strict preterminal time. -/
theorem h3Audit_actualVelocity_physicalHomogeneousThreeHalves_membership
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    H3AuditPhysicalHomogeneousThreeHalvesSobolev
      (velocityH3L2JetAt u t
        (hH3.velocity_h3_integrable t ht)
        (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
          hH3.navier_stokes ht)
        (h3JetSlot0
          (h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair p)))) := by
  exact ⟨h3AuditActualVelocityThreeHalvesRealDerivativeAt hH3 p t ht,
    h3Audit_actualVelocity_physicalHomogeneousThreeHalves_derivativeSpec
      hH3 p t ht⟩

/-- Stronger than mere membership: the physical derivative supplied by the
construction is the unique real Fourier 3/2 derivative of this velocity. -/
theorem h3Audit_actualVelocity_physicalHomogeneousThreeHalves_uniqueDerivative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∃! D : H3FourierRealL2,
      H3AuditPhysicalHomogeneousThreeHalvesDerivativeSpec
        (velocityH3L2JetAt u t
          (hH3.velocity_h3_integrable t ht)
          (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
            hH3.navier_stokes ht)
          (h3JetSlot0
            (h3ClassicalizationFinOfAxis
              (h3TerminalComplementComponentAxisForPair p)))) D := by
  refine ⟨h3AuditActualVelocityThreeHalvesRealDerivativeAt hH3 p t ht,
    h3Audit_actualVelocity_physicalHomogeneousThreeHalves_derivativeSpec
      hH3 p t ht, ?_⟩
  intro D hD
  exact h3Audit_physicalHomogeneousThreeHalvesDerivative_unique
    hD (h3Audit_actualVelocity_physicalHomogeneousThreeHalves_derivativeSpec
      hH3 p t ht)

/-- One physical curl-component endpoint supplies both actual transverse
velocity components in the intrinsic physical Fourier-Sobolev domain,
and both real fractional derivative norms in L² time on the same strict
terminal interval. Neither regularity property is postulated here. -/
theorem h3Audit_onePhysicalEndpoint_twoPhysicalHomogeneousThreeHalves_timeL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      (∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
        H3AuditPhysicalHomogeneousThreeHalvesSobolev
          (velocityH3L2JetAt u t
            (hH3.velocity_h3_integrable t ht)
            (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
              hH3.navier_stokes ht)
            (h3JetSlot0 (h3ClassicalizationFinOfAxis
              (h3TerminalComplementComponentAxisForPair
                (h3TerminalActualVorticityPositiveComplementPair i))))) ∧
        H3AuditPhysicalHomogeneousThreeHalvesSobolev
          (velocityH3L2JetAt u t
            (hH3.velocity_h3_integrable t ht)
            (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
              hH3.navier_stokes ht)
            (h3JetSlot0 (h3ClassicalizationFinOfAxis
              (h3TerminalComplementComponentAxisForPair
                (h3TerminalActualVorticityNegativeComplementPair i)))))) ∧
      MemLp (fun t : ℝ =>
        ‖h3AuditActualVelocityThreeHalvesRealDerivativeTotal hH3
          (h3TerminalActualVorticityPositiveComplementPair i) t‖)
        2 (volume.restrict (Set.Ioo c T)) ∧
      MemLp (fun t : ℝ =>
        ‖h3AuditActualVelocityThreeHalvesRealDerivativeTotal hH3
          (h3TerminalActualVorticityNegativeComplementPair i) t‖)
        2 (volume.restrict (Set.Ioo c T)) := by
  obtain ⟨c, hc, hPos, hNeg⟩ :=
    h3Audit_onePhysicalEndpoint_twoRealFractionalDerivative_timeL2
      hH3 hClass i hPhysical
  refine ⟨c, hc, ?_, hPos, hNeg⟩
  intro t ht
  constructor
  · exact h3Audit_actualVelocity_physicalHomogeneousThreeHalves_membership
      hH3 (h3TerminalActualVorticityPositiveComplementPair i) t ht
  · exact h3Audit_actualVelocity_physicalHomogeneousThreeHalves_membership
      hH3 (h3TerminalActualVorticityNegativeComplementPair i) t ht

end
end Euclidean
end Bridge
end PrimeTensor
