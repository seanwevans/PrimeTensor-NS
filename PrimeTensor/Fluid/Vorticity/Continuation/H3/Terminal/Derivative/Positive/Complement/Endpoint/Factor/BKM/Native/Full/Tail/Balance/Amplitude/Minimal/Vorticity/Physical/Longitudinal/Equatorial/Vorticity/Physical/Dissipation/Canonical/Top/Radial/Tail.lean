import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Arbitrary.Coercive.Radial.Weight

/-!
# Canonical top-order radial tails

The top-order radial-tail compactness predicate inherited a hereditary
formulation:

* for every measurable subset `S` of the far radial region,
* the localized top-order dissipation mass of `S` is small.

For the physical top-order H³ dissipation density this extra quantification is
unnecessary because the density is nonnegative.  It is enough to control the
single canonical set

    (h3TerminalRadialFrequencyBelow R)ᶜ.

This file introduces the canonical top-order radial tail mass

    Tail₃(t,R)
      =
    ∫_{|D(ξ)| ≥ R} q(ξ)^4 |û(t,ξ)|² dξ,

proves that the hereditary radial-tail tightness predicate is equivalent to
smallness of this one tail integral, and upgrades the previously extracted
radial escape sequence so that the escaping set is always the full radial
tail.

Thus under the retained endpoint assumptions, hypothetical nonextension
forces a fixed positive amount of physical top-order H³ dissipation to remain
in the entire region `|D| ≥ n+1` along a terminal sequence.

No claim is made that the nonextension branch is realizable.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalCanonicalTopRadialTail
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalCanonicalTopRadialTail :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Monotonicity of localized top-order mass -/

/--
Localized physical top-order H³ dissipation mass is monotone in the measurable
region because its density is nonnegative.
-/
theorem h3TerminalPhysicalTopDissipationSetMass_mono
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {S U : Set H3FourierPoint3}
    (hSU : S ⊆ U) :
    h3TerminalPhysicalTopDissipationSetMassAt
        hH3 hClass t ht S
      ≤
    h3TerminalPhysicalTopDissipationSetMassAt
      hH3 hClass t ht U := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let top : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 4
        *
      velocityH3FourierMassDensityAt
        u t hInt hMeas ξ

  have hTopInt :
      Integrable top volume := by
    dsimp only [top, hInt, hMeas, htAbs]
    simpa only using
      (h3TerminalPhysicalTopDissipationDensity_integrable
        hH3 hClass ht)

  have hTopNonneg :
      0 ≤ᵐ[volume] top := by
    exact
      Eventually.of_forall
        (fun ξ => by
          dsimp only [top]
          exact
            mul_nonneg
              (pow_nonneg
                (h3FourierGradientSquare_nonneg ξ)
                4)
              (velocityH3FourierMassDensityAt_nonneg
                u t hInt hMeas ξ))

  unfold
    h3TerminalPhysicalTopDissipationSetMassAt

  change
    (∫ ξ in S, top ξ ∂volume)
      ≤
    ∫ ξ in U, top ξ ∂volume

  apply
    setIntegral_mono_set
      hTopInt.integrableOn

  · exact
      hTopNonneg.filter_mono
        ae_restrict_le

  · exact
      Eventually.of_forall
        (fun ξ hξ =>
          hSU hξ)

/-! ## Canonical full radial-tail mass -/

/--
Physical top-order H³ dissipation mass in the entire complement of the radial
frequency ball of radius `R`.
-/
noncomputable def h3TerminalPhysicalTopDissipationRadialTailMassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T)
    (R : ℝ) : ℝ :=
  h3TerminalPhysicalTopDissipationSetMassAt
    hH3 hClass t ht
    (h3TerminalRadialFrequencyBelow R)ᶜ

/--
Every localized top-order mass carried by a subset of the radial tail is
bounded by the canonical full radial-tail mass.
-/
theorem h3TerminalPhysicalTopDissipationSetMass_le_radialTailMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {S : Set H3FourierPoint3}
    (hS :
      S ⊆ (h3TerminalRadialFrequencyBelow R)ᶜ) :
    h3TerminalPhysicalTopDissipationSetMassAt
        hH3 hClass t ht S
      ≤
    h3TerminalPhysicalTopDissipationRadialTailMassAt
      hH3 hClass t ht R := by

  unfold
    h3TerminalPhysicalTopDissipationRadialTailMassAt

  exact
    h3TerminalPhysicalTopDissipationSetMass_mono
      hH3
      hClass
      ht
      hS

/-! ## Canonical radial-tail tightness -/

/--
Canonical top-order radial-tail tightness: only the whole complement of one
radial ball is tested.
-/
def H3TerminalPhysicalTopDissipationCanonicalRadialTailTightAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ R : ℝ,
      0 < R
        ∧
      ∃ η : ℝ,
        0 < η
          ∧
        ∀ t : ℝ,
          ∀ ht : t ∈ Set.Ioo a T,
            dist t T < η
              →
            h3TerminalPhysicalTopDissipationRadialTailMassAt
                hH3 hClass t ht R
              <
            δ

/--
The hereditary top-order radial-tail tightness predicate implies canonical
full-tail tightness.
-/
theorem canonicalTopDissipationRadialTailTightAtEndpoint_of_topDissipationRadialTailTightAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTail :
      H3TerminalPhysicalTopDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationCanonicalRadialTailTightAtEndpoint
      hH3 hClass := by

  intro δ hδ

  obtain
    ⟨
      R,
      hR,
      η,
      hη,
      hSmall
    ⟩ :=
    hTail
      δ
      hδ

  refine
    ⟨
      R,
      hR,
      η,
      hη,
      ?_
    ⟩

  intro t ht htNear

  unfold
    h3TerminalPhysicalTopDissipationRadialTailMassAt

  exact
    hSmall
      t
      ht
      htNear
      (h3TerminalRadialFrequencyBelow R)ᶜ
      (measurableSet_h3TerminalRadialFrequencyBelow R).compl
      (by intro ξ hξ; exact hξ)

/--
Canonical full-tail tightness implies the hereditary top-order radial-tail
tightness predicate.
-/
theorem topDissipationRadialTailTightAtEndpoint_of_canonicalTopDissipationRadialTailTightAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTail :
      H3TerminalPhysicalTopDissipationCanonicalRadialTailTightAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationSingleTimeRadialTailTightAtEndpoint
      hH3 hClass := by

  intro δ hδ

  obtain
    ⟨
      R,
      hR,
      η,
      hη,
      hSmall
    ⟩ :=
    hTail
      δ
      hδ

  refine
    ⟨
      R,
      hR,
      η,
      hη,
      ?_
    ⟩

  intro t ht htNear S hS hOutside

  have hSubsetLe :
      h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass t ht S
        ≤
      h3TerminalPhysicalTopDissipationRadialTailMassAt
        hH3 hClass t ht R :=
    h3TerminalPhysicalTopDissipationSetMass_le_radialTailMass
      hH3
      hClass
      ht
      hOutside

  exact
    lt_of_le_of_lt
      hSubsetLe
      (hSmall t ht htNear)

/--
The hereditary and canonical formulations of top-order radial-tail tightness
are equivalent.
-/
theorem topDissipationRadialTailTightAtEndpoint_iff_canonical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalPhysicalTopDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass
      ↔
    H3TerminalPhysicalTopDissipationCanonicalRadialTailTightAtEndpoint
      hH3 hClass := by

  constructor

  · exact
      canonicalTopDissipationRadialTailTightAtEndpoint_of_topDissipationRadialTailTightAtEndpoint
        hH3
        hClass

  · exact
      topDissipationRadialTailTightAtEndpoint_of_canonicalTopDissipationRadialTailTightAtEndpoint
        hH3
        hClass

/-! ## Canonical full-tail escape sequence -/

/--
A fixed positive amount of top-order physical H³ dissipation survives in the
entire radial tail outside cutoff `n+1`, along times converging to `T`.
-/
def H3TerminalPhysicalTopDissipationCanonicalRadialTailEscapeSequence
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
              ∧
            δ
                ≤
              h3TerminalPhysicalTopDissipationRadialTailMassAt
                hH3 hClass (τ n) (hτ n) ((n : ℝ) + 1)
        )
          ∧
        Tendsto τ atTop (𝓝 T)

/--
Every previously extracted top-order radial escape sequence canonically
upgrades to escape of the entire radial tail on the same terminal times.
-/
theorem canonicalTopDissipationRadialTailEscapeSequence_of_topDissipationRadialEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape :
      H3TerminalPhysicalTopDissipationRadialEscapeSequence
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationCanonicalRadialTailEscapeSequence
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
      ?_,
      hτTendsto
    ⟩

  intro n

  have hSubsetLe :
      h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass (τ n) (ht n) (S n)
        ≤
      h3TerminalPhysicalTopDissipationRadialTailMassAt
        hH3 hClass (τ n) (ht n) ((n : ℝ) + 1) :=
    h3TerminalPhysicalTopDissipationSetMass_le_radialTailMass
      hH3
      hClass
      (ht n)
      (hOutside n)

  exact
    ⟨
      hNear n,
      (hMass n).trans hSubsetLe
    ⟩

/-! ## Endpoint consequence -/

/--
Under the retained endpoint hypotheses, hypothetical nonextension forces a
canonical full-radial-tail escape sequence for the physical top-order H³
dissipation.
-/
theorem canonicalTopDissipationRadialTailEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalPhysicalTopDissipationCanonicalRadialTailEscapeSequence
      hH3 hClass := by

  exact
    canonicalTopDissipationRadialTailEscapeSequence_of_topDissipationRadialEscapeSequence
      hH3
      hClass
      (physicalTopDissipationRadialEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hCauchy)

/--
The continuation criterion may equivalently be stated using only the canonical
full radial-tail mass.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_canonicalTopDissipationRadialTailTightness_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hTail :
      H3TerminalPhysicalTopDissipationCanonicalRadialTailTightAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hHereditary :
      H3TerminalPhysicalTopDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass :=
    topDissipationRadialTailTightAtEndpoint_of_canonicalTopDissipationRadialTailTightAtEndpoint
      hH3
      hClass
      hTail

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalTopDissipationRadialTailTightness_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      hHereditary

/-! ## Neutral formulation -/

/--
Neutral endpoint alternative: either the H³ path extends smoothly through
`T`, or a fixed positive amount of physical top-order H³ dissipation survives
in the entire radial tail outside cutoff `n+1` along a terminal sequence.

The escaping region is canonical; no auxiliary measurable witness sets remain.
-/
theorem smoothContinuationExtension_or_canonicalTopDissipationRadialTailEscapeSequence
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
    H3TerminalPhysicalTopDissipationCanonicalRadialTailEscapeSequence
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
        (canonicalTopDissipationRadialTailEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
