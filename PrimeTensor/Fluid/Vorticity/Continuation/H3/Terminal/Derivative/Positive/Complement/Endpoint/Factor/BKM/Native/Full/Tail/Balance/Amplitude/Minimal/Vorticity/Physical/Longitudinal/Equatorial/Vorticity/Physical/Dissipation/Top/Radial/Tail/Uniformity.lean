import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Canonical.Top.Radial.Tail
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Pointwise versus uniform top-order radial-tail decay

The canonical top-order radial tail mass is

    Tail₃(t,R)
      =
    ∫_{|D(ξ)| ≥ R} q(ξ)^4 |û(t,ξ)|² dξ.

At every fixed strict preterminal time `t`, the top-order density is integrable.
Therefore the decreasing sets

    {|D| ≥ n+1}

shrink to the empty set, and dominated convergence gives

    Tail₃(t,n+1) → 0.

So radial escape on a hypothetical nonextension branch cannot mean that a
single fixed preterminal state has a persistent tail.  The obstruction is a
loss of uniformity as `t → T`.

This file packages that distinction exactly.

We define terminal uniform natural-tail vanishing by requiring that, for every
`δ > 0`, one terminal neighborhood and one natural cutoff `N` work
simultaneously for every later natural cutoff `n ≥ N`.

This uniform natural-tail vanishing is equivalent to the canonical radial-tail
tightness criterion proved previously.  Consequently it is sufficient for
smooth continuation under the retained endpoint hypotheses, while hypothetical
nonextension forces its failure.

Thus the nonextension obstruction is precisely:

* pointwise in every fixed strict time, the top-order radial tail tends to zero;
* uniformly near the terminal time, that convergence fails.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopRadialTailUniformity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalTopRadialTailUniformity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Tail monotonicity in the radial cutoff -/

/--
The canonical top-order radial tail mass is antitone in the radial cutoff.
-/
theorem h3TerminalPhysicalTopDissipationRadialTailMass_antitone
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    Antitone
      (fun R : ℝ =>
        h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass t ht R) := by

  intro R Q hRQ

  unfold
    h3TerminalPhysicalTopDissipationRadialTailMassAt

  apply
    h3TerminalPhysicalTopDissipationSetMass_mono
      hH3
      hClass
      ht

  intro ξ hξ

  change
    ¬ h3FourierGradientMagnitude ξ < Q
      at hξ

  change
    ¬ h3FourierGradientMagnitude ξ < R

  intro hBelow

  exact
    hξ
      (lt_of_lt_of_le
        hBelow
        hRQ)

/-! ## Fixed-time tail decay -/

/--
For every fixed strict preterminal time, the canonical top-order H³
dissipation tail tends to zero along the natural radial cutoffs `n+1`.
-/
theorem h3TerminalPhysicalTopDissipationRadialTailMass_tendsto_zero_at_fixed_time
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass t ht ((n : ℝ) + 1))
      atTop
      (𝓝 0) := by

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

  let tailSet : ℕ → Set H3FourierPoint3 :=
    fun n =>
      (h3TerminalRadialFrequencyBelow
        ((n : ℝ) + 1))ᶜ

  have hTopInt :
      Integrable top volume := by

    dsimp only [top, hInt, hMeas, htAbs]

    simpa only using
      (h3TerminalPhysicalTopDissipationDensity_integrable
        hH3 hClass ht)

  have hTailMeas :
      ∀ n : ℕ,
        MeasurableSet (tailSet n) := by

    intro n

    dsimp only [tailSet]

    exact
      (measurableSet_h3TerminalRadialFrequencyBelow
        ((n : ℝ) + 1)).compl

  have hTailAnti :
      Antitone tailSet := by

    intro m n hmn

    intro ξ hξ

    dsimp only [tailSet] at hξ ⊢

    change
      ¬ h3FourierGradientMagnitude ξ
          <
        (n : ℝ) + 1
      at hξ

    change
      ¬ h3FourierGradientMagnitude ξ
          <
        (m : ℝ) + 1

    intro hBelow

    have hCast :
        (m : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hmn

    exact
      hξ
        (lt_of_lt_of_le
          hBelow
          (by linarith))

  have hTailInter :
      (⋂ n : ℕ, tailSet n)
        =
      (∅ : Set H3FourierPoint3) := by

    ext ξ

    constructor

    · intro hξ

      have hAll :
          ∀ n : ℕ,
            ξ ∈ tailSet n := by

        intro n

        exact
          Set.mem_iInter.1 hξ n

      obtain
        ⟨N : ℕ, hN⟩ :=
        exists_nat_gt
          (h3FourierGradientMagnitude ξ)

      have hTailN :=
        hAll N

      dsimp only [tailSet] at hTailN

      change
        ¬ h3FourierGradientMagnitude ξ
            <
          (N : ℝ) + 1
        at hTailN

      exact
        False.elim
          (hTailN
            (lt_trans
              hN
              (by linarith)))

    · intro hξ

      exact
        False.elim
          (by simpa using hξ)

  have hTendsto :
      Tendsto
        (fun n : ℕ =>
          ∫ ξ in tailSet n, top ξ ∂volume)
        atTop
        (𝓝
          (∫ ξ in ⋂ n : ℕ, tailSet n,
            top ξ
            ∂volume)) := by

    exact
      Antitone.tendsto_setIntegral
        hTailMeas
        hTailAnti
        hTopInt.integrableOn

  rw [hTailInter] at hTendsto

  simpa only [
    h3TerminalPhysicalTopDissipationRadialTailMassAt,
    h3TerminalPhysicalTopDissipationSetMassAt,
    tailSet,
    top,
    htAbs,
    hInt,
    hMeas,
    Measure.restrict_empty,
    integral_zero_measure
  ] using
    hTendsto

/-! ## Uniform natural-tail decay near the endpoint -/

/--
Uniform natural-cutoff decay of the top-order radial tail near the terminal
time.

For every tolerance, one terminal neighborhood and one natural cutoff work for
all later natural cutoffs.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailUniformVanishingAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ N : ℕ,
      ∃ η : ℝ,
        0 < η
          ∧
        ∀ t : ℝ,
          ∀ ht : t ∈ Set.Ioo a T,
            dist t T < η
              →
            ∀ n : ℕ,
              N ≤ n
                →
              h3TerminalPhysicalTopDissipationRadialTailMassAt
                  hH3 hClass t ht ((n : ℝ) + 1)
                <
              δ

/-! ## Equivalence with canonical radial-tail tightness -/

/--
Canonical radial-tail tightness implies uniform vanishing along the natural
cutoffs.
-/
theorem naturalRadialTailUniformVanishingAtEndpoint_of_canonicalTopDissipationRadialTailTightAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTail :
      H3TerminalPhysicalTopDissipationCanonicalRadialTailTightAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformVanishingAtEndpoint
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

  obtain
    ⟨N : ℕ, hN⟩ :=
    exists_nat_gt R

  refine
    ⟨
      N,
      η,
      hη,
      ?_
    ⟩

  intro t ht htNear n hn

  have hCast :
      (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  have hRLe :
      R ≤ (n : ℝ) + 1 := by
    linarith

  have hMono :=
    h3TerminalPhysicalTopDissipationRadialTailMass_antitone
      hH3
      hClass
      ht
      hRLe

  exact
    lt_of_le_of_lt
      hMono
      (hSmall t ht htNear)

/--
Uniform vanishing along the natural radial cutoffs implies canonical
radial-tail tightness.
-/
theorem canonicalTopDissipationRadialTailTightAtEndpoint_of_naturalRadialTailUniformVanishingAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hUniform :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformVanishingAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationCanonicalRadialTailTightAtEndpoint
      hH3 hClass := by

  intro δ hδ

  obtain
    ⟨
      N,
      η,
      hη,
      hSmall
    ⟩ :=
    hUniform
      δ
      hδ

  let R : ℝ :=
    (N : ℝ) + 1

  have hR :
      0 < R := by
    dsimp only [R]
    positivity

  refine
    ⟨
      R,
      hR,
      η,
      hη,
      ?_
    ⟩

  intro t ht htNear

  dsimp only [R]

  exact
    hSmall
      t
      ht
      htNear
      N
      le_rfl

/--
Canonical radial-tail tightness is exactly terminal uniform decay of the
natural top-order radial tails.
-/
theorem canonicalTopDissipationRadialTailTightAtEndpoint_iff_naturalRadialTailUniformVanishingAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalPhysicalTopDissipationCanonicalRadialTailTightAtEndpoint
        hH3 hClass
      ↔
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformVanishingAtEndpoint
      hH3 hClass := by

  constructor

  · exact
      naturalRadialTailUniformVanishingAtEndpoint_of_canonicalTopDissipationRadialTailTightAtEndpoint
        hH3
        hClass

  · exact
      canonicalTopDissipationRadialTailTightAtEndpoint_of_naturalRadialTailUniformVanishingAtEndpoint
        hH3
        hClass

/-! ## Continuation and the exact loss-of-uniformity obstruction -/

/--
Terminal uniform natural-tail decay is sufficient for smooth continuation under
the retained endpoint assumptions.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformVanishing_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hUniform :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformVanishingAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hCanonical :
      H3TerminalPhysicalTopDissipationCanonicalRadialTailTightAtEndpoint
        hH3 hClass :=
    canonicalTopDissipationRadialTailTightAtEndpoint_of_naturalRadialTailUniformVanishingAtEndpoint
      hH3
      hClass
      hUniform

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_canonicalTopDissipationRadialTailTightness_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      hCanonical

/--
Under the retained endpoint assumptions, hypothetical nonextension forces
failure of uniform natural-tail decay, even though fixed-time tail decay holds
at every strict preterminal time.
-/
theorem fixedTimeTopDissipationRadialTailVanishing_and_not_uniform_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    (
      ∀ t : ℝ,
        ∀ ht : t ∈ Set.Ioo a T,
          Tendsto
            (fun n : ℕ =>
              h3TerminalPhysicalTopDissipationRadialTailMassAt
                hH3 hClass t ht ((n : ℝ) + 1))
            atTop
            (𝓝 0)
    )
      ∧
    ¬ H3TerminalPhysicalTopDissipationNaturalRadialTailUniformVanishingAtEndpoint
        hH3 hClass := by

  constructor

  · intro t ht

    exact
      h3TerminalPhysicalTopDissipationRadialTailMass_tendsto_zero_at_fixed_time
        hH3
        hClass
        ht

  · intro hUniform

    exact
      hNoExtension
        (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformVanishing_of_actualVorticityStrongH3EndpointPath
          hH3
          hClass
          hPhysical
          hCauchy
          hUniform)

/-! ## Explicit diagonal witness -/

/--
The canonical escape sequence is an explicit diagonal witness to the loss of
uniformity: the cutoff tends to infinity at the same time as the physical time
approaches `T`, while a fixed positive top-order tail mass survives.
-/
theorem canonicalTopDissipationRadialTailDiagonalEscape_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    ∃ δ : ℝ,
      0 < δ
        ∧
      ∃ τ : ℕ → ℝ,
        ∃ hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T,
          Tendsto τ atTop (𝓝 T)
            ∧
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
          ) := by

  obtain
    ⟨
      δ,
      hδ,
      τ,
      hτ,
      hData,
      hTendsto
    ⟩ :=
    canonicalTopDissipationRadialTailEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy

  exact
    ⟨
      δ,
      hδ,
      τ,
      hτ,
      hTendsto,
      hData
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
