import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationTopRadialTailCutoffScaleBoundedness

/-!
# Cofinality of the canonical top-order radial-tail cutoff scale

The preceding checkpoint identified hypothetical nonextension with local
unboundedness of one fixed-tolerance canonical cutoff index

    Nε(t)
      =
    min { n : ℕ | Tail₃(t,n+1) < ε }.

Local unboundedness in every terminal neighborhood has a stronger selection
consequence.

For every prescribed natural profile

    g : ℕ → ℕ,

one can choose strict terminal times `τₙ → T` satisfying

    dist(τₙ,T) < 1/(n+1)

and simultaneously

    g(n) < Nε(τₙ).

Thus the canonical cutoff scale is cofinal against every prescribed natural
index profile after terminal-time selection.

This must not be interpreted as a physical-time growth rate.  The times are
chosen depending on `g`; no lower bound of the form

    Nε(t) ≥ F(T-t)

is asserted.

The theorem is therefore an exact cofinality statement for the surviving
frequency-scale obstruction, not a quantitative singularity-rate claim.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopRadialTailCutoffScaleCofinality
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalTopRadialTailCutoffScaleCofinality :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Cofinal escape package -/

/--
For one fixed positive tail tolerance, every prescribed natural growth profile
can be dominated by the canonical least cutoff index along a terminal sequence.

The terminal sequence may depend on the prescribed profile.
-/
def H3TerminalPhysicalTopDissipationTailCutoffIndexCofinalEscapeAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∃ ε : ℝ,
    ∃ hε : 0 < ε,
      ∀ g : ℕ → ℕ,
        ∃ τ : ℕ → ℝ,
          ∃ hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T,
            (
              ∀ n : ℕ,
                dist (τ n) T
                    <
                  (1 : ℝ) / ((n : ℝ) + 1)
                  ∧
                g n
                    <
                  h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
                    hH3 hClass ε hε (τ n) (hτ n)
            )
              ∧
            Tendsto τ atTop (𝓝 T)

/-! ## Local unboundedness gives arbitrary-profile cofinality -/

/--
If one fixed-tolerance canonical cutoff index is unbounded in every terminal
neighborhood, then it dominates every prescribed natural profile along a
suitably selected terminal sequence.
-/
theorem topDissipationTailCutoffIndexCofinalEscapeAtEndpoint_of_locallyUnboundedAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hUnbounded :
      H3TerminalPhysicalTopDissipationTailCutoffIndexLocallyUnboundedAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationTailCutoffIndexCofinalEscapeAtEndpoint
      hH3 hClass := by

  obtain
    ⟨
      ε,
      hε,
      hLocal
    ⟩ :=
    hUnbounded

  refine
    ⟨
      ε,
      hε,
      ?_
    ⟩

  intro g

  have hChoice :
      ∀ n : ℕ,
        ∃ t : ℝ,
          ∃ ht : t ∈ Set.Ioo a T,
            dist t T
                <
              (1 : ℝ) / ((n : ℝ) + 1)
              ∧
            g n
                <
              h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
                hH3 hClass ε hε t ht := by

    intro n

    have hRadiusPos :
        0
          <
        (1 : ℝ) / ((n : ℝ) + 1) := by
      positivity

    exact
      hLocal
        (g n)
        ((1 : ℝ) / ((n : ℝ) + 1))
        hRadiusPos

  choose τ hτ hNear hAbove using hChoice

  have hInv :
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / ((n : ℝ) + 1)
        )
        atTop
        (𝓝 0) := by

    have hInvShift :
        Tendsto
          (
            fun n : ℕ =>
              (1 : ℝ) / ((n + 1 : ℕ) : ℝ)
          )
          atTop
          (𝓝 0) := by

      exact
        (tendsto_const_div_atTop_nhds_zero_nat
          (1 : ℝ)).comp
          (tendsto_add_atTop_nat 1)

    convert hInvShift using 1

    ext n

    norm_num

  have hTauTendsto :
      Tendsto τ atTop (𝓝 T) := by

    rw [
      tendsto_iff_dist_tendsto_zero
    ]

    exact
      squeeze_zero
        (fun n : ℕ =>
          dist_nonneg)
        (fun n : ℕ =>
          le_of_lt
            (hNear n))
        hInv

  refine
    ⟨
      τ,
      hτ,
      ?_,
      hTauTendsto
    ⟩

  intro n

  exact
    ⟨
      hNear n,
      hAbove n
    ⟩

/-! ## Growing prescribed profiles force corresponding cutoff divergence -/

/--
If the prescribed profile itself tends to `+∞`, then the selected canonical
cutoff indices also tend to `+∞`.
-/
theorem exists_terminal_topDissipationTailCutoffIndex_dominating_profile
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hCofinal :
      H3TerminalPhysicalTopDissipationTailCutoffIndexCofinalEscapeAtEndpoint
        hH3 hClass)
    (g : ℕ → ℕ)
    (hg :
      Tendsto g atTop atTop) :
    ∃ ε : ℝ,
      ∃ hε : 0 < ε,
        ∃ τ : ℕ → ℝ,
          ∃ hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T,
            (
              ∀ n : ℕ,
                dist (τ n) T
                    <
                  (1 : ℝ) / ((n : ℝ) + 1)
                  ∧
                g n
                    <
                  h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
                    hH3 hClass ε hε (τ n) (hτ n)
            )
              ∧
            Tendsto τ atTop (𝓝 T)
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
                    hH3 hClass ε hε (τ n) (hτ n)
              )
              atTop
              atTop := by

  obtain
    ⟨
      ε,
      hε,
      hUniversal
    ⟩ :=
    hCofinal

  obtain
    ⟨
      τ,
      hτ,
      hData,
      hTau
    ⟩ :=
    hUniversal
      g

  have hIndexTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
              hH3 hClass ε hε (τ n) (hτ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hEventuallyG :
        ∀ᶠ n : ℕ in atTop,
          M ≤ g n :=
      (tendsto_atTop.1 hg)
        M

    filter_upwards
      [hEventuallyG]
      with n hn

    exact
      hn.trans
        (Nat.le_of_lt
          (hData n).2)

  exact
    ⟨
      ε,
      hε,
      τ,
      hτ,
      hData,
      hTau,
      hIndexTop
    ⟩

/-! ## Endpoint consequence -/

/--
Under the retained endpoint hypotheses, hypothetical nonextension forces the
canonical top-order tail cutoff index to be cofinal against every prescribed
natural profile after selecting terminal times for that profile.

This is a selection/cofinality theorem only.  It does not provide a growth
rate as a function of physical time-to-endpoint.
-/
theorem topDissipationTailCutoffIndexCofinalEscapeAtEndpoint_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalPhysicalTopDissipationTailCutoffIndexCofinalEscapeAtEndpoint
      hH3 hClass := by

  exact
    topDissipationTailCutoffIndexCofinalEscapeAtEndpoint_of_locallyUnboundedAtEndpoint
      hH3
      hClass
      (topDissipationTailCutoffIndexLocallyUnboundedAtEndpoint_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hCauchy)

/-! ## Neutral formulation -/

/--
Neutral endpoint alternative: either the H³ path extends smoothly through
`T`, or one fixed positive top-order tail tolerance has a canonical least
cutoff index which is cofinal against every prescribed natural index profile
along a profile-dependent terminal sequence.

No physical-time rate is asserted.
-/
theorem smoothContinuationExtension_or_topDissipationTailCutoffIndexCofinalEscapeAtEndpoint
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
    H3TerminalPhysicalTopDissipationTailCutoffIndexCofinalEscapeAtEndpoint
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
        (topDissipationTailCutoffIndexCofinalEscapeAtEndpoint_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
