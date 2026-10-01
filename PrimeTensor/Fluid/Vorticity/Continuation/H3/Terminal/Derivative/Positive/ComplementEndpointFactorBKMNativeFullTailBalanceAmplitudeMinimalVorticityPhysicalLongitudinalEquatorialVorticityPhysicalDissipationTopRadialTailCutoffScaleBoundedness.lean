import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationTopRadialTailCutoffScale

/-!
# Local boundedness of the canonical top-order radial-tail cutoff scale

For each positive tolerance `ε` and strict preterminal time `t`, the preceding
checkpoint defined the least natural cutoff index

    Nε(t)
      =
    min { n : ℕ | Tail₃(t,n+1) < ε }.

This index is finite at every fixed strict time.

The exact terminal compactness condition is that `Nε(t)` remain locally
bounded as `t → T`, for every `ε > 0`.

This file proves:

* terminal uniform natural-tail vanishing is equivalent to local boundedness of
  every cutoff index `Nε`;
* therefore local boundedness of every `Nε` is sufficient for continuation
  under the retained endpoint hypotheses;
* the previously extracted diverging cutoff-scale sequence upgrades to local
  unboundedness: for one fixed positive tolerance `ε`, every terminal
  neighborhood contains strict times at which `Nε(t)` exceeds any prescribed
  natural bound.

Thus the nonextension obstruction is represented by one canonical scalar
frequency scale which is finite at every strict time but locally unbounded at
the terminal time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopRadialTailCutoffScaleBoundedness
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalTopRadialTailCutoffScaleBoundedness :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Local boundedness and unboundedness predicates -/

/--
For every positive tail tolerance, the least natural cutoff index is bounded on
some terminal neighborhood.
-/
def H3TerminalPhysicalTopDissipationTailCutoffIndexLocallyBoundedAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∀ ε : ℝ,
    ∀ hε : 0 < ε,
      ∃ N : ℕ,
        ∃ η : ℝ,
          0 < η
            ∧
          ∀ t : ℝ,
            ∀ ht : t ∈ Set.Ioo a T,
              dist t T < η
                →
              h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
                  hH3 hClass ε hε t ht
                ≤
              N

/--
For one fixed positive tail tolerance, the least natural cutoff index is
unbounded in every terminal neighborhood.
-/
def H3TerminalPhysicalTopDissipationTailCutoffIndexLocallyUnboundedAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∃ ε : ℝ,
    ∃ hε : 0 < ε,
      ∀ N : ℕ,
        ∀ η : ℝ,
          0 < η
            →
          ∃ t : ℝ,
            ∃ ht : t ∈ Set.Ioo a T,
              dist t T < η
                ∧
              N
                <
              h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
                hH3 hClass ε hε t ht

/-! ## Uniform tail decay implies cutoff-index boundedness -/

/--
Terminal uniform natural-tail decay bounds the least cutoff index on a terminal
neighborhood for every positive tolerance.
-/
theorem topDissipationTailCutoffIndexLocallyBoundedAtEndpoint_of_naturalRadialTailUniformVanishingAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hUniform :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformVanishingAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationTailCutoffIndexLocallyBoundedAtEndpoint
      hH3 hClass := by

  intro ε hε

  obtain
    ⟨
      N,
      η,
      hη,
      hSmall
    ⟩ :=
    hUniform
      ε
      hε

  refine
    ⟨
      N,
      η,
      hη,
      ?_
    ⟩

  intro t ht htNear

  by_contra hNotBounded

  have hNLt :
      N
        <
      h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
        hH3 hClass ε hε t ht :=
    Nat.lt_of_not_ge
      hNotBounded

  have hTailLarge :
      ε
        ≤
      h3TerminalPhysicalTopDissipationRadialTailMassAt
        hH3 hClass t ht ((N : ℝ) + 1) :=
    h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt_minimal
      hH3
      hClass
      ε
      hε
      t
      ht
      N
      hNLt

  have hTailSmall :
      h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass t ht ((N : ℝ) + 1)
        <
      ε :=
    hSmall
      t
      ht
      htNear
      N
      le_rfl

  exact
    (not_lt_of_ge hTailLarge)
      hTailSmall

/-! ## Cutoff-index boundedness implies uniform tail decay -/

/--
If every positive-tolerance least cutoff index is locally bounded near the
terminal time, then the canonical natural radial tails vanish uniformly there.
-/
theorem naturalRadialTailUniformVanishingAtEndpoint_of_topDissipationTailCutoffIndexLocallyBoundedAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hBounded :
      H3TerminalPhysicalTopDissipationTailCutoffIndexLocallyBoundedAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformVanishingAtEndpoint
      hH3 hClass := by

  intro ε hε

  obtain
    ⟨
      N,
      η,
      hη,
      hIndexBound
    ⟩ :=
    hBounded
      ε
      hε

  refine
    ⟨
      N,
      η,
      hη,
      ?_
    ⟩

  intro t ht htNear n hn

  let k : ℕ :=
    h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
      hH3 hClass ε hε t ht

  have hkN :
      k ≤ N := by

    dsimp only [k]

    exact
      hIndexBound
        t
        ht
        htNear

  have hkn :
      k ≤ n :=
    hkN.trans
      hn

  have hCast :
      (k : ℝ) + 1
        ≤
      (n : ℝ) + 1 := by

    have hCast0 :
        (k : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hkn

    linarith

  have hMono :
      h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass t ht ((n : ℝ) + 1)
        ≤
      h3TerminalPhysicalTopDissipationRadialTailMassAt
        hH3 hClass t ht ((k : ℝ) + 1) :=
    h3TerminalPhysicalTopDissipationRadialTailMass_antitone
      hH3
      hClass
      ht
      hCast

  have hSpec :
      h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass t ht ((k : ℝ) + 1)
        <
      ε := by

    dsimp only [k]

    exact
      h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt_spec
        hH3
        hClass
        ε
        hε
        t
        ht

  exact
    lt_of_le_of_lt
      hMono
      hSpec

/-! ## Exact scalar compactness equivalence -/

/--
Terminal uniform natural-tail vanishing is exactly local boundedness of every
least cutoff index.
-/
theorem naturalRadialTailUniformVanishingAtEndpoint_iff_topDissipationTailCutoffIndexLocallyBoundedAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformVanishingAtEndpoint
        hH3 hClass
      ↔
    H3TerminalPhysicalTopDissipationTailCutoffIndexLocallyBoundedAtEndpoint
      hH3 hClass := by

  constructor

  · exact
      topDissipationTailCutoffIndexLocallyBoundedAtEndpoint_of_naturalRadialTailUniformVanishingAtEndpoint
        hH3
        hClass

  · exact
      naturalRadialTailUniformVanishingAtEndpoint_of_topDissipationTailCutoffIndexLocallyBoundedAtEndpoint
        hH3
        hClass

/-! ## Scalar continuation criterion -/

/--
Under the retained endpoint assumptions, local boundedness of every canonical
least top-order radial-tail cutoff index is sufficient for smooth continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_topDissipationTailCutoffIndexLocallyBounded_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hBounded :
      H3TerminalPhysicalTopDissipationTailCutoffIndexLocallyBoundedAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hUniform :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformVanishingAtEndpoint
        hH3 hClass :=
    naturalRadialTailUniformVanishingAtEndpoint_of_topDissipationTailCutoffIndexLocallyBoundedAtEndpoint
      hH3
      hClass
      hBounded

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformVanishing_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      hUniform

/-! ## Diverging sequence implies local unboundedness -/

/--
A diverging canonical cutoff-scale sequence implies local unboundedness of that
same fixed-tolerance cutoff index in every terminal neighborhood.
-/
theorem topDissipationTailCutoffIndexLocallyUnboundedAtEndpoint_of_tailCutoffScaleEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape :
      H3TerminalPhysicalTopDissipationTailCutoffScaleEscapeSequence
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationTailCutoffIndexLocallyUnboundedAtEndpoint
      hH3 hClass := by

  obtain
    ⟨
      ε,
      hε,
      τ,
      hτ,
      hData,
      hτTendsto,
      hIndexTendsto,
      hRadiusTendsto
    ⟩ :=
    hEscape

  refine
    ⟨
      ε,
      hε,
      ?_
    ⟩

  intro N η hη

  have hNear :
      ∀ᶠ n : ℕ in atTop,
        dist (τ n) T < η := by

    have hBall :
        Metric.ball T η ∈ 𝓝 T :=
      Metric.ball_mem_nhds
        T
        hη

    have hEventually :=
      hτTendsto.eventually
        hBall

    filter_upwards
      [hEventually]
      with n hn

    simpa only [
      Metric.mem_ball,
      dist_comm
    ] using
      hn

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        N
          <
        h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
          hH3 hClass ε hε (τ n) (hτ n) := by

    have hEventually :
        ∀ᶠ n : ℕ in atTop,
          N + 1
            ≤
          h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
            hH3 hClass ε hε (τ n) (hτ n) :=
      (tendsto_atTop.1 hIndexTendsto)
        (N + 1)

    filter_upwards
      [hEventually]
      with n hn

    omega

  obtain
    ⟨
      n,
      hnNear,
      hnLarge
    ⟩ :=
    (hNear.and hLarge).exists

  exact
    ⟨
      τ n,
      hτ n,
      hnNear,
      hnLarge
    ⟩

/-! ## Endpoint consequence -/

/--
Under the retained endpoint assumptions, hypothetical nonextension forces one
fixed positive tail tolerance whose canonical least cutoff index is locally
unbounded in every terminal neighborhood.
-/
theorem topDissipationTailCutoffIndexLocallyUnboundedAtEndpoint_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalPhysicalTopDissipationTailCutoffIndexLocallyUnboundedAtEndpoint
      hH3 hClass := by

  exact
    topDissipationTailCutoffIndexLocallyUnboundedAtEndpoint_of_tailCutoffScaleEscapeSequence
      hH3
      hClass
      (topDissipationTailCutoffScaleEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hCauchy)

/-! ## Neutral formulation -/

/--
Neutral endpoint alternative: either the H³ path extends smoothly through `T`,
or one fixed positive top-order tail tolerance has a canonical least radial
cutoff index which is unbounded in every terminal neighborhood.

This is stronger than merely exhibiting one diverging subsequence and gives a
fully local scalar formulation of the surviving frequency-escape obstruction.
-/
theorem smoothContinuationExtension_or_topDissipationTailCutoffIndexLocallyUnboundedAtEndpoint
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
    H3TerminalPhysicalTopDissipationTailCutoffIndexLocallyUnboundedAtEndpoint
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
        (topDissipationTailCutoffIndexLocallyUnboundedAtEndpoint_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
