import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationTopRadialTailUniformity
import Mathlib.Data.Nat.Find

/-!
# Canonical top-order radial-tail cutoff scale

The preceding checkpoint identified the nonextension obstruction as loss of
uniform decay of the canonical top-order H³ dissipation radial tail

    Tail₃(t,R)
      =
    ∫_{|D(ξ)| ≥ R} q(ξ)^4 |û(t,ξ)|² dξ.

At every fixed strict preterminal time this tail tends to zero as
`R → +∞`.  Therefore, for every fixed tolerance `ε > 0`, there is a least
natural cutoff index after which the tail has dropped below `ε`.

This file packages that least cutoff as a canonical scalar frequency scale.

For strict `t`, define

    Nε(t)
      =
    min { n : ℕ | Tail₃(t,n+1) < ε }

and the corresponding real radial scale

    Rε(t) = Nε(t) + 1.

The fixed-time tail theorem makes `Nε(t)` finite at every strict time.

On the hypothetical nonextension branch, the canonical tail-escape sequence
supplies a fixed `δ > 0` with

    δ ≤ Tail₃(τₙ,n+1).

Taking `ε = δ/2`, minimality forces

    n < Nε(τₙ),

hence

    n+1 < Rε(τₙ),

and both the natural cutoff index and real cutoff radius tend to `+∞`.

Thus the frequency escape can be represented by one canonical scalar scale,
without auxiliary measurable witness sets or selected Fourier points.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopRadialTailCutoffScale
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalTopRadialTailCutoffScale :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Existence of a finite cutoff at every strict time -/

/--
At every fixed strict preterminal time and every positive tolerance, some
natural radial cutoff makes the canonical top-order dissipation tail smaller
than that tolerance.
-/
theorem exists_naturalTopDissipationRadialTailMass_lt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hε : 0 < ε) :
    ∃ n : ℕ,
      h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass t ht ((n : ℝ) + 1)
        <
      ε := by

  have hTendsto :=
    h3TerminalPhysicalTopDissipationRadialTailMass_tendsto_zero_at_fixed_time
      hH3
      hClass
      ht

  exact
    (
      hTendsto.eventually
        (Iio_mem_nhds hε)
    ).exists

/-! ## Least natural cutoff index -/

/--
Least natural radial cutoff index at which the canonical top-order dissipation
tail is below the positive tolerance `ε`.
-/
noncomputable def h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ε : ℝ)
    (hε : 0 < ε)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T) : ℕ :=
  Nat.find
    (exists_naturalTopDissipationRadialTailMass_lt
      hH3 hClass ht hε)

/--
The canonical tail is below `ε` at the least cutoff index.
-/
theorem h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt_spec
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ε : ℝ)
    (hε : 0 < ε)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalTopDissipationRadialTailMassAt
        hH3 hClass t ht
        (
          (h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
              hH3 hClass ε hε t ht : ℝ)
            + 1
        )
      <
    ε := by

  exact
    Nat.find_spec
      (exists_naturalTopDissipationRadialTailMass_lt
        hH3 hClass ht hε)

/--
Every smaller natural cutoff still carries at least `ε` top-order tail mass.
-/
theorem h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt_minimal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ε : ℝ)
    (hε : 0 < ε)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T)
    (m : ℕ)
    (hm :
      m
        <
      h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
        hH3 hClass ε hε t ht) :
    ε
      ≤
    h3TerminalPhysicalTopDissipationRadialTailMassAt
      hH3 hClass t ht ((m : ℝ) + 1) := by

  have hNot :
      ¬
        h3TerminalPhysicalTopDissipationRadialTailMassAt
            hH3 hClass t ht ((m : ℝ) + 1)
          <
        ε := by

    apply
      Nat.find_min
        (exists_naturalTopDissipationRadialTailMass_lt
          hH3 hClass ht hε)

    exact
      hm

  exact
    le_of_not_gt
      hNot

/--
If the tail at natural cutoff `n+1` still carries at least `ε`, then `n` lies
strictly below the least cutoff index.
-/
theorem lt_naturalTailCutoffIndex_of_threshold_le_tailMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ε : ℝ)
    (hε : 0 < ε)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T)
    (n : ℕ)
    (hTail :
      ε
        ≤
      h3TerminalPhysicalTopDissipationRadialTailMassAt
        hH3 hClass t ht ((n : ℝ) + 1)) :
    n
      <
    h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
      hH3 hClass ε hε t ht := by

  by_contra hNot

  have hFindLe :
      h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
          hH3 hClass ε hε t ht
        ≤
      n :=
    Nat.le_of_not_gt
      hNot

  have hCast :
      (
        h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
            hH3 hClass ε hε t ht : ℝ
      ) + 1
        ≤
      (n : ℝ) + 1 := by

    have hCast' :
        (
          h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
              hH3 hClass ε hε t ht : ℝ
        )
          ≤
        (n : ℝ) := by
      exact_mod_cast hFindLe

    linarith

  have hMono :
      h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass t ht ((n : ℝ) + 1)
        ≤
      h3TerminalPhysicalTopDissipationRadialTailMassAt
        hH3 hClass t ht
        (
          (h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
              hH3 hClass ε hε t ht : ℝ)
            + 1
        ) :=
    h3TerminalPhysicalTopDissipationRadialTailMass_antitone
      hH3
      hClass
      ht
      hCast

  have hSpec :=
    h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt_spec
      hH3
      hClass
      ε
      hε
      t
      ht

  have hTailLt :
      h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass t ht ((n : ℝ) + 1)
        <
      ε :=
    lt_of_le_of_lt
      hMono
      hSpec

  exact
    (not_lt_of_ge hTail)
      hTailLt

/-! ## Real cutoff radius -/

/--
Real radial cutoff associated to the least natural tail index.
-/
noncomputable def h3TerminalPhysicalTopDissipationTailCutoffRadiusAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ε : ℝ)
    (hε : 0 < ε)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T) : ℝ :=
  (
    h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
      hH3 hClass ε hε t ht : ℝ
  ) + 1

theorem h3TerminalPhysicalTopDissipationTailCutoffRadiusAt_pos
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ε : ℝ)
    (hε : 0 < ε)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T) :
    0
      <
    h3TerminalPhysicalTopDissipationTailCutoffRadiusAt
      hH3 hClass ε hε t ht := by

  unfold
    h3TerminalPhysicalTopDissipationTailCutoffRadiusAt

  positivity

/--
The canonical tail is below the threshold at its cutoff radius.
-/
theorem h3TerminalPhysicalTopDissipationTailCutoffRadiusAt_spec
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ε : ℝ)
    (hε : 0 < ε)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalTopDissipationRadialTailMassAt
        hH3 hClass t ht
        (h3TerminalPhysicalTopDissipationTailCutoffRadiusAt
          hH3 hClass ε hε t ht)
      <
    ε := by

  exact
    h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt_spec
      hH3
      hClass
      ε
      hε
      t
      ht

/-! ## Diverging cutoff-scale escape package -/

/--
A fixed tail tolerance whose canonical least cutoff index and corresponding
real radial cutoff both diverge along terminal times.
-/
def H3TerminalPhysicalTopDissipationTailCutoffScaleEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
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
              n
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
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalPhysicalTopDissipationTailCutoffRadiusAt
                  hH3 hClass ε hε (τ n) (hτ n)
            )
            atTop
            atTop

/-! ## Canonical radial escape implies cutoff-scale escape -/

/--
Canonical full-tail escape forces divergence of one fixed-tolerance least
tail-cutoff scale.
-/
theorem topDissipationTailCutoffScaleEscapeSequence_of_canonicalRadialTailEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape :
      H3TerminalPhysicalTopDissipationCanonicalRadialTailEscapeSequence
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationTailCutoffScaleEscapeSequence
      hH3 hClass := by

  obtain
    ⟨
      δ,
      hδ,
      τ,
      hτ,
      hData,
      hτTendsto
    ⟩ :=
    hEscape

  let ε : ℝ :=
    δ / 2

  have hε :
      0 < ε := by
    dsimp only [ε]
    linarith

  have hIndexLower :
      ∀ n : ℕ,
        n
          <
        h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
          hH3 hClass ε hε (τ n) (hτ n) := by

    intro n

    have hTailDelta :
        δ
          ≤
        h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass (τ n) (hτ n) ((n : ℝ) + 1) :=
      (hData n).2

    have hTailEpsilon :
        ε
          ≤
        h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass (τ n) (hτ n) ((n : ℝ) + 1) := by
      dsimp only [ε]
      linarith

    exact
      lt_naturalTailCutoffIndex_of_threshold_le_tailMass
        hH3
        hClass
        ε
        hε
        (τ n)
        (hτ n)
        n
        hTailEpsilon

  have hIndexTendsto :
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

    filter_upwards
      [eventually_ge_atTop M]
      with n hn

    exact
      hn.trans
        (Nat.le_of_lt
          (hIndexLower n))

  have hRadiusTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalPhysicalTopDissipationTailCutoffRadiusAt
              hH3 hClass ε hε (τ n) (hτ n)
        )
        atTop
        atTop := by

    unfold
      h3TerminalPhysicalTopDissipationTailCutoffRadiusAt

    have hCast :
        Tendsto
          (
            fun n : ℕ =>
              (
                h3TerminalPhysicalTopDissipationNaturalTailCutoffIndexAt
                  hH3 hClass ε hε (τ n) (hτ n) : ℝ
              )
          )
          atTop
          atTop :=
      tendsto_natCast_atTop_atTop.comp
        hIndexTendsto

    exact
      tendsto_atTop_add_const_right
        atTop
        (1 : ℝ)
        hCast

  refine
    ⟨
      ε,
      hε,
      τ,
      hτ,
      ?_,
      hτTendsto,
      hIndexTendsto,
      hRadiusTendsto
    ⟩

  intro n

  exact
    ⟨
      (hData n).1,
      hIndexLower n
    ⟩

/-! ## Endpoint consequence -/

/--
Under the retained endpoint assumptions, hypothetical nonextension forces a
fixed positive top-order tail tolerance whose least natural radial cutoff scale
diverges along terminal times.
-/
theorem topDissipationTailCutoffScaleEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalPhysicalTopDissipationTailCutoffScaleEscapeSequence
      hH3 hClass := by

  exact
    topDissipationTailCutoffScaleEscapeSequence_of_canonicalRadialTailEscapeSequence
      hH3
      hClass
      (canonicalTopDissipationRadialTailEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hCauchy)

/-! ## Neutral formulation -/

/--
Neutral endpoint alternative: either the H³ path extends smoothly through
`T`, or a fixed positive top-order tail tolerance has a canonical least radial
cutoff scale which diverges along a terminal sequence.

The cutoff scale is finite at every individual strict time by fixed-time
integrability; the obstruction is its terminal divergence.
-/
theorem smoothContinuationExtension_or_topDissipationTailCutoffScaleEscapeSequence
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
    H3TerminalPhysicalTopDissipationTailCutoffScaleEscapeSequence
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
        (topDissipationTailCutoffScaleEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
