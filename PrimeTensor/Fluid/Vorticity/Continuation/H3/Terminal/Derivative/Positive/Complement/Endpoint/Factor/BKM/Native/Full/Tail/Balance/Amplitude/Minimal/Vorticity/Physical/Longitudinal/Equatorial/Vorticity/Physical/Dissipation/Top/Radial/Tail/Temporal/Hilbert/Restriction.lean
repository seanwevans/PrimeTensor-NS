import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Derivative
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Remove cutoff dependence from the sharp-tail Hilbert derivative

The preceding checkpoint reduced the localized sharp-tail balance to strong
derivatives of the three cutoff-dependent Hilbert paths

    1_{|D| ≥ R} q² û_j(t).

The cutoff itself should not be part of the temporal differentiation problem.
Mathlib already provides the contractive continuous linear restriction map

    L²(volume) → L²(volume.restrict S).

This file uses that map to separate the two operations.

First package the *global* fourth-radial coordinate

    q² û_j(t)

as an ordinary Fourier `L²` path.  For a fixed radial tail set `S_R`, restrict
that global path to `L²(volume.restrict S_R)`.  Its squared norm is exactly the
same localized coordinate mass as the indicator realization from
`Temporal.Hilbert.State`.

Because restriction is continuous linear, any strong derivative of the global
weighted path is carried automatically to every fixed cutoff.  Thus one global
three-component derivative theorem suffices simultaneously for all natural
sharp radial tails.

This is useful for the PDE step: the remaining temporal target is now

    d/dt (q² û_j)
      =
    -q³ û_j - q² F_j(U,U)

in global Fourier `L²` at each strict preterminal time.  The existing positive
time regularity already supplies the spatial `L²` orders suggested by this
identity; no cutoff-dependent difference quotient remains.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailHilbertRestriction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Generic `L²` norm-square formula for a restricted measure -/

/--
The standard `L²` norm-square identity, specialized to the Fourier carrier but
with an arbitrary restricted volume measure.
-/
theorem h3FourierComplexL2Restrict_norm_sq_eq_integral_norm_sq
    (S : Set H3FourierPoint3)
    (f :
      Lp ℂ 2
        ((volume : Measure H3FourierPoint3).restrict S)) :
    ‖f‖ ^ 2
      =
    ∫ ξ : H3FourierPoint3,
      ‖f ξ‖ ^ 2
      ∂((volume : Measure H3FourierPoint3).restrict S) := by

  calc
    ‖f‖ ^ 2 = Complex.re ⟪f, f⟫_ℂ :=
      norm_sq_eq_re_inner (𝕜 := ℂ) f
    _ =
      Complex.re
        (∫ ξ : H3FourierPoint3,
          ⟪f ξ, f ξ⟫_ℂ
          ∂((volume : Measure H3FourierPoint3).restrict S)) := by
      rw [MeasureTheory.L2.inner_def]
    _ =
      ∫ ξ : H3FourierPoint3,
        Complex.re ⟪f ξ, f ξ⟫_ℂ
        ∂((volume : Measure H3FourierPoint3).restrict S) := by
      symm
      exact
        Complex.reCLM.integral_comp_comm
          (MeasureTheory.L2.integrable_inner f f)
    _ =
      ∫ ξ : H3FourierPoint3,
        ‖f ξ‖ ^ 2
        ∂((volume : Measure H3FourierPoint3).restrict S) := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [inner_self_eq_norm_sq_to_K]
      norm_cast

/-! ## Global fourth-radial Fourier `L²` coordinate -/

/--
The global `q² û_j` coordinate as an actual Fourier `L²` element at one strict
preterminal time.
-/
noncomputable def h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    H3FourierComplexL2 :=
  (
    h3TerminalPhysicalTopDissipationFourthRadialComponent_memLp2
      hH3 hClass ht j
  ).toLp
    (
      h3TerminalPhysicalTopDissipationFourthRadialComponent
        hH3 hClass ht j
    )

/--
The global fourth-radial `L²` state has the expected representative almost
everywhere.
-/
theorem h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    (
      (h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
        hH3 hClass ht j :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[volume]
    h3TerminalPhysicalTopDissipationFourthRadialComponent
      hH3 hClass ht j := by

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (
        h3TerminalPhysicalTopDissipationFourthRadialComponent_memLp2
          hH3 hClass ht j
      )

/--
The global fourth-radial coordinate as an ordinary path on all of `ℝ`, set to
zero outside the strict energy-class interval.
-/
noncomputable def h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
      hH3 hClass ht j
  else
    0

@[simp]
theorem h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
        hH3 hClass j t
      =
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
      hH3 hClass ht j := by

  unfold
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path

  simp only [dif_pos ht]

/-! ## Restrict the global path to one radial tail -/

/--
The contractive real-linear restriction map from global Fourier `L²` to the
same functions viewed in `L²` of the restricted radial-tail measure.
-/
noncomputable def h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
    (R : ℝ) :
    H3FourierComplexL2 →L[ℝ]
      Lp ℂ 2
        (
          (volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow R)ᶜ
        ) :=
  MeasureTheory.LpToLpRestrictCLM
    H3FourierPoint3
    ℂ
    ℝ
    (volume : Measure H3FourierPoint3)
    2
    (h3TerminalRadialFrequencyBelow R)ᶜ

/--
One global fourth-radial coordinate restricted to the sharp radial tail.
-/
noncomputable def h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R : ℝ)
    (j : Fin 3)
    (t : ℝ) :
    Lp ℂ 2
      (
        (volume : Measure H3FourierPoint3).restrict
          (h3TerminalRadialFrequencyBelow R)ᶜ
      ) :=
  h3TerminalPhysicalTopDissipationRadialTailRestrictCLM R
    (
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
        hH3 hClass j t
    )

/-! ## Restricted and indicator realizations have the same norm -/

/--
At a strict preterminal time, the restricted-measure realization and the
indicator realization have exactly the same squared `L²` norm.
-/
theorem norm_sq_h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ‖h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
        hH3 hClass R j t‖ ^ 2
      =
    ‖h3TerminalPhysicalTopDissipationRadialTailComponentL2At
        hH3 hClass ht R j‖ ^ 2 := by

  let S : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow R)ᶜ

  let F : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
      hH3 hClass ht j

  have hPath :
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j t
        =
      F := by
    dsimp only [F]
    exact
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_eq
        hH3 hClass ht j

  have hRestrict :
      (
        (
          h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
            hH3 hClass R j t :
          Lp ℂ 2
            ((volume : Measure H3FourierPoint3).restrict S)
        ) :
        H3FourierPoint3 → ℂ
      )
        =ᵐ[
          (volume : Measure H3FourierPoint3).restrict S
        ]
      F := by

    unfold
      h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
      h3TerminalPhysicalTopDissipationRadialTailRestrictCLM

    rw [hPath]

    exact
      MeasureTheory.LpToLpRestrictCLM_coeFn
        ℝ
        S
        F

  have hGlobal :
      ((F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[
          (volume : Measure H3FourierPoint3).restrict S
        ]
      h3TerminalPhysicalTopDissipationFourthRadialComponent
        hH3 hClass ht j := by

    exact
      ae_restrict_of_ae
        (
          h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_ae
            hH3 hClass ht j
        )

  rw [
    h3FourierComplexL2Restrict_norm_sq_eq_integral_norm_sq
      S
  ]

  rw [
    norm_sq_h3TerminalPhysicalTopDissipationRadialTailComponentL2At
      hH3 hClass ht R j
  ]

  apply integral_congr_ae

  filter_upwards [hRestrict, hGlobal] with ξ hRestrictξ hGlobalξ

  rw [hRestrictξ, hGlobalξ]

  unfold
    h3TerminalPhysicalTopDissipationFourthRadialComponent

  dsimp only

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg
      (pow_nonneg
        (h3FourierGradientSquare_nonneg ξ)
        2),
    mul_pow
  ]

  ring

/-! ## Exact restricted Hilbert realization of the scalar tail -/

/--
The natural sharp-tail scalar path is also exactly the sum of the three
squared norms in the restricted-measure Hilbert spaces.
-/
theorem h3TerminalPhysicalTopDissipationNaturalRadialTailPath_eq_sum_norm_sq_restricted
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (n : ℕ) :
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath
        hH3 hClass n
      =
    fun t : ℝ =>
      ∑ j : Fin 3,
        ‖h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
            hH3 hClass ((n : ℝ) + 1) j t‖ ^ 2 := by

  funext t

  by_cases ht :
      t ∈ Set.Ioo a T

  · have hOld :=
      congrFun
        (
          h3TerminalPhysicalTopDissipationNaturalRadialTailPath_eq_hilbertEnergyPath
            hH3 hClass n
        )
        t

    rw [hOld]

    unfold
      h3TerminalPhysicalTopDissipationRadialTailHilbertEnergyPath

    apply Finset.sum_congr rfl

    intro j hj

    rw [
      h3TerminalPhysicalTopDissipationRadialTailComponentL2Path_eq
        hH3 hClass ht j
    ]

    exact
      (
        norm_sq_h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
          hH3 hClass ht j
      ).symm

  · unfold
      h3TerminalPhysicalTopDissipationNaturalRadialTailPath
      h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path

    simp [ht]

/-! ## Restriction transports strong derivatives -/

/--
A strong derivative of the global `q² û_j` path is carried through every fixed
radial cutoff by the contractive restriction map.
-/
theorem h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path_hasDerivAt_of_global
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (W : H3FourierComplexL2)
    (hGlobal :
      HasDerivAt
        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j)
        W
        t) :
    HasDerivAt
      (h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
        hH3 hClass R j)
      (
        h3TerminalPhysicalTopDissipationRadialTailRestrictCLM R
          W
      )
      t := by

  change
    HasDerivAt
      (fun x : ℝ =>
        h3TerminalPhysicalTopDissipationRadialTailRestrictCLM R
          (
            h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass j x
          ))
      (
        h3TerminalPhysicalTopDissipationRadialTailRestrictCLM R
          W
      )
      t

  have h :=
    (
      h3TerminalPhysicalTopDissipationRadialTailRestrictCLM R
    ).hasFDerivAt.comp_hasDerivAt
      t
      hGlobal

  simpa only [Function.comp_def] using h

/-! ## One global weighted derivative differentiates every cutoff tail -/

/--
If the three global fourth-radial Fourier `L²` paths have strong derivatives
`W_j`, then every natural cutoff tail is differentiable.  The derivative is
the sum of the restricted real Hilbert pairings.

The cutoff appears only through a continuous linear restriction applied after
the global derivative.
-/
theorem h3TerminalPhysicalTopDissipationNaturalRadialTailPath_hasDerivAt_of_globalFourthRadialComponentL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (n : ℕ)
    (W : Fin 3 → H3FourierComplexL2)
    (hGlobal :
      ∀ j : Fin 3,
        HasDerivAt
          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j)
          (W j)
          t) :
    HasDerivAt
      (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
        hH3 hClass n)
      (
        ∑ j : Fin 3,
          2 *
            inner ℝ
              (
                h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
                  hH3 hClass ((n : ℝ) + 1) j t
              )
              (
                h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
                  ((n : ℝ) + 1)
                  (W j)
              )
      )
      t := by

  have hSum :
      HasDerivAt
        (fun s : ℝ =>
          ∑ j : Fin 3,
            ‖h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
                hH3 hClass ((n : ℝ) + 1) j s‖ ^ 2)
        (
          ∑ j : Fin 3,
            2 *
              inner ℝ
                (
                  h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
                    hH3 hClass ((n : ℝ) + 1) j t
                )
                (
                  h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
                    ((n : ℝ) + 1)
                    (W j)
                )
        )
        t := by

    exact
      HasDerivAt.fun_sum
        (u := (Finset.univ : Finset (Fin 3)))
        (fun j hj =>
          (
            h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path_hasDerivAt_of_global
              hH3
              hClass
              j
              (W j)
              (hGlobal j)
          ).norm_sq)

  rw [
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath_eq_sum_norm_sq_restricted
      hH3 hClass n
  ]

  exact
    hSum

/-! ## Global derivative + pairing identification closes the balance -/

/--
Cutoff-independent temporal datum: all three global `q² û_j` paths possess
strong Fourier `L²` derivatives at every strict preterminal time.
-/
def H3TerminalPhysicalTopDissipationGlobalFourthRadialHilbertDerivativeAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∀ t : ℝ,
    ∀ ht : t ∈ Set.Ioo a T,
      ∃ W : Fin 3 → H3FourierComplexL2,
        ∀ j : Fin 3,
          HasDerivAt
            (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass j)
            (W j)
            t

/--
Given global weighted derivatives, the remaining cutoff-dependent statement is
only the scalar pairing identification with the concrete PDE rates.
-/
def H3TerminalPhysicalTopDissipationGlobalFourthRadialHilbertPairingIdentifiesPDEAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∀ t : ℝ,
    ∀ ht : t ∈ Set.Ioo a T,
      ∀ W : Fin 3 → H3FourierComplexL2,
        (
          ∀ j : Fin 3,
            HasDerivAt
              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                hH3 hClass j)
              (W j)
              t
        )
          →
        ∀ n : ℕ,
          (
            ∑ j : Fin 3,
              2 *
                inner ℝ
                  (
                    h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
                      hH3 hClass ((n : ℝ) + 1) j t
                  )
                  (
                    h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
                      ((n : ℝ) + 1)
                      (W j)
                  )
          )
            =
          h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
              hH3 hClass ht ((n : ℝ) + 1)
            +
          h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
            hH3 hClass ht ((n : ℝ) + 1)

/--
The cutoff-independent global weighted derivative together with the remaining
scalar pairing identification implies the exact localized PDE balance.
-/
theorem naturalTopDissipationRadialTailLocalizedPDEBalanceAtEndpoint_of_globalFourthRadialHilbertDerivative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDerivative :
      H3TerminalPhysicalTopDissipationGlobalFourthRadialHilbertDerivativeAtEndpoint
        hH3 hClass)
    (hPairing :
      H3TerminalPhysicalTopDissipationGlobalFourthRadialHilbertPairingIdentifiesPDEAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint
      hH3 hClass := by

  intro n t ht

  obtain
    ⟨
      W,
      hGlobal
    ⟩ :=
    hDerivative t ht

  have hTail :=
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath_hasDerivAt_of_globalFourthRadialComponentL2
      hH3
      hClass
      n
      W
      hGlobal

  refine
    ⟨
      hTail.differentiableAt,
      ?_
    ⟩

  rw [
    hTail.deriv,
    hPairing t ht W hGlobal n
  ]

end

end Euclidean
end Bridge
end PrimeTensor
