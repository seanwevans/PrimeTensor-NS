import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Balance
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Hilbert differentiation of the canonical sharp top radial tail

The sharp top-order radial tail has already been realized as the sum of three
squared Fourier `L²` norms.  This file turns that static realization into the
exact temporal differentiation interface needed by the localized PDE balance.

For a fixed sharp cutoff `R`, package each coordinate as the ordinary
`H3FourierComplexL2` path

    Xⱼ,R(t) = 1_{|D| ≥ R} q² ûⱼ(t)

on the strict energy-class interval, extended by zero outside it.

The previously proved norm identity gives, globally as ordinary scalar paths,

    Tail₃(t,n+1) = Σⱼ ‖Xⱼ,n+1(t)‖².

Therefore any componentwise strong derivatives

    Xⱼ,n+1'(t) = Vⱼ

imply immediately, by `HasDerivAt.norm_sq` and finite summation,

    Tail₃'(t,n+1)
      =
    Σⱼ 2 ⟪Xⱼ,n+1(t), Vⱼ⟫_ℝ.

No differentiation under the frequency integral is needed.

Finally, if that summed Hilbert pairing is identified with the concrete
diffusion-plus-nonlinear-transfer scalar defined in the preceding PDE file,
then the exact localized PDE balance follows.

Thus the remaining evolution problem is genuinely vector-valued: construct the
strong derivative of each fixed-cutoff weighted Fourier `L²` path and identify
its Hilbert pairing with the already named PDE terms.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailHilbertDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Ordinary sharp-tail Hilbert paths -/

/--
One sharp weighted top-tail coordinate as an ordinary Fourier `L²` path.
Outside the strict energy-class interval the path is set to zero.
-/
noncomputable def h3TerminalPhysicalTopDissipationRadialTailComponentL2Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R : ℝ)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalTopDissipationRadialTailComponentL2At
      hH3 hClass ht R j
  else
    0

/--
At every strict energy-class time, the ordinary component path is exactly the
previously constructed sharp weighted `L²` state.
-/
@[simp]
theorem h3TerminalPhysicalTopDissipationRadialTailComponentL2Path_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationRadialTailComponentL2Path
        hH3 hClass R j t
      =
    h3TerminalPhysicalTopDissipationRadialTailComponentL2At
      hH3 hClass ht R j := by

  unfold
    h3TerminalPhysicalTopDissipationRadialTailComponentL2Path

  simp only [dif_pos ht]

/--
The sum of the three squared sharp weighted `L²` norms, viewed as an ordinary
real-valued path.
-/
noncomputable def h3TerminalPhysicalTopDissipationRadialTailHilbertEnergyPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R : ℝ)
    (t : ℝ) : ℝ :=
  ∑ j : Fin 3,
    ‖h3TerminalPhysicalTopDissipationRadialTailComponentL2Path
        hH3 hClass R j t‖ ^ 2

/-! ## Global scalar-path identification -/

/--
The canonical natural-cutoff scalar tail path is globally identical to the
sum-of-squared-norms Hilbert path at the same natural cutoff.

Both sides are zero outside `(a,T)`, so this is an equality of ordinary
functions on all of `ℝ`, not merely a pointwise interior identity.
-/
theorem h3TerminalPhysicalTopDissipationNaturalRadialTailPath_eq_hilbertEnergyPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (n : ℕ) :
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath
        hH3 hClass n
      =
    h3TerminalPhysicalTopDissipationRadialTailHilbertEnergyPath
      hH3 hClass ((n : ℝ) + 1) := by

  funext t

  by_cases ht :
      t ∈ Set.Ioo a T

  · rw [
      h3TerminalPhysicalTopDissipationNaturalRadialTailPath_eq
        hH3 hClass n ht,
      h3TerminalPhysicalTopDissipationRadialTailMassAt_eq_sum_norm_sq_tailL2
        hH3 hClass ht ((n : ℝ) + 1)
    ]

    unfold
      h3TerminalPhysicalTopDissipationRadialTailHilbertEnergyPath

    apply Finset.sum_congr rfl

    intro j hj

    rw [
      h3TerminalPhysicalTopDissipationRadialTailComponentL2Path_eq
        hH3 hClass ht j
    ]

    rfl

  · unfold
      h3TerminalPhysicalTopDissipationNaturalRadialTailPath
      h3TerminalPhysicalTopDissipationRadialTailHilbertEnergyPath
      h3TerminalPhysicalTopDissipationRadialTailComponentL2Path

    simp [ht]

/-! ## Differentiate the sharp tail from componentwise Hilbert derivatives -/

/--
Componentwise strong Fourier `L²` derivatives differentiate the canonical
natural sharp-tail scalar path.

The derivative is the sum of the three real Hilbert norm-square pairings.
-/
theorem h3TerminalPhysicalTopDissipationNaturalRadialTailPath_hasDerivAt_of_componentL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (n : ℕ)
    (V : Fin 3 → H3FourierComplexL2)
    (hComponent :
      ∀ j : Fin 3,
        HasDerivAt
          (h3TerminalPhysicalTopDissipationRadialTailComponentL2Path
            hH3 hClass ((n : ℝ) + 1) j)
          (V j)
          t) :
    HasDerivAt
      (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
        hH3 hClass n)
      (
        ∑ j : Fin 3,
          2 *
            inner ℝ
              (h3TerminalPhysicalTopDissipationRadialTailComponentL2Path
                hH3 hClass ((n : ℝ) + 1) j t)
              (V j)
      )
      t := by

  have hSum :
      HasDerivAt
        (fun s : ℝ =>
          ∑ j : Fin 3,
            ‖h3TerminalPhysicalTopDissipationRadialTailComponentL2Path
                hH3 hClass ((n : ℝ) + 1) j s‖ ^ 2)
        (
          ∑ j : Fin 3,
            2 *
              inner ℝ
                (h3TerminalPhysicalTopDissipationRadialTailComponentL2Path
                  hH3 hClass ((n : ℝ) + 1) j t)
                (V j)
        )
        t := by

    exact
      HasDerivAt.fun_sum
        (u := (Finset.univ : Finset (Fin 3)))
        (fun j hj =>
          (hComponent j).norm_sq)

  rw [
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath_eq_hilbertEnergyPath
      hH3 hClass n
  ]

  change
    HasDerivAt
      (fun s : ℝ =>
        ∑ j : Fin 3,
          ‖h3TerminalPhysicalTopDissipationRadialTailComponentL2Path
              hH3 hClass ((n : ℝ) + 1) j s‖ ^ 2)
      (
        ∑ j : Fin 3,
          2 *
            inner ℝ
              (h3TerminalPhysicalTopDissipationRadialTailComponentL2Path
                hH3 hClass ((n : ℝ) + 1) j t)
              (V j)
      )
      t

  exact hSum

/--
Interior version of the preceding theorem, with the value in the derivative
pairing written directly as the strict-time sharp-tail state.
-/
theorem h3TerminalPhysicalTopDissipationNaturalRadialTailPath_hasDerivAt_of_componentL2_at
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (n : ℕ)
    (ht : t ∈ Set.Ioo a T)
    (V : Fin 3 → H3FourierComplexL2)
    (hComponent :
      ∀ j : Fin 3,
        HasDerivAt
          (h3TerminalPhysicalTopDissipationRadialTailComponentL2Path
            hH3 hClass ((n : ℝ) + 1) j)
          (V j)
          t) :
    HasDerivAt
      (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
        hH3 hClass n)
      (
        ∑ j : Fin 3,
          2 *
            inner ℝ
              (h3TerminalPhysicalTopDissipationRadialTailComponentL2At
                hH3 hClass ht ((n : ℝ) + 1) j)
              (V j)
      )
      t := by

  have h :=
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath_hasDerivAt_of_componentL2
      hH3 hClass n V hComponent

  simpa only [
    h3TerminalPhysicalTopDissipationRadialTailComponentL2Path_eq
      hH3 hClass ht
  ] using
    h

/--
Ordinary `deriv` form of the componentwise Hilbert differentiation theorem.
-/
theorem deriv_h3TerminalPhysicalTopDissipationNaturalRadialTailPath_eq_sum_inner_of_componentL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (n : ℕ)
    (ht : t ∈ Set.Ioo a T)
    (V : Fin 3 → H3FourierComplexL2)
    (hComponent :
      ∀ j : Fin 3,
        HasDerivAt
          (h3TerminalPhysicalTopDissipationRadialTailComponentL2Path
            hH3 hClass ((n : ℝ) + 1) j)
          (V j)
          t) :
    deriv
        (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
          hH3 hClass n)
        t
      =
    ∑ j : Fin 3,
      2 *
        inner ℝ
          (h3TerminalPhysicalTopDissipationRadialTailComponentL2At
            hH3 hClass ht ((n : ℝ) + 1) j)
          (V j) := by

  exact
    (
      h3TerminalPhysicalTopDissipationNaturalRadialTailPath_hasDerivAt_of_componentL2_at
        hH3 hClass n ht V hComponent
    ).deriv

/-! ## Hilbert evolution datum implies the exact localized PDE balance -/

/--
Concrete Hilbert-space form of the remaining localized evolution identity.

For every natural cutoff and strict preterminal time there is a three-component
Fourier `L²` derivative vector such that

1. each sharp weighted tail coordinate has that strong derivative; and
2. the resulting norm-square pairing is exactly the already named
   diffusion-plus-nonlinear-transfer scalar.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailHilbertPDEDerivativeAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∀ n : ℕ,
    ∀ t : ℝ,
      ∀ ht : t ∈ Set.Ioo a T,
        ∃ V : Fin 3 → H3FourierComplexL2,
          (
            ∀ j : Fin 3,
              HasDerivAt
                (h3TerminalPhysicalTopDissipationRadialTailComponentL2Path
                  hH3 hClass ((n : ℝ) + 1) j)
                (V j)
                t
          )
            ∧
          (
            ∑ j : Fin 3,
              2 *
                inner ℝ
                  (h3TerminalPhysicalTopDissipationRadialTailComponentL2At
                    hH3 hClass ht ((n : ℝ) + 1) j)
                  (V j)
          )
            =
          h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
              hH3 hClass ht ((n : ℝ) + 1)
            +
          h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
            hH3 hClass ht ((n : ℝ) + 1)

/--
The Hilbert-space component evolution datum is sufficient for the exact
localized sharp-tail PDE balance.
-/
theorem naturalTopDissipationRadialTailLocalizedPDEBalanceAtEndpoint_of_hilbertPDEDerivative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hHilbert :
      H3TerminalPhysicalTopDissipationNaturalRadialTailHilbertPDEDerivativeAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint
      hH3 hClass := by

  intro n t ht

  obtain
    ⟨
      V,
      hComponent,
      hPairing
    ⟩ :=
    hHilbert n t ht

  have hDerivative :=
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath_hasDerivAt_of_componentL2_at
      hH3 hClass n ht V hComponent

  refine
    ⟨
      hDerivative.differentiableAt,
      ?_
    ⟩

  rw [
    hDerivative.deriv,
    hPairing
  ]

end

end Euclidean
end Bridge
end PrimeTensor
