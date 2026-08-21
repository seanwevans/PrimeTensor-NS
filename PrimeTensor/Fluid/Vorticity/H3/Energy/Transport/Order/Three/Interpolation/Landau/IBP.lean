import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Algebra

/-!
# Third-order H³ interpolation: Landau integration by parts

This file isolates the whole-space integration-by-parts identity behind the
Landau estimate used by the hard third-order transport block.

For scalar fields `v`, `g`, and `dg`, think of

    g  = ∂ₐ v,
    dg = ∂ₐ g.

The classical identity is

    ∫ g⁴ = -3 ∫ v g² dg,

after the boundary term from `∂ₐ (v g³)` vanishes.

As elsewhere in PrimeTensor, the whole-space boundary/decay fact and the
integrability needed by the Bochner integral are explicit analytic data.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

/-
Use the same product measure-space witness under which `spatialEnergyPairing`
and the green Hölder specialization were elaborated.
-/
noncomputable local instance axisFintypeH3LandauIBP
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3EnergyDerivative d

noncomputable local instance point3MeasureSpaceH3LandauIBP :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3EnergyDerivative Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
Whole-space one-coordinate integration by parts for the quartic Landau
estimate.

This equality packages the derivative/product-rule identification and the
vanishing boundary term.
-/
def LandauQuarticIntegrationByParts
    (v g dg : ScalarField3) : Prop :=
  (
    ∫ x : Point3,
      (g x) ^ 4
  )
    =
  -3 *
    (
      ∫ x : Point3,
        v x * ((g x) ^ 2 * dg x)
    )

/--
Pointwise first-derivative envelope for the scalar field playing the role of
`v` in the Landau identity.
-/
def LandauScalarEnvelope
    (v : ScalarField3)
    (h : ℝ) : Prop :=
  0 ≤ h
    ∧
  ∀ x : Point3,
    abs (v x) ≤ h

/--
Integrability data needed to compare the absolute cubic integrand with its
pointwise envelope majorant using the ordinary Bochner integral.
-/
def LandauQuarticEnvelopeIntegrable
    (v g dg : ScalarField3)
    (h : ℝ) : Prop :=
  MeasureTheory.Integrable
      (
        fun x : Point3 =>
          abs
            (
              v x * ((g x) ^ 2 * dg x)
            )
      )
    ∧
  MeasureTheory.Integrable
      (
        fun x : Point3 =>
          h * (abs (g x) ^ 2 * abs (dg x))
      )

/--
The integration-by-parts identity and the pointwise envelope reduce the
quartic integral to

    ∫ g⁴ ≤ 3 h ∫ |g|² |dg|.

No Cauchy--Schwarz estimate is used here.
-/
theorem landau_quartic_integral_le_envelope_integral
    {v g dg : ScalarField3}
    {h : ℝ}
    (
      hIBP :
        LandauQuarticIntegrationByParts
          v g dg
    )
    (
      hEnv :
        LandauScalarEnvelope
          v h
    )
    (
      hInt :
        LandauQuarticEnvelopeIntegrable
          v g dg h
    ) :
    (
      ∫ x : Point3,
        (g x) ^ 4
    )
      ≤
    3 * h *
      (
        ∫ x : Point3,
          abs (g x) ^ 2 * abs (dg x)
      ) := by

  rcases hEnv with
    ⟨hh, hPointwise⟩

  rcases hInt with
    ⟨hAbsIntegrable, hMajorantIntegrable⟩

  unfold LandauQuarticIntegrationByParts at hIBP

  have hAbsIntegral :
      abs
          (
            ∫ x : Point3,
              v x * ((g x) ^ 2 * dg x)
          )
        ≤
      ∫ x : Point3,
        abs
          (
            v x * ((g x) ^ 2 * dg x)
          ) := by

    simpa only [Real.norm_eq_abs] using
      (
        MeasureTheory.norm_integral_le_integral_norm
          (
            f :=
              fun x : Point3 =>
                v x * ((g x) ^ 2 * dg x)
          )
      )

  have hPointwiseAbs :
      ∀ x : Point3,
        abs
            (
              v x * ((g x) ^ 2 * dg x)
            )
          ≤
        h * (abs (g x) ^ 2 * abs (dg x)) := by

    intro x

    have hv :
        abs (v x) ≤ h :=
      hPointwise x

    have hnon :
        0 ≤ abs (g x) ^ 2 * abs (dg x) := by
      positivity

    calc
      abs
          (
            v x * ((g x) ^ 2 * dg x)
          )
          =
        abs (v x)
          *
        (abs (g x) ^ 2 * abs (dg x)) := by
            rw [abs_mul, abs_mul, abs_pow]
      _ ≤
        h * (abs (g x) ^ 2 * abs (dg x)) :=
          mul_le_mul_of_nonneg_right
            hv
            hnon

  have hIntegralMono :
      (
        ∫ x : Point3,
          abs
            (
              v x * ((g x) ^ 2 * dg x)
            )
      )
        ≤
      ∫ x : Point3,
        h * (abs (g x) ^ 2 * abs (dg x)) := by

    exact
      MeasureTheory.integral_mono
        hAbsIntegrable
        hMajorantIntegrable
        hPointwiseAbs

  have hPull :
      (
        ∫ x : Point3,
          h * (abs (g x) ^ 2 * abs (dg x))
      )
        =
      h *
        (
          ∫ x : Point3,
            abs (g x) ^ 2 * abs (dg x)
        ) := by

    exact
      MeasureTheory.integral_const_mul
        h
        (
          fun x : Point3 =>
            abs (g x) ^ 2 * abs (dg x)
        )

  have hAbsBound :
      abs
          (
            ∫ x : Point3,
              v x * ((g x) ^ 2 * dg x)
          )
        ≤
      h *
        (
          ∫ x : Point3,
            abs (g x) ^ 2 * abs (dg x)
        ) := by

    calc
      abs
          (
            ∫ x : Point3,
              v x * ((g x) ^ 2 * dg x)
          )
          ≤
        ∫ x : Point3,
          abs
            (
              v x * ((g x) ^ 2 * dg x)
            ) :=
        hAbsIntegral
      _ ≤
        ∫ x : Point3,
          h * (abs (g x) ^ 2 * abs (dg x)) :=
        hIntegralMono
      _ =
        h *
          (
            ∫ x : Point3,
              abs (g x) ^ 2 * abs (dg x)
          ) :=
        hPull

  have hNegIntegral :
      -
        (
          ∫ x : Point3,
            v x * ((g x) ^ 2 * dg x)
        )
        ≤
      h *
        (
          ∫ x : Point3,
            abs (g x) ^ 2 * abs (dg x)
        ) := by

    exact
      le_trans
        (
          neg_le_abs
            (
              ∫ x : Point3,
                v x * ((g x) ^ 2 * dg x)
            )
        )
        hAbsBound

  rw [hIBP]

  nlinarith

end Euclidean
end Bridge
end PrimeTensor
