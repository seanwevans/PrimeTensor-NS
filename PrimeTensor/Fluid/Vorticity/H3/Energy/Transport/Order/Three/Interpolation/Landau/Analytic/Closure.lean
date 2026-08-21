import PrimeTensor.Bridge.Euclidean.Partials.Mixed
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.One.Bound
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Energy.Bookkeeping
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.L2.Bridge

/-!
# Landau analytic data: remove redundant envelope nonnegativity

`H3OrderThreeInterpolationLandauAnalyticDataAt` historically stores both

    0 ≤ h t

and

    VelocityGradientEnvelope u h t.

The first field is redundant.  A gradient envelope bounds the absolute value
of every first derivative by `h t`; since an absolute value is nonnegative,
the existence of even one such derivative immediately implies `0 ≤ h t`.

This file introduces the narrower core analytic package and reconstructs the
older package when downstream lemmas still expect it.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped ENNReal

noncomputable local instance axisFintypeH3LandauAnalyticClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3LandauAnalyticClosure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3LandauAnalyticClosure Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
The remaining quartic membership datum.

For measurable real-valued `g`, this is equivalent to `g ∈ L⁴`.  Keeping it
named separately makes the remaining analytic frontier explicit instead of
hiding it inside `LandauCauchyMemLp`.
-/
def LandauQuarticSquareMemLp
    (g : ScalarField3) : Prop :=
  MeasureTheory.MemLp
    (fun x : Point3 => abs (g x) ^ 2)
    (ENNReal.ofReal 2)
    volume

/--
For a spatially `C¹` scalar field on `Point3`, square-integrability of all
three coordinate partials implies square-integrability of the full Fréchet
derivative.

Pointwise we use
`SpatialC1.norm_fderiv_le_sum_abs_partialDeriv`; the finite sum of the three
absolute coordinate partials remains in `L²`.
-/
theorem SpatialC1.fderiv_memLp_two_of_partials
    {g : ScalarField3}
    (hC1 : SpatialC1 g)
    (
      hPartials :
        ∀ i : Axis Depth.three,
          MeasureTheory.MemLp
            (spatial3.d i g)
            (ENNReal.ofReal 2)
            volume
    ) :
    MeasureTheory.MemLp
      (fun x : Point3 => fderiv ℝ g x)
      (ENNReal.ofReal 2)
      volume := by

  have hAbsPartial :
      ∀ i : Axis Depth.three,
        MeasureTheory.MemLp
          (fun x : Point3 =>
            abs ((spatial3.d i g) x))
          (ENNReal.ofReal 2)
          volume := by

    intro i

    simpa [Real.norm_eq_abs] using
      (hPartials i).norm

  have hSum :
      MeasureTheory.MemLp
        (
          fun x : Point3 =>
            ∑ i : Axis Depth.three,
              abs ((spatial3.d i g) x)
        )
        (ENNReal.ofReal 2)
        volume := by

    exact
      MeasureTheory.memLp_finsetSum
        Finset.univ
        (fun i hi =>
          hAbsPartial i)

  have hFDerivMeas :
      MeasureTheory.AEStronglyMeasurable
        (fun x : Point3 => fderiv ℝ g x)
        volume :=
    (
      hC1.continuous_fderiv
        (by norm_num)
    ).aestronglyMeasurable

  apply
    hSum.mono
      hFDerivMeas

  filter_upwards with x

  have hBound :
      ‖fderiv ℝ g x‖
        ≤
      ∑ i : Axis Depth.three,
        abs ((spatial3.d i g) x) := by

    simpa [spatial3, spatial] using
      hC1.norm_fderiv_le_sum_abs_partialDeriv
        x

  have hSumNonneg :
      0
        ≤
      ∑ i : Axis Depth.three,
        abs ((spatial3.d i g) x) := by

    exact
      Finset.sum_nonneg
        (fun i hi =>
          abs_nonneg ((spatial3.d i g) x))

  simpa [
    Real.norm_eq_abs,
    abs_of_nonneg hSumNonneg
  ] using
    hBound

/--
The Fréchet-native whole-space Sobolev endpoint.

This is the form matching Mathlib's compact-support Sobolev inequality:
`g` is spatially `C¹`, `g ∈ L²`, and its full Fréchet derivative is in `L²`.
The only remaining theorem is the classical removal of compact support.
-/
def WholeSpaceC1FDerivL2ToL6 : Prop :=
  ∀ g : ScalarField3,
    SpatialC1 g
      →
    MeasureTheory.MemLp
        g
        (ENNReal.ofReal 2)
        volume
      →
    MeasureTheory.MemLp
        (fun x : Point3 => fderiv ℝ g x)
        (ENNReal.ofReal 2)
        volume
      →
    MeasureTheory.MemLp
      g
      (ENNReal.ofReal 6)
      volume

/--
The standard three-dimensional whole-space Sobolev endpoint frontier needed
by this proof.

Only spatially `C¹` functions are required here, because every second
velocity derivative in the H³ application already has that regularity. This
is the concrete PrimeTensor form of the `C¹ ∩ H¹(ℝ³) → L⁶(ℝ³)` endpoint.  It is the
endpoint that matches the compact-support Gagliardo--Nirenberg--Sobolev theorem
already available in Mathlib.  The remaining library work is the classical
whole-space extension from compactly supported smooth functions.
-/
def WholeSpaceC1H1ToL6 : Prop :=
  ∀ g : ScalarField3,
    SpatialC1 g
      →
    MeasureTheory.MemLp
        g
        (ENNReal.ofReal 2)
        volume
      →
    (
      ∀ i : Axis Depth.three,
        MeasureTheory.MemLp
          (spatial3.d i g)
          (ENNReal.ofReal 2)
          volume
    )
      →
    MeasureTheory.MemLp
      g
      (ENNReal.ofReal 6)
      volume


/--
The Fréchet-native endpoint discharges the coordinatewise H¹ interface used by
the H³ reconstruction.
-/
theorem wholeSpaceC1H1ToL6_of_fderiv
    (
      hSobolev :
        WholeSpaceC1FDerivL2ToL6
    ) :
    WholeSpaceC1H1ToL6 := by

  intro g hC1 hg2 hPartials

  exact
    hSobolev
      g
      hC1
      hg2
      (
        hC1.fderiv_memLp_two_of_partials
          hPartials
      )

/--
Derived non-endpoint `C¹` interface retained for the Landau reconstruction layer.
It is discharged from `WholeSpaceC1H1ToL6` by
`wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6`.
-/
def WholeSpaceC1H1ToL4 : Prop :=
  ∀ g : ScalarField3,
    SpatialC1 g
      →
    MeasureTheory.MemLp
        g
        (ENNReal.ofReal 2)
        volume
      →
    (
      ∀ i : Axis Depth.three,
        MeasureTheory.MemLp
          (spatial3.d i g)
          (ENNReal.ofReal 2)
          volume
    )
      →
    MeasureTheory.MemLp
      g
      (ENNReal.ofReal 4)
      volume

/--
The `L⁴` membership used by the Landau estimate is not an independent
whole-space frontier.  It follows from the Sobolev endpoint `L⁶` together with
the already available `L²` datum:

    ∫ ‖g‖⁴ = ∫ ‖g‖³ · ‖g‖

and Hölder with exponents `2` and `2`.
-/
theorem wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6
    (
      hSobolev6 :
        WholeSpaceC1H1ToL6
    ) :
    WholeSpaceC1H1ToL4 := by

  intro g hC1 hg2 hdg2

  have hMeas :
      MeasureTheory.AEStronglyMeasurable
        g
        volume :=
    hC1.continuous.aestronglyMeasurable

  have hg6 :
      MeasureTheory.MemLp
        g
        (ENNReal.ofReal 6)
        volume :=
    hSobolev6
      g
      hC1
      hg2
      hdg2

  have hSixDivThree :
      (ENNReal.ofReal 6) / (ENNReal.ofReal 3)
        =
      ENNReal.ofReal 2 := by

    have hThree_ne_zero :
        ENNReal.ofReal 3 ≠ 0 := by
      norm_num

    have hThree_ne_top :
        ENNReal.ofReal 3 ≠ ⊤ := by
      simp

    symm

    apply
      (
        ENNReal.eq_div_iff
          hThree_ne_zero
          hThree_ne_top
      ).2

    norm_num

  have hCube2 :
      MeasureTheory.MemLp
        (fun x : Point3 => ‖g x‖ ^ 3)
        (ENNReal.ofReal 2)
        volume := by

    have hCube :=
      hg6.norm_rpow_div
        (ENNReal.ofReal 3)

    rw [hSixDivThree] at hCube

    simpa using
      hCube

  have hNorm2_ofReal :
      MeasureTheory.MemLp
        (fun x : Point3 => ‖g x‖)
        (ENNReal.ofReal 2)
        volume :=
    hg2.norm

  have hCube2_literal :
      MeasureTheory.MemLp
        (fun x : Point3 => ‖g x‖ ^ 3)
        (2 : ENNReal)
        volume := by
    simpa using
      hCube2

  have hNorm2 :
      MeasureTheory.MemLp
        (fun x : Point3 => ‖g x‖)
        (2 : ENNReal)
        volume := by
    simpa using
      hNorm2_ofReal

  have hFourth1 :
      MeasureTheory.MemLp
        (fun x : Point3 => ‖g x‖ ^ 4)
        (1 : ENNReal)
        volume := by

    have hProd :
        MeasureTheory.MemLp
          (fun x : Point3 =>
            (‖g x‖ ^ 3) * ‖g x‖)
          (1 : ENNReal)
          volume :=
      hNorm2.mul' hCube2_literal

    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      hProd

  apply
    (
      MeasureTheory.memLp_norm_rpow_iff
        (p := ENNReal.ofReal 4)
        (q := ENNReal.ofReal 4)
        hMeas
        (by norm_num)
        (by simp)
    ).1

  have hFourDivFour :
      (ENNReal.ofReal 4) / (ENNReal.ofReal 4)
        =
      (1 : ENNReal) := by

    have hFour_ne_zero :
        ENNReal.ofReal 4 ≠ 0 := by
      norm_num

    have hFour_ne_top :
        ENNReal.ofReal 4 ≠ ⊤ := by
      simp

    symm

    apply
      (
        ENNReal.eq_div_iff
          hFour_ne_zero
          hFour_ne_top
      ).2

    norm_num

  rw [hFourDivFour]

  simpa using
    hFourth1

/--
The standard whole-space quartic derivative integration-by-parts frontier.

For a bounded `C¹` scalar field `v` whose coordinate derivative
`g = ∂ₐ v` is `C¹ ∩ L⁴` and whose repeated derivative `∂ₐ g` lies in `L²`,
the classical whole-space identity is

    ∫ g⁴ = -3 ∫ v g² (∂ₐ g).

The pointwise envelope supplies the boundedness needed to kill the cutoff
boundary term.  This statement is deliberately independent of Navier--Stokes:
the remaining work is the ordinary whole-space cutoff/integration-by-parts
argument.
-/
def WholeSpaceQuarticDerivativeIntegrationByParts : Prop :=
  ∀
    (v : ScalarField3)
    (a : Axis Depth.three)
    (h : ℝ),
      SpatialC1 v
        →
      SpatialC1 (spatial3.d a v)
        →
      LandauScalarEnvelope v h
        →
      MeasureTheory.MemLp
          (spatial3.d a v)
          (ENNReal.ofReal 4)
          volume
        →
      MeasureTheory.MemLp
          (spatial3.d a (spatial3.d a v))
          (ENNReal.ofReal 2)
          volume
        →
      LandauQuarticIntegrationByParts
        v
        (spatial3.d a v)
        (spatial3.d a (spatial3.d a v))

/--
The genuinely Landau-specific derivative control.

This tuple-local core now contains only the quartic integration-by-parts
identity.  The second-derivative quartic membership frontier is centralized
once at the H³ order level, while canonical H³ data reconstructs the
third-derivative `L²` datum.
-/
def LandauDerivativeCoreControl
    (v g dg : ScalarField3) : Prop :=
  LandauQuarticIntegrationByParts
    v g dg

/--
For a measurable real field, the quartic-square representation is exactly the
legacy `L⁴` membership needed downstream.
-/
theorem memLp_four_of_landauQuarticSquareMemLp_of_measurable
    {g : ScalarField3}
    (
      hMeas :
        AEStronglyMeasurable
          g
          volume
    )
    (
      hSquare :
        LandauQuarticSquareMemLp
          g
    ) :
    MeasureTheory.MemLp
      g
      (ENNReal.ofReal 4)
      volume := by

  apply
    (
      MeasureTheory.memLp_norm_rpow_iff
        (p := ENNReal.ofReal 4)
        (q := ENNReal.ofReal 2)
        hMeas
        (by norm_num)
        (by simp)
    ).1

  have hFourDivTwo :
      (ENNReal.ofReal 4) / (ENNReal.ofReal 2)
        =
      ENNReal.ofReal 2 := by

    have hTwo_ne_zero :
        ENNReal.ofReal 2 ≠ 0 := by
      norm_num

    have hTwo_ne_top :
        ENNReal.ofReal 2 ≠ ⊤ := by
      simp

    symm

    apply
      (
        ENNReal.eq_div_iff
          hTwo_ne_zero
          hTwo_ne_top
      ).2

    norm_num

  rw [hFourDivTwo]

  simpa [LandauQuarticSquareMemLp, sq_abs] using
    hSquare

/--
The explicit whole-space envelope-integrability package is redundant once the
Landau scalar envelope and Cauchy `L²` data are available.

The Cauchy package gives `|g|² ∈ L²` and `|dg| ∈ L²`, so Hölder gives
`|g|² |dg| ∈ L¹`. Multiplication by the scalar envelope constant preserves
integrability, and the pointwise bound `|v| ≤ h` dominates the absolute cubic
Landau integrand.
-/
theorem landauQuarticEnvelopeIntegrable_of_cauchy_of_envelope_of_measurable
    {v g dg : ScalarField3}
    {h : ℝ}
    (
      hVMeas :
        AEStronglyMeasurable
          v
          volume
    )
    (
      hEnv :
        LandauScalarEnvelope
          v h
    )
    (
      hCauchy :
        LandauCauchyMemLp
          g dg
    ) :
    LandauQuarticEnvelopeIntegrable
      v g dg h := by

  have hg2 :
      MemLp
        (fun x : Point3 => abs (g x) ^ 2)
        (2 : ENNReal)
        volume := by
    simpa using hCauchy.1

  have hdg2 :
      MemLp
        (fun x : Point3 => abs (dg x))
        (2 : ENNReal)
        volume := by
    simpa using hCauchy.2

  have hProdLp :
      MemLp
        (
          fun x : Point3 =>
            abs (g x) ^ 2
              *
            abs (dg x)
        )
        (1 : ENNReal)
        volume := by
    exact
      hdg2.mul'
        hg2

  have hProdInt :
      Integrable
        (
          fun x : Point3 =>
            abs (g x) ^ 2
              *
            abs (dg x)
        )
        volume :=
    memLp_one_iff_integrable.mp
      hProdLp

  have hMajorantInt :
      Integrable
        (
          fun x : Point3 =>
            h
              *
            (
              abs (g x) ^ 2
                *
              abs (dg x)
            )
        )
        volume :=
    hProdInt.const_mul h

  have hAbsMeas :
      AEStronglyMeasurable
        (
          fun x : Point3 =>
            abs
              (
                v x
                  *
                (
                  (g x) ^ 2
                    *
                  dg x
                )
              )
        )
        volume := by

    have hMeas :
        AEStronglyMeasurable
          (
            fun x : Point3 =>
              ‖v x‖
                *
              (
                abs (g x) ^ 2
                  *
                abs (dg x)
              )
          )
          volume :=
      hVMeas.norm.mul
        hProdInt.aestronglyMeasurable

    simpa [Real.norm_eq_abs, abs_mul, abs_pow, mul_assoc] using
      hMeas

  have hPointwise :
      ∀ x : Point3,
        norm
          (
            abs
              (
                v x
                  *
                (
                  (g x) ^ 2
                    *
                  dg x
                )
              )
          )
          ≤
        h
          *
        (
          abs (g x) ^ 2
            *
          abs (dg x)
        ) := by

    intro x

    have hv :
        abs (v x) ≤ h :=
      hEnv.2 x

    have hnon :
        0
          ≤
        abs (g x) ^ 2
          *
        abs (dg x) := by
      positivity

    have hmul :
        abs (v x)
            *
          (
            abs (g x) ^ 2
              *
            abs (dg x)
          )
          ≤
        h
            *
          (
            abs (g x) ^ 2
              *
            abs (dg x)
          ) :=
      mul_le_mul_of_nonneg_right
        hv
        hnon

    simpa [
      Real.norm_eq_abs,
      abs_mul,
      abs_pow,
      mul_assoc
    ] using hmul

  have hAbsInt :
      Integrable
        (
          fun x : Point3 =>
            abs
              (
                v x
                  *
                (
                  (g x) ^ 2
                    *
                  dg x
                )
              )
        )
        volume :=
    hMajorantInt.mono'
      hAbsMeas
      (
        Filter.Eventually.of_forall
          hPointwise
      )

  exact
    ⟨
      hAbsInt,
      hMajorantInt
    ⟩

/--
For measurable `v` and `g`, the narrower core control reconstructs the legacy
`LandauDerivativeControl`. The `L⁴` field comes from Cauchy plus measurability;
the explicit envelope-integrability field comes from Cauchy plus the scalar
envelope.
-/
theorem landauDerivativeControl_of_core_of_measurable
    {v g dg : ScalarField3}
    {h : ℝ}
    (
      hVMeas :
        AEStronglyMeasurable
          v
          volume
    )
    (
      hGMeas :
        AEStronglyMeasurable
          g
          volume
    )
    (
      hEnv :
        LandauScalarEnvelope
          v h
    )
    (
      hDg2 :
        MeasureTheory.MemLp
          dg
          (ENNReal.ofReal 2)
          volume
    )
    (
      hgSquare2 :
        LandauQuarticSquareMemLp
          g
    )
    (
      hCore :
        LandauDerivativeCoreControl
          v g dg
    ) :
    LandauDerivativeControl
      v g dg h := by

  have hIBP :
      LandauQuarticIntegrationByParts
        v g dg :=
    hCore

  have hDgAbs2 :
      MeasureTheory.MemLp
        (fun x : Point3 => abs (dg x))
        (ENNReal.ofReal 2)
        volume := by
    simpa [Real.norm_eq_abs] using
      hDg2.norm

  have hCauchy :
      LandauCauchyMemLp
        g dg :=
    ⟨
      hgSquare2,
      hDgAbs2
    ⟩

  have hInt :
      LandauQuarticEnvelopeIntegrable
        v g dg h :=
    landauQuarticEnvelopeIntegrable_of_cauchy_of_envelope_of_measurable
      hVMeas
      hEnv
      hCauchy

  have hg4 :
      MeasureTheory.MemLp
        g
        (ENNReal.ofReal 4)
        volume :=
    memLp_four_of_landauQuarticSquareMemLp_of_measurable
      hGMeas
      hgSquare2

  exact
    ⟨
      hg4,
      hIBP,
      hInt,
      hCauchy
    ⟩

/--
The single H³-level quartic frontier.

Instead of storing the same `L⁴` information repeatedly inside every Landau
tuple, record it once for every second velocity derivative.  Under the
measurability supplied by the energy class, each field below is equivalent to
the corresponding second derivative belonging to `L⁴`.
-/
def H3SecondDerivativeQuarticSquareMemLpAt
    (
      u :
        SpaceTimeVectorField
          ℝ ℝ MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  ∀ j m n : Axis Depth.three,
    LandauQuarticSquareMemLp
      (
        spatial3.d m
          (
            spatial3.d n
              (loggedVelocityComponent u t j)
          )
      )

/--
The genuinely Landau-specific data for one interpolation tuple.

The tuple core itself is envelope-independent and quartic-membership-
independent: every field below is now only a quartic IBP identity.  The
second-derivative `L⁴` frontier is centralized once by
`H3SecondDerivativeQuarticSquareMemLpAt`; canonical H³ data supplies the
third-derivative `L²` terms.
-/
structure H3InterpolationTupleLandauCoreAnalyticData
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (i k l j r : Axis Depth.three) : Prop where

  g1_control :
    LandauDerivativeCoreControl
      (
        spatial3.d l
          (loggedVelocityComponent u t r)
      )
      (
        spatial3.d k
          (
            spatial3.d l
              (loggedVelocityComponent u t r)
          )
      )
      (
        spatial3.d k
          (
            spatial3.d k
              (
                spatial3.d l
                  (loggedVelocityComponent u t r)
              )
          )
      )

  q1_control :
    LandauDerivativeCoreControl
      (
        spatial3.d r
          (loggedVelocityComponent u t j)
      )
      (
        spatial3.d i
          (
            spatial3.d r
              (loggedVelocityComponent u t j)
          )
      )
      (
        spatial3.d i
          (
            spatial3.d i
              (
                spatial3.d r
                  (loggedVelocityComponent u t j)
              )
          )
      )

  g2_control :
    LandauDerivativeCoreControl
      (
        spatial3.d l
          (loggedVelocityComponent u t r)
      )
      (
        spatial3.d i
          (
            spatial3.d l
              (loggedVelocityComponent u t r)
          )
      )
      (
        spatial3.d i
          (
            spatial3.d i
              (
                spatial3.d l
                  (loggedVelocityComponent u t r)
              )
          )
      )

  q2_control :
    LandauDerivativeCoreControl
      (
        spatial3.d r
          (loggedVelocityComponent u t j)
      )
      (
        spatial3.d k
          (
            spatial3.d r
              (loggedVelocityComponent u t j)
          )
      )
      (
        spatial3.d k
          (
            spatial3.d k
              (
                spatial3.d r
                  (loggedVelocityComponent u t j)
              )
          )
      )

  g3_control :
    LandauDerivativeCoreControl
      (
        spatial3.d k
          (loggedVelocityComponent u t r)
      )
      (
        spatial3.d i
          (
            spatial3.d k
              (loggedVelocityComponent u t r)
          )
      )
      (
        spatial3.d i
          (
            spatial3.d i
              (
                spatial3.d k
                  (loggedVelocityComponent u t r)
              )
          )
      )

  q3_control :
    LandauDerivativeCoreControl
      (
        spatial3.d l
          (loggedVelocityComponent u t j)
      )
      (
        spatial3.d r
          (
            spatial3.d l
              (loggedVelocityComponent u t j)
          )
      )
      (
        spatial3.d r
          (
            spatial3.d r
              (
                spatial3.d l
                  (loggedVelocityComponent u t j)
              )
          )
      )

/--
Every first velocity derivative occurring as an envelope factor in a Landau
tuple is spatially `C¹` on the strict tail.
-/
private theorem h3FirstDerivative_spatialC1
    {
      u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three
    }
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      j i :
        Axis Depth.three
    ) :
    SpatialC1
      (
        spatial3.d i
          (loggedVelocityComponent u t j)
      ) := by

  rcases hClass.pressure_witness with
    ⟨p, s, hp4⟩

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans
        hClass.terminal_start.1
        ht.1,
      ht.2
    ⟩

  change
    SpatialC1
      (
        spatial3.d i
          (
            fun x =>
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u t x
              ).component j
          )
      )

  exact
    s.velocity_firstPartial_spatialC1
      htNS j i

/--
Every first velocity derivative occurring as an envelope factor in a Landau
tuple is strongly measurable on the strict tail.
-/
private theorem h3FirstDerivative_aestronglyMeasurable
    {
      u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three
    }
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      j i :
        Axis Depth.three
    ) :
    AEStronglyMeasurable
      (
        spatial3.d i
          (loggedVelocityComponent u t j)
      )
      volume := by

  exact
    (
      h3FirstDerivative_spatialC1
        hClass ht j i
    ).continuous.aestronglyMeasurable

/--
Every second velocity derivative occurring in a Landau tuple is spatially
`C¹` on the strict tail.
-/
private theorem h3SecondDerivative_spatialC1
    {
      u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three
    }
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      j m n :
        Axis Depth.three
    ) :
    SpatialC1
      (
        spatial3.d m
          (
            spatial3.d n
              (loggedVelocityComponent u t j)
          )
      ) := by

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨
      le_of_lt ht.1,
      ht.2
    ⟩

  have hC3 :
      SpatialC3
        (
          spatial3.d m
            (
              spatial3.d n
                (loggedVelocityComponent u t j)
            )
        ) := by

    change
      SpatialC3
        (
          spatial3.d m
            (
              spatial3.d n
                (
                  fun x =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t x
                    ).component j
                )
            )
        )

    exact
      hClass.velocity_spatial_five
        t htTail j m n

  unfold SpatialC3 at hC3
  unfold SpatialC1

  exact
    hC3.of_le
      (by norm_num)

/--
Every second velocity derivative occurring in a Landau tuple is strongly
measurable on the tail, by the spatial regularity already stored in the
preterminal H³ energy class.
-/
private theorem h3SecondDerivative_aestronglyMeasurable
    {
      u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three
    }
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      j m n :
        Axis Depth.three
    ) :
    AEStronglyMeasurable
      (
        spatial3.d m
          (
            spatial3.d n
              (loggedVelocityComponent u t j)
          )
      )
      volume := by

  exact
    (
      h3SecondDerivative_spatialC1
        hClass ht j m n
    ).continuous.aestronglyMeasurable

/--
Canonical H³ data reconstructs `L²` membership for every measurable second
velocity derivative on the strict tail.
-/
private theorem h3SecondDerivative_memLp2
    {
      u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three
    }
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (
      j m n :
        Axis Depth.three
    ) :
    MeasureTheory.MemLp
      (
        spatial3.d m
          (
            spatial3.d n
              (loggedVelocityComponent u t j)
          )
      )
      (ENNReal.ofReal 2)
      volume := by

  exact
    memLp_two_of_spatialL2SquareIntegrable
      (
        h3SecondDerivative_aestronglyMeasurable
          hClass ht j m n
      )
      (
        (hH3 j).2.2.1 m n
      )

/--
Canonical H³ data reconstructs `L²` membership for every measurable third
velocity derivative on the strict tail.
-/
private theorem h3ThirdDerivative_memLp2
    {
      u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three
    }
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (
      j i k l :
        Axis Depth.three
    ) :
    MeasureTheory.MemLp
      (
        spatial3.d i
          (
            spatial3.d k
              (
                spatial3.d l
                  (loggedVelocityComponent u t j)
              )
          )
      )
      (ENNReal.ofReal 2)
      volume := by

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨
      le_of_lt ht.1,
      ht.2
    ⟩

  have hBaseC3 :
      SpatialC3
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t j)
            )
        ) := by

    change
      SpatialC3
        (
          spatial3.d k
            (
              spatial3.d l
                (
                  fun x =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t x
                    ).component j
                )
            )
        )

    exact
      hClass.velocity_spatial_five
        t htTail j k l

  have hThirdC2 :
      SpatialC2
        (
          spatial3.d i
            (
              spatial3.d k
                (
                  spatial3.d l
                    (loggedVelocityComponent u t j)
                )
            )
        ) := by

    change
      SpatialC2
        (
          fun q =>
            partialDeriv
              i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t j)
                  )
              )
              q
        )

    exact
      PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
        hBaseC3 i

  have hMeas :
      MeasureTheory.AEStronglyMeasurable
        (
          spatial3.d i
            (
              spatial3.d k
                (
                  spatial3.d l
                    (loggedVelocityComponent u t j)
                )
            )
        )
        volume := by

    unfold SpatialC2 at hThirdC2

    exact
      hThirdC2.continuous.aestronglyMeasurable

  exact
    velocityH3IntegrableAt_third_memLp2
      hH3
      j i k l
      hMeas

/--
The generic whole-space `H¹ → L⁴` theorem discharges the entire centralized
second-derivative quartic frontier from canonical H³ data.

For each second derivative `g = D_m D_n u_j`, canonical H³ gives `g ∈ L²` and
every coordinate derivative `D_i g ∈ L²`; energy-class regularity supplies
measurability.  `WholeSpaceC1H1ToL4` then yields `g ∈ L⁴`, which is converted to
the legacy square-in-`L²` representation.
-/
theorem h3SecondDerivativeQuarticSquareMemLpAt_of_wholeSpaceH1ToL4
    {
      u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three
    }
    {a T t : ℝ}
    (
      hSobolev :
        WholeSpaceC1H1ToL4
    )
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    ) :
    H3SecondDerivativeQuarticSquareMemLpAt
      u t := by

  intro j m n

  have hC1 :
      SpatialC1
        (
          spatial3.d m
            (
              spatial3.d n
                (loggedVelocityComponent u t j)
            )
        ) :=
    h3SecondDerivative_spatialC1
      hClass ht j m n

  have hMeas :
      MeasureTheory.AEStronglyMeasurable
        (
          spatial3.d m
            (
              spatial3.d n
                (loggedVelocityComponent u t j)
            )
        )
        volume :=
    hC1.continuous.aestronglyMeasurable

  have hg2 :
      MeasureTheory.MemLp
        (
          spatial3.d m
            (
              spatial3.d n
                (loggedVelocityComponent u t j)
            )
        )
        (ENNReal.ofReal 2)
        volume :=
    h3SecondDerivative_memLp2
      hClass ht hH3
      j m n

  have hdg2 :
      ∀ i : Axis Depth.three,
        MeasureTheory.MemLp
          (
            spatial3.d i
              (
                spatial3.d m
                  (
                    spatial3.d n
                      (loggedVelocityComponent u t j)
                  )
              )
          )
          (ENNReal.ofReal 2)
          volume := by

    intro i

    exact
      h3ThirdDerivative_memLp2
        hClass ht hH3
        j i m n

  have hg4 :
      MeasureTheory.MemLp
        (
          spatial3.d m
            (
              spatial3.d n
                (loggedVelocityComponent u t j)
            )
        )
        (ENNReal.ofReal 4)
        volume :=
    hSobolev
      (
        spatial3.d m
          (
            spatial3.d n
              (loggedVelocityComponent u t j)
          )
      )
      hC1
      hg2
      hdg2

  unfold LandauQuarticSquareMemLp

  apply
    (
      MeasureTheory.memLp_norm_rpow_iff
        (p := ENNReal.ofReal 4)
        (q := ENNReal.ofReal 2)
        hMeas
        (by norm_num)
        (by simp)
    ).2 at hg4

  have hFourDivTwo :
      (ENNReal.ofReal 4) / (ENNReal.ofReal 2)
        =
      ENNReal.ofReal 2 := by

    have hTwo_ne_zero :
        ENNReal.ofReal 2 ≠ 0 := by
      norm_num

    have hTwo_ne_top :
        ENNReal.ofReal 2 ≠ ⊤ := by
      simp

    symm

    apply
      (
        ENNReal.eq_div_iff
          hTwo_ne_zero
          hTwo_ne_top
      ).2

    norm_num

  rw [hFourDivTwo] at hg4

  simpa [Real.norm_eq_abs] using
    hg4

/--
Canonical H³ square-integrability plus the regularity already stored in the
preterminal energy class reconstruct the outer `f_memLp2` field, all six
legacy third-derivative Cauchy `L²` fields, and all six legacy `MemLp _ 4`
fields of the tuple package.
-/
theorem h3InterpolationTupleLandauAnalyticData_of_core
    {
      u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three
    }
    {a T t : ℝ}
    {h : ℝ → ℝ}
    {i k l j r : Axis Depth.three}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (
      hGradient :
        VelocityGradientEnvelope
          u h t
    )
    (
      hQuartic :
        H3SecondDerivativeQuarticSquareMemLpAt
          u t
    )
    (
      hQuarticIBP :
        WholeSpaceQuarticDerivativeIntegrationByParts
    ) :
    H3InterpolationTupleLandauAnalyticData
      u h t i k l j r := by



  have hh :
      0 ≤ h t :=
    velocityGradientEnvelope_nonneg
      hGradient
      (fun _ : PrimeTensor.Axis Depth.three => (0 : ℝ))

  have hEnvG1 :
      LandauScalarEnvelope
        (
          spatial3.d l
            (loggedVelocityComponent u t r)
        )
        (h t) :=
    landauScalarEnvelope_of_velocityGradientEnvelope
      hh hGradient l r

  have hEnvQ1 :
      LandauScalarEnvelope
        (
          spatial3.d r
            (loggedVelocityComponent u t j)
        )
        (h t) :=
    landauScalarEnvelope_of_velocityGradientEnvelope
      hh hGradient r j

  have hEnvG3 :
      LandauScalarEnvelope
        (
          spatial3.d k
            (loggedVelocityComponent u t r)
        )
        (h t) :=
    landauScalarEnvelope_of_velocityGradientEnvelope
      hh hGradient k r

  have hEnvQ3 :
      LandauScalarEnvelope
        (
          spatial3.d l
            (loggedVelocityComponent u t j)
        )
        (h t) :=
    landauScalarEnvelope_of_velocityGradientEnvelope
      hh hGradient l j

  have hG1Core :
      LandauDerivativeCoreControl
        (
          spatial3.d l
            (loggedVelocityComponent u t r)
        )
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t r)
            )
        )
        (
          spatial3.d k
            (
              spatial3.d k
                (
                  spatial3.d l
                    (loggedVelocityComponent u t r)
                )
            )
        ) := by

    exact
      hQuarticIBP
        (
          spatial3.d l
            (loggedVelocityComponent u t r)
        )
        k
        (h t)
        (h3FirstDerivative_spatialC1 hClass ht r l)
        (h3SecondDerivative_spatialC1 hClass ht r k l)
        hEnvG1
        (
          memLp_four_of_landauQuarticSquareMemLp_of_measurable
            (h3SecondDerivative_aestronglyMeasurable hClass ht r k l)
            (hQuartic r k l)
        )
        (h3ThirdDerivative_memLp2 hClass ht hH3 r k k l)

  have hQ1Core :
      LandauDerivativeCoreControl
        (
          spatial3.d r
            (loggedVelocityComponent u t j)
        )
        (
          spatial3.d i
            (
              spatial3.d r
                (loggedVelocityComponent u t j)
            )
        )
        (
          spatial3.d i
            (
              spatial3.d i
                (
                  spatial3.d r
                    (loggedVelocityComponent u t j)
                )
            )
        ) := by

    exact
      hQuarticIBP
        (
          spatial3.d r
            (loggedVelocityComponent u t j)
        )
        i
        (h t)
        (h3FirstDerivative_spatialC1 hClass ht j r)
        (h3SecondDerivative_spatialC1 hClass ht j i r)
        hEnvQ1
        (
          memLp_four_of_landauQuarticSquareMemLp_of_measurable
            (h3SecondDerivative_aestronglyMeasurable hClass ht j i r)
            (hQuartic j i r)
        )
        (h3ThirdDerivative_memLp2 hClass ht hH3 j i i r)

  have hG2Core :
      LandauDerivativeCoreControl
        (
          spatial3.d l
            (loggedVelocityComponent u t r)
        )
        (
          spatial3.d i
            (
              spatial3.d l
                (loggedVelocityComponent u t r)
            )
        )
        (
          spatial3.d i
            (
              spatial3.d i
                (
                  spatial3.d l
                    (loggedVelocityComponent u t r)
                )
            )
        ) := by

    exact
      hQuarticIBP
        (
          spatial3.d l
            (loggedVelocityComponent u t r)
        )
        i
        (h t)
        (h3FirstDerivative_spatialC1 hClass ht r l)
        (h3SecondDerivative_spatialC1 hClass ht r i l)
        hEnvG1
        (
          memLp_four_of_landauQuarticSquareMemLp_of_measurable
            (h3SecondDerivative_aestronglyMeasurable hClass ht r i l)
            (hQuartic r i l)
        )
        (h3ThirdDerivative_memLp2 hClass ht hH3 r i i l)

  have hQ2Core :
      LandauDerivativeCoreControl
        (
          spatial3.d r
            (loggedVelocityComponent u t j)
        )
        (
          spatial3.d k
            (
              spatial3.d r
                (loggedVelocityComponent u t j)
            )
        )
        (
          spatial3.d k
            (
              spatial3.d k
                (
                  spatial3.d r
                    (loggedVelocityComponent u t j)
                )
            )
        ) := by

    exact
      hQuarticIBP
        (
          spatial3.d r
            (loggedVelocityComponent u t j)
        )
        k
        (h t)
        (h3FirstDerivative_spatialC1 hClass ht j r)
        (h3SecondDerivative_spatialC1 hClass ht j k r)
        hEnvQ1
        (
          memLp_four_of_landauQuarticSquareMemLp_of_measurable
            (h3SecondDerivative_aestronglyMeasurable hClass ht j k r)
            (hQuartic j k r)
        )
        (h3ThirdDerivative_memLp2 hClass ht hH3 j k k r)

  have hG3Core :
      LandauDerivativeCoreControl
        (
          spatial3.d k
            (loggedVelocityComponent u t r)
        )
        (
          spatial3.d i
            (
              spatial3.d k
                (loggedVelocityComponent u t r)
            )
        )
        (
          spatial3.d i
            (
              spatial3.d i
                (
                  spatial3.d k
                    (loggedVelocityComponent u t r)
                )
            )
        ) := by

    exact
      hQuarticIBP
        (
          spatial3.d k
            (loggedVelocityComponent u t r)
        )
        i
        (h t)
        (h3FirstDerivative_spatialC1 hClass ht r k)
        (h3SecondDerivative_spatialC1 hClass ht r i k)
        hEnvG3
        (
          memLp_four_of_landauQuarticSquareMemLp_of_measurable
            (h3SecondDerivative_aestronglyMeasurable hClass ht r i k)
            (hQuartic r i k)
        )
        (h3ThirdDerivative_memLp2 hClass ht hH3 r i i k)

  have hQ3Core :
      LandauDerivativeCoreControl
        (
          spatial3.d l
            (loggedVelocityComponent u t j)
        )
        (
          spatial3.d r
            (
              spatial3.d l
                (loggedVelocityComponent u t j)
            )
        )
        (
          spatial3.d r
            (
              spatial3.d r
                (
                  spatial3.d l
                    (loggedVelocityComponent u t j)
                )
            )
        ) := by

    exact
      hQuarticIBP
        (
          spatial3.d l
            (loggedVelocityComponent u t j)
        )
        r
        (h t)
        (h3FirstDerivative_spatialC1 hClass ht j l)
        (h3SecondDerivative_spatialC1 hClass ht j r l)
        hEnvQ3
        (
          memLp_four_of_landauQuarticSquareMemLp_of_measurable
            (h3SecondDerivative_aestronglyMeasurable hClass ht j r l)
            (hQuartic j r l)
        )
        (h3ThirdDerivative_memLp2 hClass ht hH3 j r r l)

  exact
    {
      f_memLp2 :=
        h3ThirdDerivative_memLp2
          hClass ht hH3
          j i k l
      g1_control :=
        landauDerivativeControl_of_core_of_measurable
          (
            h3FirstDerivative_aestronglyMeasurable
              hClass ht r l
          )
          (
            h3SecondDerivative_aestronglyMeasurable
              hClass ht r k l
          )
          hEnvG1
          (
            h3ThirdDerivative_memLp2
              hClass ht hH3
              r k k l
          )
          (hQuartic r k l)
          hG1Core

      q1_control :=
        landauDerivativeControl_of_core_of_measurable
          (
            h3FirstDerivative_aestronglyMeasurable
              hClass ht j r
          )
          (
            h3SecondDerivative_aestronglyMeasurable
              hClass ht j i r
          )
          hEnvQ1
          (
            h3ThirdDerivative_memLp2
              hClass ht hH3
              j i i r
          )
          (hQuartic j i r)
          hQ1Core

      g2_control :=
        landauDerivativeControl_of_core_of_measurable
          (
            h3FirstDerivative_aestronglyMeasurable
              hClass ht r l
          )
          (
            h3SecondDerivative_aestronglyMeasurable
              hClass ht r i l
          )
          hEnvG1
          (
            h3ThirdDerivative_memLp2
              hClass ht hH3
              r i i l
          )
          (hQuartic r i l)
          hG2Core

      q2_control :=
        landauDerivativeControl_of_core_of_measurable
          (
            h3FirstDerivative_aestronglyMeasurable
              hClass ht j r
          )
          (
            h3SecondDerivative_aestronglyMeasurable
              hClass ht j k r
          )
          hEnvQ1
          (
            h3ThirdDerivative_memLp2
              hClass ht hH3
              j k k r
          )
          (hQuartic j k r)
          hQ2Core

      g3_control :=
        landauDerivativeControl_of_core_of_measurable
          (
            h3FirstDerivative_aestronglyMeasurable
              hClass ht r k
          )
          (
            h3SecondDerivative_aestronglyMeasurable
              hClass ht r i k
          )
          hEnvG3
          (
            h3ThirdDerivative_memLp2
              hClass ht hH3
              r i i k
          )
          (hQuartic r i k)
          hG3Core

      q3_control :=
        landauDerivativeControl_of_core_of_measurable
          (
            h3FirstDerivative_aestronglyMeasurable
              hClass ht j l
          )
          (
            h3SecondDerivative_aestronglyMeasurable
              hClass ht j r l
          )
          hEnvQ3
          (
            h3ThirdDerivative_memLp2
              hClass ht hH3
              j r r l
          )
          (hQuartic j r l)
          hQ3Core
    }

/--
The genuine NS-specific order-three analytic core is now only the
velocity-gradient envelope.  Both the `H¹ → L⁴` step and the quartic
derivative integration-by-parts identity have been factored into generic
whole-space functional-analysis frontiers.
-/
def H3OrderThreeInterpolationLandauCoreAnalyticDataAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (h : ℝ → ℝ)
    (t : ℝ) : Prop :=
  VelocityGradientEnvelope u h t

/--
Reconstruct the legacy analytic-data package from the narrower core package,
using canonical H³ data for the tuplewise outer `L²` fields.
-/
theorem h3OrderThreeInterpolationLandauAnalyticDataAt_of_core
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T t : ℝ}
    {h : ℝ → ℝ}
    (
      hSobolev :
        WholeSpaceC1H1ToL4
    )
    (
      hQuarticIBP :
        WholeSpaceQuarticDerivativeIntegrationByParts
    )
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (
      hCore :
        H3OrderThreeInterpolationLandauCoreAnalyticDataAt
          u h t
    ) :
    H3OrderThreeInterpolationLandauAnalyticDataAt
      u h t := by

  have hQuartic :
      H3SecondDerivativeQuarticSquareMemLpAt
        u t :=
    h3SecondDerivativeQuarticSquareMemLpAt_of_wholeSpaceH1ToL4
      hSobolev
      hClass
      ht
      hH3

  have hGradient :
      VelocityGradientEnvelope
        u h t := by
    simpa [H3OrderThreeInterpolationLandauCoreAnalyticDataAt] using
      hCore

  refine
    ⟨
      velocityGradientEnvelope_nonneg
        hGradient
        (fun _ : PrimeTensor.Axis Depth.three => (0 : ℝ)),
      hGradient,
      ?_
    ⟩

  intro i k l j r

  exact
    h3InterpolationTupleLandauAnalyticData_of_core
      hClass
      ht
      hH3
      hGradient
      hQuartic
      hQuarticIBP

/--
The legacy package forgets to the narrower tuplewise core package.
-/
theorem h3OrderThreeInterpolationLandauCoreAnalyticDataAt_of_analyticData
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t : ℝ}
    (
      hAnalytic :
        H3OrderThreeInterpolationLandauAnalyticDataAt
          u h t
    ) :
    H3OrderThreeInterpolationLandauCoreAnalyticDataAt
      u h t := by

  simpa [H3OrderThreeInterpolationLandauCoreAnalyticDataAt] using
    hAnalytic.2.1


end Euclidean
end Bridge
end PrimeTensor
