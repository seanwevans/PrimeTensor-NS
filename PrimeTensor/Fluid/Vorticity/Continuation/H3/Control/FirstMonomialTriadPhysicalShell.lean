import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadPhysicalTransport
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Encoded.Reality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Derivative

/-!
# The shell formula for the existing physical first-monomial aggregate

Complexification, finite-sum reindexing and physical divergence transport
connect the Schwartz shell theorem to h3PathCanonicalFirstMonomialAggregateAt.
The explicit hypothesis is a real Schwartz realization of the logged velocity
at the time in question. No claim that arbitrary H3 data are Schwartz is made.
-/

namespace PrimeTensor.Bridge.Euclidean

open MeasureTheory
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3TriadPhysicalShell (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TriadPhysicalShell : MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

local notation "A3" => PrimeTensor.Axis Depth.three
local notation "V3" => H3FourierPoint3

/-- Reuse the existing complexification/derivative compatibility. -/
theorem h3TriadComplexify_lineDeriv (f : SchwartzMap V3 ℝ) (a : V3) :
    ∂_{a} (h3SchwartzComplexify f) = h3SchwartzComplexify (∂_{a} f) :=
  h3SchwartzComplexify_lineDeriv f a

/-- A complexified coordinate slot is exactly the real integral embedded in C. -/
theorem h3SchwartzFirstMonomialSlot_complexify
    (f : A3 → SchwartzMap V3 ℝ) (i k l v j : A3) :
    h3SchwartzFirstMonomialSlot (fun j => h3SchwartzComplexify (f j)) i k l v j =
      ((∫ x : V3,
        ((∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} (f j)))) x) *
        (((∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} (f v))) x) *
          ((∂_{h3FourierAxisDirection i} (∂_{h3FourierAxisDirection v} (f j))) x)) : ℝ) : ℂ) := by
  let F := ∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} (f j)))
  let G := ∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} (f v))
  let H := ∂_{h3FourierAxisDirection i} (∂_{h3FourierAxisDirection v} (f j))
  have hi : Integrable (fun x : V3 => F x * (G x * H x)) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) F
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) G H)).integrable
  simp only [h3SchwartzFirstMonomialSlot, h3TriadComplexify_lineDeriv,
    h3SchwartzComplexify_apply]
  change (∫ x : V3, ((F x : ℂ) * (G x : ℂ)) * (H x : ℂ)) = _
  calc
    _ = ∫ x : V3, ((F x * (G x * H x) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      push_cast
      ring
    _ = _ := Complex.ofRealCLM.integral_comp_comm hi

/-- Identify the genuine physical slot with twice the real part of its complex slot. -/
theorem h3PathCanonicalFirstMonomial_eq_complexSchwartz
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j, loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (j i k l v : A3) :
    h3PathCanonicalInterpolationMonomialPairing u t j i k l v 0 =
      2 * (h3SchwartzFirstMonomialSlot
        (fun j => h3SchwartzComplexify (f j)) i k l v j).re := by
  rw [h3PathCanonicalFirstMonomial_eq_realSchwartz u t f hRealization,
    h3SchwartzFirstMonomialSlot_complexify]
  rfl

/-- The physical index order and the kernel index order enumerate the same slots. -/
private theorem h3Triad_sum_order (F : A3 → A3 → A3 → A3 → A3 → ℝ) :
    (∑ j, ∑ v, ∑ i, ∑ k, ∑ l, F i k l v j) =
      ∑ i, ∑ k, ∑ l, ∑ v, ∑ j, F i k l v j := by
  simp only [axis_sum_three]
  ac_rfl

/-- Exact identification with the previously defined complex Schwartz aggregate. -/
theorem h3PathCanonicalFirstMonomialAggregate_eq_complexSchwartz
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j, loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    h3PathCanonicalFirstMonomialAggregateAt u t =
      2 * (h3SchwartzFirstMonomialAggregate (fun j => h3SchwartzComplexify (f j))).re := by
  classical
  have hRe :
      (h3SchwartzFirstMonomialAggregate (fun j => h3SchwartzComplexify (f j))).re =
      ∑ i, ∑ k, ∑ l, ∑ v, ∑ j,
        (h3SchwartzFirstMonomialSlot (fun j => h3SchwartzComplexify (f j)) i k l v j).re := by
    unfold h3SchwartzFirstMonomialAggregate
    change Complex.reCLM (∑ i, ∑ k, ∑ l, ∑ v, ∑ j,
      h3SchwartzFirstMonomialSlot (fun j => h3SchwartzComplexify (f j)) i k l v j) = _
    simp only [map_sum]
    rfl
  unfold h3PathCanonicalFirstMonomialAggregateAt
  simp only [h3PathCanonicalFirstMonomial_eq_complexSchwartz u t f hRealization]
  rw [hRe]
  simp only [← Finset.mul_sum]
  rw [h3Triad_sum_order]

/-- Physical divergence on Point3 transports to complex Schwartz divergence. -/
theorem h3TriadComplexify_physical_divergence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j, loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hDiv : ∀ x : Point3, ∑ j, spatial3.d j (loggedVelocityComponent u t j) x = 0) :
    ∀ y : V3, ∑ j, fderiv ℝ (h3SchwartzComplexify (f j)) y (h3FourierAxisDirection j) = 0 := by
  intro y
  have hr := hDiv (WithLp.ofLp y)
  simp only [hRealization, h3SchwartzPoint3Scalar_spatial_d, h3SchwartzPoint3Scalar] at hr
  have hr' : (∑ j, (∂_{h3FourierAxisDirection j} (f j)) y) = 0 := hr
  simp only [← SchwartzMap.lineDerivOp_apply_eq_fderiv, h3TriadComplexify_lineDeriv,
    h3SchwartzComplexify_apply]
  exact_mod_cast hr'

/-- The signed shell formula for the existing physical first-monomial aggregate.
Only a real Schwartz realization and physical incompressibility are assumed. -/
theorem h3PathCanonicalFirstMonomialAggregate_eq_shell_of_realSchwartz
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j, loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hDiv : ∀ x : Point3, ∑ j, spatial3.d j (loggedVelocityComponent u t j) x = 0) :
    h3PathCanonicalFirstMonomialAggregateAt u t =
      (2 * Real.pi) ^ 7 *
        (∫ z, h3SchwartzTriadShellKernel (fun j => h3SchwartzComplexify (f j)) z
          ∂volume.prod volume).im := by
  rw [h3PathCanonicalFirstMonomialAggregate_eq_complexSchwartz u t f hRealization]
  exact h3SchwartzFirstMonomialAggregate_twice_re_eq_shell_im_of_physical_divergence _
    (h3TriadComplexify_physical_divergence u t f hRealization hDiv)

/-- Recover the interpolation multiplicity three after the physical aggregate
has been identified. All Fourier and pairing constants are now explicit. -/
theorem h3PathCanonicalInterpolation_eq_shell_of_realSchwartz
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j, loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hDiv : ∀ x : Point3, ∑ j, spatial3.d j (loggedVelocityComponent u t j) x = 0) :
    thirdOrderInterpolationTransportSum u t =
      3 * (2 * Real.pi) ^ 7 *
        (∫ z, h3SchwartzTriadShellKernel (fun j => h3SchwartzComplexify (f j)) z
          ∂volume.prod volume).im := by
  rw [h3PathCanonical_interpolation_eq_three_firstMonomialAggregate hH3 hClass ht,
    h3PathCanonicalFirstMonomialAggregate_eq_shell_of_realSchwartz u t f hRealization hDiv]
  ring

end
end PrimeTensor.Bridge.Euclidean
