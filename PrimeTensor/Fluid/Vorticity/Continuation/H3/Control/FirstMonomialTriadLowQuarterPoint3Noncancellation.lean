import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterCanonicalIntegralTransport

/-!
# Actual physical Point3 first-monomial noncancellation for a real Schwartz velocity

The preceding work constructs a real solenoidal Schwartz velocity on the
canonical `Axis Depth.three` Hilbert carrier, with strictly negative full
physically phased six-order Fourier integral.

Here we define the ORIGINAL physical first-monomial from its spatial
`Point3` derivatives and energy pairings, without assuming the existence of
a Navier--Stokes path having this snapshot. The previous physical Schwartz
and cyclic Fourier identities then give an exact formula with factor three.
Consequently an actual real smooth divergence-free Schwartz velocity has a
strictly negative complete signed spatial first-monomial aggregate.

This is a concrete counterexample to *universal cancellation* of that
monomial. It is not a Navier--Stokes singularity, a nonextension result, or
a global regularity theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap FourierTransform LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3
private abbrev P3 := V3 × V3

noncomputable local instance axisFintypeQuarterPoint3 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceQuarterPoint3 : MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The explicit spatial real Schwartz velocity, indexed by the actual axes. -/
noncomputable def lowNormalQuarterPoint3Velocity
    (ρ : ℝ) (hρ : 0 < ρ) : A3 → ScalarField3 :=
  fun j => h3SchwartzPoint3Scalar
    (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)

/-- The complete 243-slot first-monomial expression, with original Point3
spatial derivatives and the physical energy pairing's factor two. -/
noncomputable def lowNormalQuarterPoint3FirstMonomial
    (ρ : ℝ) (hρ : 0 < ρ) : ℝ :=
  let v := lowNormalQuarterPoint3Velocity ρ hρ
  ∑ j : A3, ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
    spatialEnergyPairing
      (spatial3.d i (spatial3.d k (spatial3.d l (v j))))
      (fun x => spatial3.d k (spatial3.d l (v r)) x *
        spatial3.d i (spatial3.d r (v j)) x)

/-- The complete physical Point3 sum equals twice the real part of the
complex Schwartz aggregate, for any real Schwartz velocity. -/
theorem lowNormalRealSchwartz_point3_firstMonomial_eq
    (f : A3 → SchwartzMap V3 ℝ) :
    (∑ j : A3, ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
      spatialEnergyPairing
        (spatial3.d i (spatial3.d k (spatial3.d l (h3SchwartzPoint3Scalar (f j)))))
        (fun x => spatial3.d k (spatial3.d l (h3SchwartzPoint3Scalar (f r))) x *
          spatial3.d i (spatial3.d r (h3SchwartzPoint3Scalar (f j))) x)) =
      2 * (h3SchwartzFirstMonomialAggregate
        (fun j => h3SchwartzComplexify (f j))).re := by
  classical
  let F : A3 → SchwartzMap V3 ℂ := fun j => h3SchwartzComplexify (f j)
  have hSlot (j r i k l : A3) :
      spatialEnergyPairing
        (spatial3.d i (spatial3.d k (spatial3.d l (h3SchwartzPoint3Scalar (f j)))))
        (fun x => spatial3.d k (spatial3.d l (h3SchwartzPoint3Scalar (f r))) x *
          spatial3.d i (spatial3.d r (h3SchwartzPoint3Scalar (f j))) x) =
        2 * (h3SchwartzFirstMonomialSlot F i k l r j).re := by
    rw [h3SchwartzPoint3_firstMonomial_pairing (f j) (f r) (f j) i k l r]
    rw [h3SchwartzFirstMonomialSlot_complexify f i k l r j]
    simp only [Complex.ofReal_re]
  have hOrder :
      (∑ j : A3, ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
        (h3SchwartzFirstMonomialSlot F i k l r j).re) =
      ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
        (h3SchwartzFirstMonomialSlot F i k l r j).re := by
    simp only [axis_sum_three]
    ac_rfl
  have hRe :
      (h3SchwartzFirstMonomialAggregate F).re =
      ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
        (h3SchwartzFirstMonomialSlot F i k l r j).re := by
    unfold h3SchwartzFirstMonomialAggregate
    change Complex.reCLM
      (∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
        h3SchwartzFirstMonomialSlot F i k l r j) = _
    simp only [map_sum]
    rfl
  simp_rw [hSlot]
  simp only [← Finset.mul_sum]
  rw [hOrder, ← hRe]

/-- Specialize the exact Schwartz/Point3 equality to the constructed
canonical real velocity; no path-realization assumptions are introduced. -/
theorem lowNormalQuarterPoint3FirstMonomial_eq_complex
    (ρ : ℝ) (hρ : 0 < ρ) :
    lowNormalQuarterPoint3FirstMonomial ρ hρ =
      2 * (h3SchwartzFirstMonomialAggregate
        (fun j : A3 => h3SchwartzComplexify
          (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j))).re := by
  unfold lowNormalQuarterPoint3FirstMonomial lowNormalQuarterPoint3Velocity
  exact lowNormalRealSchwartz_point3_firstMonomial_eq
    (fun j : A3 => lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)

/-- EXACT signed spatial/Fourier equality for the constructed real
solenoidal Schwartz field. The physical factor two and the cyclic factor
three are both retained, so there is no hidden scalar normalization. -/
theorem lowNormalQuarterPoint3FirstMonomial_three_eq_fourier
    (ρ : ℝ) (hρ : 0 < ρ) :
    3 * lowNormalQuarterPoint3FirstMonomial ρ hρ =
      ∫ z : P3,
        (((2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
          h3SchwartzTriadSixOrderKernel
            (fun j : A3 => h3SchwartzComplexify
              (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)) z).re
        ∂(volume.prod volume) := by
  let F : A3 → SchwartzMap V3 ℂ := fun j =>
    h3SchwartzComplexify (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)
  have hDiv : ∀ q : A3 → ℝ,
      mixedDot q (h3SchwartzTriadPolarization F q) = 0 :=
    h3SchwartzTriadPolarization_divergence_zero F
      (lowNormalQuarterAxisRealSchwartz_physical_divergence ρ hρ)
  have hTwo := h3SchwartzFirstMonomialAggregate_twice_eq_shell F hDiv
  have hSix := h3SchwartzTriadSixOrderKernel_integral F hDiv
  have hComplex :
      (3 : ℂ) * (2 * h3SchwartzFirstMonomialAggregate F) =
        (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
          (∫ z : P3, h3SchwartzTriadSixOrderKernel F z
            ∂(volume.prod volume)) := by
    calc
      _ = (3 : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
          (∫ z : P3, h3SchwartzTriadShellKernel F z
            ∂(volume.prod volume))) := by rw [hTwo]
      _ = (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
          (∫ z : P3, h3SchwartzTriadSixOrderKernel F z
            ∂(volume.prod volume)) := by rw [hSix]; ring
  have hI : Integrable
      (fun z : P3 => (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        h3SchwartzTriadSixOrderKernel F z) (volume.prod volume) :=
    (h3SchwartzTriadSixOrderKernel_integrable F hDiv).const_mul _
  rw [lowNormalQuarterPoint3FirstMonomial_eq_complex]
  change 3 * (2 * (h3SchwartzFirstMonomialAggregate F).re) = _
  calc
    _ = ((3 : ℂ) * (2 * h3SchwartzFirstMonomialAggregate F)).re := by
      norm_num [Complex.mul_re] <;> ring
    _ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
          (∫ z : P3, h3SchwartzTriadSixOrderKernel F z
            ∂(volume.prod volume))).re := congrArg Complex.re hComplex
    _ = (∫ z : P3, (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
          h3SchwartzTriadSixOrderKernel F z ∂(volume.prod volume)).re := by
      rw [integral_const_mul]
    _ = ∫ z : P3,
        (((2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
          h3SchwartzTriadSixOrderKernel F z).re
          ∂(volume.prod volume) :=
      (Complex.reCLM.integral_comp_comm hI).symm
    _ = _ := by
      rfl

/-- Explicit counterexample to a universal-cancellation identity for the
FULL 243-slot physical first monomial, not merely its Fourier symbol. -/
theorem lowNormalQuarterPoint3_exists_negative_firstMonomial :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      lowNormalQuarterPoint3FirstMonomial ρ hρ < 0 := by
  obtain ⟨ρ, hρ, hNeg⟩ :=
    lowNormalQuarterCanonical_exists_negative_physicalPhase_integral
  refine ⟨ρ, hρ, ?_⟩
  have hEq := lowNormalQuarterPoint3FirstMonomial_three_eq_fourier ρ hρ
  rw [← hEq] at hNeg
  nlinarith

/-- Any preexisting logged velocity path realizing THIS concrete real
Schwartz snapshot inherits its signed physical monomial. This is explicitly
conditional; no Navier--Stokes solution path is constructed here. -/
theorem lowNormalQuarterPathFirstMonomial_negative_of_realization
    (ρ : ℝ) (hρ : 0 < ρ)
    (hNeg : lowNormalQuarterPoint3FirstMonomial ρ hρ < 0)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j =
        lowNormalQuarterPoint3Velocity ρ hρ j) :
    h3PathCanonicalFirstMonomialAggregateAt u t < 0 := by
  have hEq := h3PathCanonicalFirstMonomialAggregate_eq_complexSchwartz u t
    (fun j : A3 => lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)
    (by simpa only [lowNormalQuarterPoint3Velocity] using hRealization)
  rw [hEq]
  simpa only [lowNormalQuarterPoint3FirstMonomial_eq_complex] using hNeg

end
end PrimeTensor.FirstMonomialTriad
