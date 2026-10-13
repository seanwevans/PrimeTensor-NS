import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowPhysicalPhase
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadIntegralBound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadPhysicalShell

/-!
# Measure-preserving cyclic reindexing of the full first-monomial triad

The involution (p,r) ↦ (p,-p-r) already exists as `h3TriadMiddleEquiv`.
Conjugating it by exchange of the two factors supplies (p,r) ↦ (-p-r,r).
Both transformations preserve product volume. As a result, the integrated
six-permutation symbol is exactly three copies of the already-established
outer-exchange shell integral, for one divergence-free Schwartz polarization.

The concluding physical identity uses the existing real-Schwartz realization
hypothesis. Nothing here constructs a Schwartz field from the sharp pointwise
polarizations, and no integrated noncancellation or continuation is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The cyclic shell identity works for the project's Axis index type, not
only for the Fin 3 example used in the sharpness audit. -/
theorem shellKernel_three_cyclic_eq_sixOrder_generic
    (U : (ι → ℝ) → (ι → ℂ)) (p q r : ι → ℝ)
    (hm : ∀ i, p i + q i + r i = 0)
    (hDiv : ∀ ξ, mixedDot ξ (U ξ) = 0) :
    shellKernel U (p, r) + shellKernel U (p, q) + shellKernel U (q, r) =
      sixOrderTriadCoefficient p q r (U p) (U q) (U r) := by
  have hpr : middleFrequency p r = q := by
    funext i
    dsimp [middleFrequency]
    linarith [hm i]
  have hpq : middleFrequency p q = r := by
    funext i
    dsimp [middleFrequency]
    linarith [hm i]
  have hqr : middleFrequency q r = p := by
    funext i
    dsimp [middleFrequency]
    linarith [hm i]
  change
    complexShellCoefficient p (middleFrequency p r) r (U (middleFrequency p r)) *
      amplitudeDot (U p) (U r) +
    complexShellCoefficient p (middleFrequency p q) q (U (middleFrequency p q)) *
      amplitudeDot (U p) (U q) +
    complexShellCoefficient q (middleFrequency q r) r (U (middleFrequency q r)) *
      amplitudeDot (U q) (U r) =
    sixOrderTriadCoefficient p q r (U p) (U q) (U r)
  rw [hpr, hpq, hqr]
  exact (sixOrderTriadCoefficient_eq_shells p q r (U p) (U q) (U r)
    hm (hDiv p) (hDiv q) (hDiv r)).symm

end
end PrimeTensor.FirstMonomialTriad

namespace PrimeTensor.Bridge.Euclidean

open MeasureTheory
open scoped BigOperators

noncomputable section

noncomputable local instance axisFintypeH3TriadCyclicIntegral (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local notation "A3" => PrimeTensor.Axis Depth.three
local notation "V3" => H3FourierPoint3

/-- The cyclic change (p,r) ↦ (q,r), q = -p-r, is the old middle-frequency
involution conjugated by the product swap. -/
def h3TriadCyclicRightEquiv : V3 × V3 ≃ᵐ V3 × V3 :=
  (MeasurableEquiv.prodComm : V3 × V3 ≃ᵐ V3 × V3).trans
    (h3TriadMiddleEquiv.trans
      (MeasurableEquiv.prodComm : V3 × V3 ≃ᵐ V3 × V3))

@[simp] theorem h3TriadCyclicRightEquiv_apply (z : V3 × V3) :
    h3TriadCyclicRightEquiv z = (-(z.1 + z.2), z.2) := by
  change (-(z.2 + z.1), z.2) = (-(z.1 + z.2), z.2)
  rw [add_comm z.2 z.1]

/-- In particular, no Jacobian or compensating Fourier constant appears. -/
theorem h3TriadCyclicRightEquiv_preserving :
    MeasurePreserving h3TriadCyclicRightEquiv
      (volume.prod volume) (volume.prod volume) := by
  have hs : MeasurePreserving
      (MeasurableEquiv.prodComm : V3 × V3 ≃ᵐ V3 × V3)
      (volume.prod volume) (volume.prod volume) :=
    Measure.measurePreserving_swap (μ := (volume : Measure V3))
      (ν := (volume : Measure V3))
  exact (hs.comp h3TriadMiddleEquiv_preserving).comp hs

/-- Cyclic sum of a *single* Schwartz shell kernel over the three choices
of outer-frequency pair. -/
def h3SchwartzTriadCyclicShellSum
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) : ℂ :=
  h3SchwartzTriadShellKernel u z +
    h3SchwartzTriadShellKernel u (h3TriadMiddleEquiv z) +
    h3SchwartzTriadShellKernel u (h3TriadCyclicRightEquiv z)

/-- The six-order polynomial evaluated on the Fourier transform of the same
Schwartz field at all three momentum-conserving frequencies. -/
def h3SchwartzTriadSixOrderKernel
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) : ℂ :=
  FirstMonomialTriad.sixOrderTriadCoefficient
    (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2))) (WithLp.ofLp z.2)
    (h3SchwartzTriadPolarization u (WithLp.ofLp z.1))
    (h3SchwartzTriadPolarization u (WithLp.ofLp (-(z.1 + z.2))))
    (h3SchwartzTriadPolarization u (WithLp.ofLp z.2))

/-- The finite-dimensional cyclic identity matches the actual Fourier
polarizations pointwise, before taking any absolute values. -/
theorem h3SchwartzTriadCyclicShellSum_eq_sixOrder
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0)
    (z : V3 × V3) :
    h3SchwartzTriadCyclicShellSum u z = h3SchwartzTriadSixOrderKernel u z := by
  let p : A3 → ℝ := WithLp.ofLp z.1
  let q : A3 → ℝ := WithLp.ofLp (-(z.1 + z.2))
  let r : A3 → ℝ := WithLp.ofLp z.2
  have hm : ∀ i, p i + q i + r i = 0 := by
    intro i
    change (WithLp.ofLp z.1) i +
      (WithLp.ofLp (-(z.1 + z.2))) i + (WithLp.ofLp z.2) i = 0
    simp only [WithLp.ofLp_neg, WithLp.ofLp_add, Pi.neg_apply, Pi.add_apply]
    abel
  have h := FirstMonomialTriad.shellKernel_three_cyclic_eq_sixOrder_generic
    (h3SchwartzTriadPolarization u) p q r hm hDiv
  simpa [h3SchwartzTriadCyclicShellSum, h3SchwartzTriadSixOrderKernel,
    h3SchwartzTriadShellKernel, h3TriadMiddleEquiv,
    h3TriadCyclicRightEquiv_apply, p, q, r] using h

/-- The cyclic sum remains integrable because each change of variables
preserves the product volume. -/
theorem h3SchwartzTriadCyclicShellSum_integrable
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    Integrable (h3SchwartzTriadCyclicShellSum u) (volume.prod volume) := by
  have hK := h3SchwartzTriadShellKernel_integrable u hDiv
  have hM : Integrable
      (fun z => h3SchwartzTriadShellKernel u (h3TriadMiddleEquiv z))
      (volume.prod volume) :=
    (h3TriadMiddleEquiv_preserving.integrable_comp hK.aestronglyMeasurable).mpr hK
  have hR : Integrable
      (fun z => h3SchwartzTriadShellKernel u (h3TriadCyclicRightEquiv z))
      (volume.prod volume) :=
    (h3TriadCyclicRightEquiv_preserving.integrable_comp hK.aestronglyMeasurable).mpr hK
  exact (hK.add hM).add hR

/-- **Integrated cyclic identity.** All three orderings give the same
integral, without discarding phases or estimating absolute values. -/
theorem h3SchwartzTriadCyclicShellSum_integral
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    (∫ z, h3SchwartzTriadCyclicShellSum u z ∂volume.prod volume) =
      3 * ∫ z, h3SchwartzTriadShellKernel u z ∂volume.prod volume := by
  have hK := h3SchwartzTriadShellKernel_integrable u hDiv
  have hM : Integrable
      (fun z => h3SchwartzTriadShellKernel u (h3TriadMiddleEquiv z))
      (volume.prod volume) :=
    (h3TriadMiddleEquiv_preserving.integrable_comp hK.aestronglyMeasurable).mpr hK
  have hR : Integrable
      (fun z => h3SchwartzTriadShellKernel u (h3TriadCyclicRightEquiv z))
      (volume.prod volume) :=
    (h3TriadCyclicRightEquiv_preserving.integrable_comp hK.aestronglyMeasurable).mpr hK
  have hAdd2 := integral_add (hK.add hM) hR
  have hAdd1 := integral_add hK hM
  simp only [Pi.add_apply] at hAdd2 hAdd1
  unfold h3SchwartzTriadCyclicShellSum
  rw [hAdd2, hAdd1,
    h3TriadMiddleEquiv_preserving.integral_comp
      h3TriadMiddleEquiv.measurableEmbedding (h3SchwartzTriadShellKernel u),
    h3TriadCyclicRightEquiv_preserving.integral_comp
      h3TriadCyclicRightEquiv.measurableEmbedding (h3SchwartzTriadShellKernel u)]
  ring

/-- The six-permutation Schwartz kernel is absolutely integrable, not merely
formally integrable. -/
theorem h3SchwartzTriadSixOrderKernel_integrable
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    Integrable (h3SchwartzTriadSixOrderKernel u) (volume.prod volume) :=
  (h3SchwartzTriadCyclicShellSum_integrable u hDiv).congr
    (Filter.Eventually.of_forall (h3SchwartzTriadCyclicShellSum_eq_sixOrder u hDiv))

/-- Exact six-order Schwartz integral, with the cyclic factor three. -/
theorem h3SchwartzTriadSixOrderKernel_integral
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    (∫ z, h3SchwartzTriadSixOrderKernel u z ∂volume.prod volume) =
      3 * ∫ z, h3SchwartzTriadShellKernel u z ∂volume.prod volume := by
  rw [← h3SchwartzTriadCyclicShellSum_integral u hDiv]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z =>
    (h3SchwartzTriadCyclicShellSum_eq_sixOrder u hDiv z).symm)

/-- Physical Schwartz realization: cyclic symmetrization introduces exactly
three copies of the signed shell contribution; no other physical prefactor. -/
theorem h3PathCanonicalFirstMonomialAggregate_three_eq_sixOrder_of_realSchwartz
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j, loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hDiv : ∀ x : Point3, ∑ j, spatial3.d j (loggedVelocityComponent u t j) x = 0) :
    3 * h3PathCanonicalFirstMonomialAggregateAt u t =
      (2 * Real.pi) ^ 7 *
        (∫ z, h3SchwartzTriadSixOrderKernel
          (fun j => h3SchwartzComplexify (f j)) z ∂volume.prod volume).im := by
  let F : A3 → SchwartzMap V3 ℂ := fun j => h3SchwartzComplexify (f j)
  have hFourierDiv : ∀ q,
      FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization F q) = 0 :=
    h3SchwartzTriadPolarization_divergence_zero F
      (h3TriadComplexify_physical_divergence u t f hRealization hDiv)
  have hIntegral := congrArg Complex.im
    (h3SchwartzTriadSixOrderKernel_integral F hFourierDiv)
  have hThree : ((3 : ℂ) *
      (∫ z, h3SchwartzTriadShellKernel F z ∂volume.prod volume)).im =
      3 * (∫ z, h3SchwartzTriadShellKernel F z ∂volume.prod volume).im := by
    rw [Complex.mul_im]
    norm_num
  rw [hThree] at hIntegral
  rw [h3PathCanonicalFirstMonomialAggregate_eq_shell_of_realSchwartz
    u t f hRealization hDiv]
  change 3 * ((2 * Real.pi) ^ 7 *
    (∫ z, h3SchwartzTriadShellKernel F z ∂volume.prod volume).im) =
    (2 * Real.pi) ^ 7 *
    (∫ z, h3SchwartzTriadSixOrderKernel F z ∂volume.prod volume).im
  rw [hIntegral]
  ring

end
end PrimeTensor.Bridge.Euclidean
