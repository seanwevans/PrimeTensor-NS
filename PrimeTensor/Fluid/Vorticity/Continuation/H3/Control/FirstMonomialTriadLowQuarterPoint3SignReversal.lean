import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3Noncancellation

/-!
# Both signs of the complete Point3 first-monomial for real solenoidal Schwartz data

The preceding checkpoint gave a strictly negative complete physical 243-slot
first-monomial integral for one real divergence-free Schwartz velocity.

Here the first-monomial's *oddness under velocity reversal* is proved, first
for arbitrary complex Schwartz fields (using all five indices and the actual
triple product), then for arbitrary real Schwartz Point3 fields. Negating the
concrete quarter packet produces a positive witness AT THE SAME WIDTH.

We also prove Fourier and physical divergence freedom for the reversed
Schwartz velocity. Hence the complete physical first monomial is sign-indefinite
even within the real solenoidal Schwartz class.

No Navier--Stokes solution is constructed. The assertion is algebraic/analytic
at a smooth snapshot, and does not control the other H3 energy terms.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap FourierTransform LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeQuarterSignReversal (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceQuarterSignReversal : MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exactly the original 243-slot physical first-monomial, for *arbitrary*
real Schwartz velocity components pulled back to Point3. -/
noncomputable def lowNormalRealSchwartzPoint3Monomial
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
    spatialEnergyPairing
      (spatial3.d i (spatial3.d k
        (spatial3.d l (h3SchwartzPoint3Scalar (f j)))))
      (fun x =>
        spatial3.d k (spatial3.d l (h3SchwartzPoint3Scalar (f r))) x *
          spatial3.d i (spatial3.d r (h3SchwartzPoint3Scalar (f j))) x)

/-- No artificial 'physical functional': the real-Schwartz expression
coincides exactly with the previously formalized spatial 243-slot pairing. -/
theorem lowNormalRealSchwartzPoint3Monomial_eq_complex
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzPoint3Monomial f =
      2 * (h3SchwartzFirstMonomialAggregate
        (fun j => h3SchwartzComplexify (f j))).re := by
  unfold lowNormalRealSchwartzPoint3Monomial
  exact lowNormalRealSchwartz_point3_firstMonomial_eq f

/-- Three occurrences of the velocity make each complex Schwartz monomial
odd under *simultaneous* sign reversal of every velocity component. -/
theorem lowNormalSchwartzFirstMonomialSlot_neg
    (F : A3 → SchwartzMap V3 ℂ) (i k l r j : A3) :
    h3SchwartzFirstMonomialSlot (fun a => -F a) i k l r j =
      -h3SchwartzFirstMonomialSlot F i k l r j := by
  unfold h3SchwartzFirstMonomialSlot
  simp only [LineDeriv.lineDerivOp_neg, neg_apply, neg_mul,
    mul_neg, neg_neg, integral_neg]

/-- The whole five-index aggregate, including its physical multiplicities,
is odd under velocity reversal. -/
theorem lowNormalSchwartzFirstMonomialAggregate_neg
    (F : A3 → SchwartzMap V3 ℂ) :
    h3SchwartzFirstMonomialAggregate (fun j => -F j) =
      -h3SchwartzFirstMonomialAggregate F := by
  unfold h3SchwartzFirstMonomialAggregate
  simp_rw [lowNormalSchwartzFirstMonomialSlot_neg F]
  simp only [Finset.sum_neg_distrib]

/-- Complexification commutes with reversing a REAL Schwartz component. -/
theorem lowNormalSchwartzComplexify_neg (g : SchwartzMap V3 ℝ) :
    h3SchwartzComplexify (-g) = -h3SchwartzComplexify g := by
  change (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM) (-g) =
    -((SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM) g)
  exact map_neg _ _

/-- The 243-slot physical Point3 integral is odd for ANY real Schwartz
velocity, with NO incompressibility or PDE hypotheses necessary. -/
theorem lowNormalRealSchwartzPoint3Monomial_neg
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzPoint3Monomial (fun j => -f j) =
      -lowNormalRealSchwartzPoint3Monomial f := by
  simp only [lowNormalRealSchwartzPoint3Monomial_eq_complex]
  simp_rw [lowNormalSchwartzComplexify_neg]
  rw [lowNormalSchwartzFirstMonomialAggregate_neg]
  simp only [Complex.neg_re, mul_neg]

/-- The canonical real Schwartz velocity from the previous checkpoint,
with EVERY velocity component reversed. -/
noncomputable def lowNormalQuarterOppositeSchwartzVelocity
    (ρ : ℝ) (hρ : 0 < ρ) : A3 → SchwartzMap V3 ℝ :=
  fun j => -lowNormalQuarterAxisRealSchwartzComponent ρ hρ j

/-- Velocity reversal preserves the true physical divergence equation, not
just a formal Fourier-side polarization constraint. -/
theorem lowNormalQuarterOppositeSchwartz_physical_divergence
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ x : V3,
      ∑ j : A3,
        fderiv ℝ
          (h3SchwartzComplexify (lowNormalQuarterOppositeSchwartzVelocity ρ hρ j))
          x (h3FourierAxisDirection j) = 0 := by
  intro x
  have h := lowNormalQuarterAxisRealSchwartz_physical_divergence ρ hρ x
  change (∑ j : A3,
    fderiv ℝ (h3SchwartzComplexify
      (-lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)) x
      (h3FourierAxisDirection j)) = 0
  have hterm (j : A3) :
      fderiv ℝ
          (h3SchwartzComplexify
            (-lowNormalQuarterAxisRealSchwartzComponent ρ hρ j))
          x (h3FourierAxisDirection j) =
        -fderiv ℝ
          (h3SchwartzComplexify
            (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j))
          x (h3FourierAxisDirection j) := by
    rw [lowNormalSchwartzComplexify_neg]
    change (∂_{h3FourierAxisDirection j}
        (-h3SchwartzComplexify
          (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j))) x =
      -((∂_{h3FourierAxisDirection j}
        (h3SchwartzComplexify
          (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j))) x)
    simp only [LineDeriv.lineDerivOp_neg, neg_apply]
  calc
    (∑ j : A3,
      fderiv ℝ
        (h3SchwartzComplexify
          (-lowNormalQuarterAxisRealSchwartzComponent ρ hρ j))
        x (h3FourierAxisDirection j)) =
        ∑ j : A3,
          -(fderiv ℝ
            (h3SchwartzComplexify
              (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j))
            x (h3FourierAxisDirection j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hterm j
    _ = -(∑ j : A3,
      fderiv ℝ
        (h3SchwartzComplexify
          (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j))
        x (h3FourierAxisDirection j)) := by
      rw [Finset.sum_neg_distrib]
    _ = 0 := by rw [h, neg_zero]

/-- The same window width gives two REAL divergence-free Schwartz velocities
with opposite, STRICT signs of the complete physical first monomial. -/
theorem lowNormalQuarterPoint3_exists_both_firstMonomial_signs :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      lowNormalRealSchwartzPoint3Monomial
        (fun j : A3 => lowNormalQuarterAxisRealSchwartzComponent ρ hρ j) < 0 ∧
      0 < lowNormalRealSchwartzPoint3Monomial
        (lowNormalQuarterOppositeSchwartzVelocity ρ hρ) := by
  obtain ⟨ρ, hρ, hNeg⟩ :=
    lowNormalQuarterPoint3_exists_negative_firstMonomial
  refine ⟨ρ, hρ, ?_, ?_⟩
  · change lowNormalQuarterPoint3FirstMonomial ρ hρ < 0
    exact hNeg
  · change 0 < lowNormalRealSchwartzPoint3Monomial
      (fun j : A3 => -lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)
    rw [lowNormalRealSchwartzPoint3Monomial_neg]
    change 0 < -lowNormalQuarterPoint3FirstMonomial ρ hρ
    exact neg_pos.mpr hNeg

end
end PrimeTensor.FirstMonomialTriad
