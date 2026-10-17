import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3CriticalHalfBalancedShape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3ActualDilationEnergySums
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3ActualDilationMonomial
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SignReversal
import Mathlib.Tactic

/-!
# Genuine fixed-kinetic-energy concentration barrier for the physical first monomial

This is an obstruction to closing the signed FIRST H³ interpolation monomial
by top dissipation with a coefficient depending only on kinetic energy.

For a real three-component Schwartz velocity f, define
  g_t(x) = t³ f(t² x), t>0.
Both operations are the already-certified actual Point3 amplitude/dilation
operations. Their *combined* exponents, with no use of formal Fourier
surrogates, are
  E0(g_t)=E0(f),  E1(g_t)=t⁴ E1(f),
  D4(g_t)=t¹⁶ D4(f), M(g_t)=t¹⁷ M(f).
Thus a positive first monomial outruns any fixed multiple of dissipation even
at an exactly fixed kinetic-energy level, and with exact solenoidality.

The result is intentionally about the signed 243-slot FIRST interpolation
monomial. It is NOT an obstruction to possible cancellation among different
physical Navier--Stokes transport terms or to dynamic a priori bounds.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFixedKinetic244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Simultaneously concentrate in space by t² and amplify by t³. The
physical squared kinetic norm, not a spectral proxy, is invariant. -/
noncomputable def fixedKineticSchwartzConcentration244
    (t : ℝ) (ht : 0 < t) (f : A3 → SchwartzMap V3 ℝ) :
    A3 → SchwartzMap V3 ℝ :=
  fun j => (t ^ 3) • (lowNormalSchwartzVelocityDilation (t ^ 2)
    (sq_pos_of_pos ht) f j)

/-- Literal Point3 physical solenoidality survives the coupled rescaling. -/
theorem fixedKineticSchwartzConcentration_solenoidal244
    (t : ℝ) (ht : 0 < t) (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f) :
    lowNormalRealSchwartz_Point3Solenoidal
      (fixedKineticSchwartzConcentration244 t ht f) := by
  unfold fixedKineticSchwartzConcentration244
  exact lowNormalRealSchwartz_Point3Solenoidal_real_smul (t ^ 3)
    (lowNormalSchwartzVelocityDilation (t ^ 2) (sq_pos_of_pos ht) f)
    (lowNormalRealSchwartz_Point3Solenoidal_dilation (t ^ 2)
      (sq_pos_of_pos ht) f hDiv)

/-- Exact conservation of the full physical kinetic square mass along the
concentrating family, including all three components. -/
theorem fixedKineticSchwartzConcentration_energy0_eq244
    (t : ℝ) (ht : 0 < t) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy0
      (fixedKineticSchwartzConcentration244 t ht f) =
    lowNormalRealSchwartzH3Energy0 f := by
  unfold fixedKineticSchwartzConcentration244
  rw [lowNormalRealSchwartzH3Energy0_real_smul,
    lowNormalRealSchwartzH3Energy0_dilation]
  have hn : t ≠ 0 := ne_of_gt ht
  field_simp [hn]


/-- At a FIXED E0, the first-order physical energy grows as t⁴. -/
theorem fixedKineticSchwartzConcentration_energy1_eq244
    (t : ℝ) (ht : 0 < t) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy1
      (fixedKineticSchwartzConcentration244 t ht f) =
    t ^ 4 * lowNormalRealSchwartzH3Energy1 f := by
  unfold fixedKineticSchwartzConcentration244
  -- The order-one energy is a finite sum of squares. Amplification has degree two.
  have hAmp (a : ℝ) (g : A3 → SchwartzMap V3 ℝ) :
      lowNormalRealSchwartzH3Energy1 (fun j => a • g j) =
        a ^ 2 * lowNormalRealSchwartzH3Energy1 g := by
    unfold lowNormalRealSchwartzH3Energy1
    simp only [LineDeriv.lineDerivOp_smul, smul_apply, smul_eq_mul,
      mul_pow, integral_const_mul]
    simp only [← Finset.mul_sum]
  rw [hAmp, lowNormalRealSchwartzH3Energy1_dilation]
  have hn : t ≠ 0 := ne_of_gt ht
  field_simp [hn]


/-- The actual signed 243-slot first monomial scales like t¹⁷,
not like the quadratic dissipation. -/
theorem fixedKineticSchwartzConcentration_monomial_eq244
    (t : ℝ) (ht : 0 < t) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzPoint3Monomial
      (fixedKineticSchwartzConcentration244 t ht f) =
    t ^ 17 * lowNormalRealSchwartzPoint3Monomial f := by
  unfold fixedKineticSchwartzConcentration244
  rw [lowNormalRealSchwartzPoint3Monomial_real_smul,
    lowNormalRealSchwartzPoint3Monomial_dilation]
  ring

/-- The actual fourth-order viscosity square mass scales like t¹⁶. -/
theorem fixedKineticSchwartzConcentration_dissipation_eq244
    (t : ℝ) (ht : 0 < t) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3TopDissipation
      (fixedKineticSchwartzConcentration244 t ht f) =
    t ^ 16 * lowNormalRealSchwartzH3TopDissipation f := by
  unfold fixedKineticSchwartzConcentration244
  rw [lowNormalRealSchwartzH3TopDissipation_real_smul,
    lowNormalRealSchwartzH3TopDissipation_dilation]
  have hn : t ≠ 0 := ne_of_gt ht
  field_simp [hn]


/-- Pure scalar concentration step. The quadratic dissipation and kinetic
remainder cannot dominate a strictly positive cubic term after the coupled
rescaling. Keeping this algebra separate avoids elaborating Schwartz
integrals, derivative operators, and the quarter-packet construction while
normalizing the powers of the scale. -/
private theorem fixedKinetic_scalar_absorption_inequality244
    (M D E C K t : ℝ)
    (ht : 1 ≤ t)
    (hBudget : |C * D| + |K * E| < t * M) :
    C * (t ^ 16 * D) + K * E < t ^ 17 * M := by
  have htPow : 1 ≤ t ^ 16 := one_le_pow₀ ht
  have htPowNonneg : 0 ≤ t ^ 16 := le_trans zero_le_one htPow
  have htPowPos : 0 < t ^ 16 := lt_of_lt_of_le zero_lt_one htPow
  have hD : t ^ 16 * (C * D) ≤ t ^ 16 * |C * D| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) htPowNonneg
  have hE : K * E ≤ t ^ 16 * |K * E| := by
    calc
      K * E ≤ |K * E| := le_abs_self _
      _ = 1 * |K * E| := by ring
      _ ≤ t ^ 16 * |K * E| :=
        mul_le_mul_of_nonneg_right htPow (abs_nonneg _)
  calc
    C * (t ^ 16 * D) + K * E = t ^ 16 * (C * D) + K * E := by ring
    _ ≤ t ^ 16 * (|C * D| + |K * E|) := by
      calc
        _ ≤ t ^ 16 * |C * D| + t ^ 16 * |K * E| :=
          add_le_add hD hE
        _ = _ := by ring
    _ < t ^ 16 * (t * M) := mul_lt_mul_of_pos_left hBudget htPowPos
    _ = t ^ 17 * M := by ring

/-- This is the actual hard obstruction to a kinetic-anchor-only absorption.
On the entire class of real physical solenoidal Schwartz fields with E0 held
EXACTLY fixed, no fixed coefficients C and K can bound the positive signed
first monomial by C times fourth-order dissipation plus K times kinetic mass.
The witness is one coupled physical-space concentration family. -/
theorem fixedKineticSchwartzConcentration_exceeds_absorption244
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hM : 0 < lowNormalRealSchwartzPoint3Monomial f)
    (C K : ℝ) :
    ∃ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g ∧
      lowNormalRealSchwartzH3Energy0 g = lowNormalRealSchwartzH3Energy0 f ∧
      C * lowNormalRealSchwartzH3TopDissipation g +
        K * lowNormalRealSchwartzH3Energy0 g <
          lowNormalRealSchwartzPoint3Monomial g := by
  let M : ℝ := lowNormalRealSchwartzPoint3Monomial f
  let D : ℝ := lowNormalRealSchwartzH3TopDissipation f
  let E : ℝ := lowNormalRealSchwartzH3Energy0 f
  have hMpos : 0 < M := hM
  let t : ℝ := (|C * D| + |K * E| + 1) / M + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have htOne : 1 ≤ t := by
    dsimp [t]
    have hnonneg : 0 ≤ (|C * D| + |K * E| + 1) / M :=
      div_nonneg (by positivity) hMpos.le
    linarith
  have hBudget : |C * D| + |K * E| < t * M := by
    dsimp [t]
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hMpos), one_mul]
    linarith
  have hScalar : C * (t ^ 16 * D) + K * E < t ^ 17 * M :=
    fixedKinetic_scalar_absorption_inequality244 M D E C K t
      htOne hBudget
  let g : A3 → SchwartzMap V3 ℝ :=
    fixedKineticSchwartzConcentration244 t ht f
  have hSol : lowNormalRealSchwartz_Point3Solenoidal g :=
    fixedKineticSchwartzConcentration_solenoidal244 t ht f hDiv
  have hMass : lowNormalRealSchwartzH3Energy0 g = E :=
    fixedKineticSchwartzConcentration_energy0_eq244 t ht f
  have hTop : lowNormalRealSchwartzH3TopDissipation g = t ^ 16 * D :=
    fixedKineticSchwartzConcentration_dissipation_eq244 t ht f
  have hMon : lowNormalRealSchwartzPoint3Monomial g = t ^ 17 * M :=
    fixedKineticSchwartzConcentration_monomial_eq244 t ht f
  have hAbsorb :
      C * lowNormalRealSchwartzH3TopDissipation g +
        K * lowNormalRealSchwartzH3Energy0 g <
          lowNormalRealSchwartzPoint3Monomial g := by
    calc
      C * lowNormalRealSchwartzH3TopDissipation g +
          K * lowNormalRealSchwartzH3Energy0 g =
          C * (t ^ 16 * D) + K * E := by rw [hTop, hMass]
      _ < t ^ 17 * M := hScalar
      _ = lowNormalRealSchwartzPoint3Monomial g := hMon.symm
  exact ⟨g, hSol, hMass, hAbsorb⟩

/-- The original noncancelling quarter packet meets the actual Point3
solenoidal predicate. This turns the parametric fixed-kinetic obstruction
into an unconditional physical Schwartz witness. -/
theorem lowNormalQuarterOppositeSchwartz_Point3Solenoidal244
    (ρ : ℝ) (hρ : 0 < ρ) :
    lowNormalRealSchwartz_Point3Solenoidal
      (lowNormalQuarterOppositeSchwartzVelocity ρ hρ) := by
  intro x
  have hComplex := lowNormalQuarterOppositeSchwartz_physical_divergence
    ρ hρ (h3Point3ToFourierCLM x)
  simp only [← SchwartzMap.lineDerivOp_apply_eq_fderiv,
    h3TriadComplexify_lineDeriv, h3SchwartzComplexify_apply] at hComplex
  have hReal :
      (∑ j : A3,
        (∂_{h3FourierAxisDirection j}
          (lowNormalQuarterOppositeSchwartzVelocity ρ hρ j))
            (h3Point3ToFourierCLM x)) = (0 : ℝ) := by
    have hRe := congrArg Complex.reCLM hComplex
    simpa only [map_sum, Complex.reCLM_apply,
      Complex.ofReal_re, map_zero] using hRe
  simpa only [h3SchwartzPoint3Scalar_spatial_d, h3SchwartzPoint3Scalar]
    using hReal

/-- A completely unconditional, explicitly packet-realized obstruction:
for every pair of proposed coefficients, one REAL Point3-solenoidal
Schwartz velocity has the SAME E0 as the base packet but violates the
proposed dissipation-plus-kinetic bound for the signed 243-slot monomial. -/
theorem lowNormalQuarter_exists_fixedKinetic_absorption_counterexample244
    (C K : ℝ) :
    ∃ f g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal f ∧
      lowNormalRealSchwartz_Point3Solenoidal g ∧
      0 < lowNormalRealSchwartzPoint3Monomial f ∧
      lowNormalRealSchwartzH3Energy0 g = lowNormalRealSchwartzH3Energy0 f ∧
      C * lowNormalRealSchwartzH3TopDissipation g +
        K * lowNormalRealSchwartzH3Energy0 g <
          lowNormalRealSchwartzPoint3Monomial g := by
  obtain ⟨ρ, hρ, _, hM⟩ :=
    lowNormalQuarterPoint3_exists_both_firstMonomial_signs
  let f : A3 → SchwartzMap V3 ℝ :=
    lowNormalQuarterOppositeSchwartzVelocity ρ hρ
  have hDiv : lowNormalRealSchwartz_Point3Solenoidal f :=
    lowNormalQuarterOppositeSchwartz_Point3Solenoidal244 ρ hρ
  obtain ⟨g, hgDiv, hgE0, hgBound⟩ :=
    fixedKineticSchwartzConcentration_exceeds_absorption244
      f hDiv hM C K
  exact ⟨f, g, hDiv, hgDiv, hM, hgE0, hgBound⟩

end
end PrimeTensor.FirstMonomialTriad
