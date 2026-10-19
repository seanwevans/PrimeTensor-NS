import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSharpSixPhysicalCenterValues244
import Mathlib.Tactic

/-!
# Exact moving-germ physical orbit and its signed local tube

The full five-index contraction has now been proved for the sharp physical
core. The first theorem below applies that contraction at *arbitrary*
Fourier frequencies in the actual cutoff-free sector polynomial: the
three transverse germs are evaluated at their own moving momenta.
There is no sector, mass, or center hypothesis in this algebraic result.

We then sum six **physical ordered cores** over the six simultaneous
permutations of one momentum-conserving triad. This orbit is proved equal
to the already established projected Hermitian kernel, with an already established
open negative neighborhood. This is a sign theorem for the symmetrized
cutoff-free physical orbit, NOT yet a sign for any one sector or for the
actual six sector integrals. An integral-level permutation transport of
the three compact Schwartz windows remains necessary.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev PairV244 := H3FourierPoint3 × H3FourierPoint3
private abbrev PairFreq244 := Freq244 × Freq244

noncomputable local instance axisFintypeVariableSixOrbit244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- No center specialization is required to identify the actual bare
physical polynomial with the sharp *form* of the four gradient slots
plus interpolation: the three polarizations may vary independently
with all three momenta. -/
theorem thirdFullPositiveSectorPhysicalCore_eq_sharp_form_variable244
    (A B C : Freq244) (n : Fin 6) (z : PairV244) :
    let p : Freq244 := WithLp.ofLp z.1
    let r : Freq244 := WithLp.ofLp z.2
    let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
    let labels := lowNormalQuarterCoherentLabelPair false n
    let middle := thirdFullPositiveMiddleLabel244 n
    let U := thirdFullPositiveSectorBareGerm244 A B C labels.1 p
    let V := thirdFullPositiveSectorBareGerm244 A B C middle q
    let W := thirdFullPositiveSectorBareGerm244 A B C labels.2 r
    thirdFullPositiveSectorPhysicalCore244 A B C n z =
      thirdFullSharpPhysicalOrderedCore244 z p q r U V W := by
  -- The source definitions have identical four seven-derivative terms
  -- and the same two bilinear interpolation contractions.
  rfl

/-- Every actual cutoff-free variable-frequency positive-sector polynomial
is twice the corrected physical ordered symbol with THREE distinct
moving, divergence-free transverse germs. No sector support or nonzero
Fourier triple mass is required for this algebraic identity. -/
theorem thirdFullPositiveSectorPhysicalCore_eq_twice_corrected_variable244
    (A B C : Freq244) (n : Fin 6) (z : PairV244) :
    let p : Freq244 := WithLp.ofLp z.1
    let r : Freq244 := WithLp.ofLp z.2
    let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
    let labels := lowNormalQuarterCoherentLabelPair false n
    let middle := thirdFullPositiveMiddleLabel244 n
    let U := thirdFullPositiveSectorBareGerm244 A B C labels.1 p
    let V := thirdFullPositiveSectorBareGerm244 A B C middle q
    let W := thirdFullPositiveSectorBareGerm244 A B C labels.2 r
    thirdFullPositiveSectorPhysicalCore244 A B C n z =
      2 * thirdFullPhysicalOrderedSymbol244 p q r U V W := by
  have hForm := thirdFullPositiveSectorPhysicalCore_eq_sharp_form_variable244
    A B C n z
  dsimp only at hForm ⊢
  rw [hForm]
  exact thirdFullSharpPhysicalOrderedCore_eq_twice_corrected244
    z _ _ _ _ _ _ rfl
      ((thirdFullMiddleFrequency_ofLp_pair244 z).symm) rfl

/-- The complete corrected six-permutation orbit, evaluated using the
**genuine five-index gradient plus interpolation core** at each ordered
frequency triple. The normalized solenoidal germs vary at their own
momenta; there are no compact cutoff factors in this orbit. -/
noncomputable def thirdFullSharpProjectedPhysicalSixOrbit244
    (p₀ q₀ r₀ A B C : Freq244) (z : PairFreq244) : ℝ :=
  let p := z.1
  let q := thirdFullMiddleFrequency244 z
  let r := z.2
  let U := thirdFullFixedCenterTransverseGerm244 p₀ p A
  let V := thirdFullFixedCenterTransverseGerm244 q₀ q B
  let W := thirdFullFixedCenterTransverseGerm244 r₀ r C
  thirdFullSharpPhysicalOrderedAt244 p q r U V W +
  thirdFullSharpPhysicalOrderedAt244 p r q U W V +
  thirdFullSharpPhysicalOrderedAt244 q p r V U W +
  thirdFullSharpPhysicalOrderedAt244 q r p V W U +
  thirdFullSharpPhysicalOrderedAt244 r p q W U V +
  thirdFullSharpPhysicalOrderedAt244 r q p W V U

/-- The six genuine physical ordered cores coincide with the existing
projected Hermitian kernel at every momentum pair, not only at the sharp
center. Consequently all old local continuity and negativity estimates
apply to this newly identified physical five-index orbit. -/
theorem thirdFullSharpProjectedPhysicalSixOrbit_eq_hermitian244
    (p₀ q₀ r₀ A B C : Freq244) (z : PairFreq244) :
    thirdFullSharpProjectedPhysicalSixOrbit244 p₀ q₀ r₀ A B C z =
      thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z := by
  let p : Freq244 := z.1
  let q : Freq244 := thirdFullMiddleFrequency244 z
  let r : Freq244 := z.2
  let U := thirdFullFixedCenterTransverseGerm244 p₀ p A
  let V := thirdFullFixedCenterTransverseGerm244 q₀ q B
  let W := thirdFullFixedCenterTransverseGerm244 r₀ r C
  have hm : ∀ i : A3, p i + q i + r i = 0 := by
    intro i
    dsimp [p, q, r, thirdFullMiddleFrequency244]
    ring
  have hmPRQ : ∀ i : A3, p i + r i + q i = 0 := by
    intro i; have h := hm i; linarith
  have hmQPR : ∀ i : A3, q i + p i + r i = 0 := by
    intro i; have h := hm i; linarith
  have hmQRP : ∀ i : A3, q i + r i + p i = 0 := by
    intro i; have h := hm i; linarith
  have hmRPQ : ∀ i : A3, r i + p i + q i = 0 := by
    intro i; have h := hm i; linarith
  have hmRQP : ∀ i : A3, r i + q i + p i = 0 := by
    intro i; have h := hm i; linarith
  have hOrbit :
      thirdFullSharpProjectedPhysicalSixOrbit244 p₀ q₀ r₀ A B C z =
        2 * thirdFullPhysicalSixSymbol244 p q r U V W := by
    dsimp only [thirdFullSharpProjectedPhysicalSixOrbit244]
    rw [thirdFullSharpPhysicalOrderedAt_twice_corrected244
          p q r U V W hm,
        thirdFullSharpPhysicalOrderedAt_twice_corrected244
          p r q U W V hmPRQ,
        thirdFullSharpPhysicalOrderedAt_twice_corrected244
          q p r V U W hmQPR,
        thirdFullSharpPhysicalOrderedAt_twice_corrected244
          q r p V W U hmQRP,
        thirdFullSharpPhysicalOrderedAt_twice_corrected244
          r p q W U V hmRPQ,
        thirdFullSharpPhysicalOrderedAt_twice_corrected244
          r q p W V U hmRQP]
    unfold thirdFullPhysicalSixSymbol244
    ring
  calc
    _ = 2 * thirdFullPhysicalSixSymbol244 p q r U V W := hOrbit
    _ = thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z := by
      unfold thirdFullProjectedHermitianKernel244
      rw [thirdFullHermitianMomentumKernel_eq244]

/-- The six-term physical five-index orbit is continuous with the ACTUAL
frequency-varying solenoidal germs. -/
theorem thirdFullSharpProjectedPhysicalSixOrbit_continuous244
    (p₀ q₀ r₀ A B C : Freq244) :
    Continuous (thirdFullSharpProjectedPhysicalSixOrbit244 p₀ q₀ r₀ A B C) := by
  have hEq : thirdFullSharpProjectedPhysicalSixOrbit244 p₀ q₀ r₀ A B C =
      thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C := by
    funext z
    exact thirdFullSharpProjectedPhysicalSixOrbit_eq_hermitian244
      p₀ q₀ r₀ A B C z
  rw [hEq]
  exact thirdFullProjectedHermitianKernel_continuous244 p₀ q₀ r₀ A B C

/-- A whole positive-radius closed momentum-pair ball has strictly
negative *six-term physical core orbit*. Mixed signs in the six individual
ordered summands are allowed and, at the sharp center, unavoidable.
This is not yet a negative statement about the six WINDOWED integrals. -/
theorem thirdFullSharpProjectedPhysicalSixOrbit_exists_negative_tube244 :
    ∃ (p q r A B C : Freq244) (ρ : ℝ),
      (∀ i, p i + q i + r i = 0) ∧
      thirdTriadAxisDot244 A p = 0 ∧
      thirdTriadAxisDot244 B q = 0 ∧
      thirdTriadAxisDot244 C r = 0 ∧
      0 < ρ ∧
      (∀ z ∈ Metric.closedBall (p, r) ρ,
        thirdFullSharpProjectedPhysicalSixOrbit244 p q r A B C z < 0) := by
  obtain ⟨p, q, r, A, B, C, ρ, hm, ha, hb, hc, hρ, hNeg⟩ :=
    thirdFullProjectedHermitianKernel_exists_solenoidal_negative_tube244
  refine ⟨p, q, r, A, B, C, ρ, hm, ha, hb, hc, hρ, ?_⟩
  intro z hz
  rw [thirdFullSharpProjectedPhysicalSixOrbit_eq_hermitian244]
  exact hNeg z hz

end
end PrimeTensor.FirstMonomialTriad
