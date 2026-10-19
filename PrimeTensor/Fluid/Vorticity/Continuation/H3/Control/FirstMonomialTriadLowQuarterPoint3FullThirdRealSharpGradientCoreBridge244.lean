import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSharpInterpolationCenters244
import Mathlib.Tactic

/-!
# The actual five-index physical gradient core at coherent sharp centers

The true real Schwartz commutator has a cutoff-free physical polynomial,
formed from all four 3+3+1 slots, all five axis sums and the true 3+2+2
interpolation contribution. The interpolation core's sharp-center bridge
has already been proved. Here we supply the missing *gradient* bridge.

At an actual coherent sharp center the dependent Fourier momentum is
itself the remaining center. Exact transverse fixed-center germs then equal
the prescribed real polarizations. We propagate that identity through the
complete four-pattern gradient axis block and all five finite axis sums.
The resulting sharp polynomial still contains the original physical seven-
derivative gradient multiplier evaluated at the genuine Hilbert frequencies.
It is NOT replaced by the old six-permutation surrogate.

These exact identities do not yet evaluate the five-index sharp polynomial
numerically and do not assert the sign of its variable-frequency integral.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev PairV244 := H3FourierPoint3 × H3FourierPoint3

noncomputable local instance axisFintypeSharpGradientBridge244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- A literal sharp four-pattern axis block: seven REAL Fourier derivative
weights of the physical gradient and three prescribed polarizations. The
four contractions correspond in order to the four original gradient slots.
There is no window and no frequency-dependent transverse germ here. -/
noncomputable def thirdFullSharpPhysicalGradientAxis244
    (z : PairV244) (U V W : Freq244) (j i k l t : A3) : ℝ :=
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection t
  2 * (((
    (thirdFullGradientSevenWeight244 a b c a b c d z).re *
      ((U j * V t) * W j) +
    (thirdFullGradientSevenWeight244 a b c a b d c z).re *
      ((U j * V j) * W t)) +
    (thirdFullGradientSevenWeight244 a b c a d c b z).re *
      ((U j * V j) * W t)) +
    (thirdFullGradientSevenWeight244 a b c d b c a z).re *
      ((U j * V j) * W t))

/-- Full five-index sharp physical 3+3+1 gradient polynomial, with the
literal physical factor TWO and all four differentiated contractions. -/
noncomputable def thirdFullSharpPhysicalGradientFive244
    (z : PairV244) (U V W : Freq244) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ t : A3,
    thirdFullSharpPhysicalGradientAxis244 z U V W j i k l t

/-- Complete sharp physical polynomial for ONE ordered center, including
the true 3+2+2 interpolation contraction with its physical factor six. -/
noncomputable def thirdFullSharpPhysicalOrderedCore244
    (z : PairV244) (p q r U V W : Freq244) : ℝ :=
  thirdFullSharpPhysicalGradientFive244 z U V W +
    6 * thirdFullSharpInterpolationOrdered244 p q r U V W

/-- Every component of the THREE actual cutoff-free Fourier germs agrees
with the sharp polarization on the coherent center. This includes the
dependent middle momentum q=-p-r, not just the independent p and r. -/
theorem thirdFullPositiveSectorBareTriple_at_center244
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hp : WithLp.ofLp z.1 =
      thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).1)
    (hr : WithLp.ofLp z.2 =
      thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).2)
    (hq : thirdFullMiddleFrequency244
      (thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).1,
       thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).2) =
        thirdFullAxisSixCenter244 (thirdFullPositiveMiddleLabel244 n))
    (hTrans : ∀ i : Fin 6, (i = 0 ∨ i = 1 ∨ i = 2) →
      thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
        (thirdFullPositiveWindowPolarization244 A B C i) = 0)
    (hNonzero : ∀ i : Fin 6,
      thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
        (thirdFullAxisSixCenter244 i) ≠ 0)
    (a b c : A3) :
    thirdFullPositiveSectorBareTriple244 A B C n z a b c =
      (thirdFullPositiveWindowPolarization244 A B C
        (lowNormalQuarterCoherentLabelPair false n).1 a *
       thirdFullPositiveWindowPolarization244 A B C
        (thirdFullPositiveMiddleLabel244 n) b) *
      thirdFullPositiveWindowPolarization244 A B C
        (lowNormalQuarterCoherentLabelPair false n).2 c := by
  unfold thirdFullPositiveSectorBareTriple244
  dsimp only
  rw [hp, hr, hq]
  have hLabels := thirdFullPositiveLabels_primary244 n
  rw [thirdFullPositiveSectorBareGerm_at_center244 A B C _
       (hTrans _ hLabels.1) (hNonzero _),
      thirdFullPositiveSectorBareGerm_at_center244 A B C _
       (hTrans _ hLabels.2.1) (hNonzero _),
      thirdFullPositiveSectorBareGerm_at_center244 A B C _
       (hTrans _ hLabels.2.2) (hNonzero _)]

/-- At each sharp center, the TRUE gradient-axis core is exactly the sharp
four-slot physical polynomial, not a selected sharp monomial. -/
theorem thirdFullPositiveSectorGradientAxisCore_at_center244
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hp : WithLp.ofLp z.1 =
      thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).1)
    (hr : WithLp.ofLp z.2 =
      thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).2)
    (hq : thirdFullMiddleFrequency244
      (thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).1,
       thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).2) =
        thirdFullAxisSixCenter244 (thirdFullPositiveMiddleLabel244 n))
    (hTrans : ∀ i : Fin 6, (i = 0 ∨ i = 1 ∨ i = 2) →
      thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
        (thirdFullPositiveWindowPolarization244 A B C i) = 0)
    (hNonzero : ∀ i : Fin 6,
      thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
        (thirdFullAxisSixCenter244 i) ≠ 0)
    (j i k l t : A3) :
    thirdFullPositiveSectorGradientAxisCore244 A B C n z j i k l t =
      thirdFullSharpPhysicalGradientAxis244 z
        (thirdFullPositiveWindowPolarization244 A B C
          (lowNormalQuarterCoherentLabelPair false n).1)
        (thirdFullPositiveWindowPolarization244 A B C
          (thirdFullPositiveMiddleLabel244 n))
        (thirdFullPositiveWindowPolarization244 A B C
          (lowNormalQuarterCoherentLabelPair false n).2)
        j i k l t := by
  unfold thirdFullPositiveSectorGradientAxisCore244
    thirdFullSharpPhysicalGradientAxis244
  dsimp only
  simp only [thirdFullPositiveSectorBareTriple_at_center244
    A B C n z hp hr hq hTrans hNonzero]

/-- Exact center evaluation of the full five-index gradient core. Every
five-index physical term is retained, with its original derivative order. -/
theorem thirdFullPositiveSectorGradientTotalCore_at_center244
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hp : WithLp.ofLp z.1 =
      thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).1)
    (hr : WithLp.ofLp z.2 =
      thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).2)
    (hq : thirdFullMiddleFrequency244
      (thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).1,
       thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).2) =
        thirdFullAxisSixCenter244 (thirdFullPositiveMiddleLabel244 n))
    (hTrans : ∀ i : Fin 6, (i = 0 ∨ i = 1 ∨ i = 2) →
      thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
        (thirdFullPositiveWindowPolarization244 A B C i) = 0)
    (hNonzero : ∀ i : Fin 6,
      thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
        (thirdFullAxisSixCenter244 i) ≠ 0) :
    thirdFullPositiveSectorGradientTotalCore244 A B C n z =
      thirdFullSharpPhysicalGradientFive244 z
        (thirdFullPositiveWindowPolarization244 A B C
          (lowNormalQuarterCoherentLabelPair false n).1)
        (thirdFullPositiveWindowPolarization244 A B C
          (thirdFullPositiveMiddleLabel244 n))
        (thirdFullPositiveWindowPolarization244 A B C
          (lowNormalQuarterCoherentLabelPair false n).2) := by
  unfold thirdFullPositiveSectorGradientTotalCore244
    thirdFullSharpPhysicalGradientFive244
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro t _
  exact thirdFullPositiveSectorGradientAxisCore_at_center244
    A B C n z hp hr hq hTrans hNonzero j i k l t

/-- Exact sharp-center representation of the COMPLETE cutoff-free physical
H3 kernel polynomial: gradient plus interpolation, without a sign claim.
The only assumptions are actual center matching and center transversality. -/
theorem thirdFullPositiveSectorPhysicalCore_at_center244
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hp : WithLp.ofLp z.1 =
      thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).1)
    (hr : WithLp.ofLp z.2 =
      thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).2)
    (hq : thirdFullMiddleFrequency244
      (thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).1,
       thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).2) =
        thirdFullAxisSixCenter244 (thirdFullPositiveMiddleLabel244 n))
    (hTrans : ∀ i : Fin 6, (i = 0 ∨ i = 1 ∨ i = 2) →
      thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
        (thirdFullPositiveWindowPolarization244 A B C i) = 0)
    (hNonzero : ∀ i : Fin 6,
      thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
        (thirdFullAxisSixCenter244 i) ≠ 0) :
    thirdFullPositiveSectorPhysicalCore244 A B C n z =
      thirdFullSharpPhysicalOrderedCore244 z
        (thirdFullAxisSixCenter244
          (lowNormalQuarterCoherentLabelPair false n).1)
        (thirdFullAxisSixCenter244 (thirdFullPositiveMiddleLabel244 n))
        (thirdFullAxisSixCenter244
          (lowNormalQuarterCoherentLabelPair false n).2)
        (thirdFullPositiveWindowPolarization244 A B C
          (lowNormalQuarterCoherentLabelPair false n).1)
        (thirdFullPositiveWindowPolarization244 A B C
          (thirdFullPositiveMiddleLabel244 n))
        (thirdFullPositiveWindowPolarization244 A B C
          (lowNormalQuarterCoherentLabelPair false n).2) := by
  unfold thirdFullPositiveSectorPhysicalCore244
    thirdFullSharpPhysicalOrderedCore244
  rw [thirdFullPositiveSectorGradientTotalCore_at_center244
    A B C n z hp hr hq hTrans hNonzero,
    thirdFullPositiveSectorInterpolationCore_at_center244
      A B C n z hp hr hq hTrans hNonzero]

end
end PrimeTensor.FirstMonomialTriad
