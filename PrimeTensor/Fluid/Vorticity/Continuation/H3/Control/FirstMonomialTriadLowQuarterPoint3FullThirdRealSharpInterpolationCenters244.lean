import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSectorWindowFactor244
import Mathlib.Tactic

/-!
# The six sharp interpolation values and the genuine center-germ bridge

The three-window physical polynomial is now cutoff-free. The genuine 3+2+2
interpolation contribution can be calculated at the sharp solenoidal triad
without mistaking its individual ordered signs for a uniform sign. These
SIX signed ordered interpolation coefficients add to zero, although several
of them are nonzero. The calculation is kept separate from the still-open
five-index gradient-center identification.

The bridge lemma below uses the ACTUAL cutoff-free interpolation core and
fixed-center transverse germs. It shows exactly when a sharp coefficient
can be substituted for that core: all three evaluation frequencies must
be the corresponding centers, and center transversality and nonvanishing
must be supplied. No localization or total-integral sign is assumed.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev PairV244 := H3FourierPoint3 × H3FourierPoint3

noncomputable local instance axisFintypeSharpInterpolation244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Ordered 3+2+2 contraction from the actual `complexCoefficient` and
`amplitudeDot` formula, with NO Fourier phase and NO scalar window. -/
noncomputable def thirdFullSharpInterpolationOrdered244
    (p q r A B C : Freq244) : ℝ :=
  dot p r * (dot p q) ^ 2 * dot r B * dot A C

/-- A real three-coordinate function on the physical positive-depth axis. -/
private def thirdFullSharpCoord244 (x y z : ℝ) (i : A3) : ℝ :=
  if axisRank i = 0 then x else if axisRank i = 1 then y else z

private theorem thirdFullSharpCoord_dot244
    (x y z u v w : ℝ) :
    dot (thirdFullSharpCoord244 x y z)
      (thirdFullSharpCoord244 u v w) = x * u + y * v + z * w := by
  unfold dot
  rw [axis_sum_three]
  norm_num [thirdFullSharpCoord244, axisRank, xAxis, yAxis, zAxis]
  ring

/-- The same sharp geometry used by the original corrected -192 orbit. -/
def thirdFullSharpP244 : Freq244 := thirdFullSharpCoord244 1 0 0
def thirdFullSharpQ244 : Freq244 := thirdFullSharpCoord244 1 1 0
def thirdFullSharpR244 : Freq244 := thirdFullSharpCoord244 (-2) (-1) 0
def thirdFullSharpA244 : Freq244 := thirdFullSharpCoord244 0 1 0
def thirdFullSharpB244 : Freq244 := thirdFullSharpCoord244 1 (-1) 0
def thirdFullSharpC244 : Freq244 := thirdFullSharpCoord244 1 (-2) 0

/-- All six TRUE interpolation orders at the specific sharp real witness.
The order is (p,q,r), (r,q,p), (q,p,r), (r,p,q), (q,r,p), (p,r,q),
matching `lowNormalQuarterCoherentLabelPair false n` with its middle label. -/
theorem thirdFullSharpInterpolation_six_values244 :
    thirdFullSharpInterpolationOrdered244
      thirdFullSharpP244 thirdFullSharpQ244 thirdFullSharpR244
      thirdFullSharpA244 thirdFullSharpB244 thirdFullSharpC244 = -4 ∧
    thirdFullSharpInterpolationOrdered244
      thirdFullSharpR244 thirdFullSharpQ244 thirdFullSharpP244
      thirdFullSharpC244 thirdFullSharpB244 thirdFullSharpA244 = 36 ∧
    thirdFullSharpInterpolationOrdered244
      thirdFullSharpQ244 thirdFullSharpP244 thirdFullSharpR244
      thirdFullSharpB244 thirdFullSharpA244 thirdFullSharpC244 = 9 ∧
    thirdFullSharpInterpolationOrdered244
      thirdFullSharpR244 thirdFullSharpP244 thirdFullSharpQ244
      thirdFullSharpC244 thirdFullSharpA244 thirdFullSharpB244 = -36 ∧
    thirdFullSharpInterpolationOrdered244
      thirdFullSharpQ244 thirdFullSharpR244 thirdFullSharpP244
      thirdFullSharpB244 thirdFullSharpC244 thirdFullSharpA244 = -9 ∧
    thirdFullSharpInterpolationOrdered244
      thirdFullSharpP244 thirdFullSharpR244 thirdFullSharpQ244
      thirdFullSharpA244 thirdFullSharpC244 thirdFullSharpB244 = 4 := by
  simp only [thirdFullSharpInterpolationOrdered244,
    thirdFullSharpP244, thirdFullSharpQ244, thirdFullSharpR244,
    thirdFullSharpA244, thirdFullSharpB244, thirdFullSharpC244,
    thirdFullSharpCoord_dot244]
  norm_num

/-- The six interpolation orders are signed, not uniformly negative; their
sum cancels at the sharp triad. This says NOTHING by itself about integrals
with nonconstant transverse germs and genuinely shifted Fourier windows. -/
theorem thirdFullSharpInterpolation_six_sum_zero244 :
    thirdFullSharpInterpolationOrdered244
      thirdFullSharpP244 thirdFullSharpQ244 thirdFullSharpR244
      thirdFullSharpA244 thirdFullSharpB244 thirdFullSharpC244 +
    thirdFullSharpInterpolationOrdered244
      thirdFullSharpR244 thirdFullSharpQ244 thirdFullSharpP244
      thirdFullSharpC244 thirdFullSharpB244 thirdFullSharpA244 +
    thirdFullSharpInterpolationOrdered244
      thirdFullSharpQ244 thirdFullSharpP244 thirdFullSharpR244
      thirdFullSharpB244 thirdFullSharpA244 thirdFullSharpC244 +
    thirdFullSharpInterpolationOrdered244
      thirdFullSharpR244 thirdFullSharpP244 thirdFullSharpQ244
      thirdFullSharpC244 thirdFullSharpA244 thirdFullSharpB244 +
    thirdFullSharpInterpolationOrdered244
      thirdFullSharpQ244 thirdFullSharpR244 thirdFullSharpP244
      thirdFullSharpB244 thirdFullSharpC244 thirdFullSharpA244 +
    thirdFullSharpInterpolationOrdered244
      thirdFullSharpP244 thirdFullSharpR244 thirdFullSharpQ244
      thirdFullSharpA244 thirdFullSharpC244 thirdFullSharpB244 = 0 := by
  rcases thirdFullSharpInterpolation_six_values244 with
    ⟨h0, h1, h2, h3, h4, h5⟩
  rw [h0, h1, h2, h3, h4, h5]
  norm_num

/-- An actual cutoff-free transverse germ becomes exactly its original
polarization, not a merely proportional vector, at its nonzero center. -/
theorem thirdFullPositiveSectorBareGerm_at_center244
    (A B C : Freq244) (i : Fin 6)
    (hTrans : thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
      (thirdFullPositiveWindowPolarization244 A B C i) = 0)
    (hNonzero : thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
      (thirdFullAxisSixCenter244 i) ≠ 0) :
    thirdFullPositiveSectorBareGerm244 A B C i
      (thirdFullAxisSixCenter244 i) =
        thirdFullPositiveWindowPolarization244 A B C i := by
  exact thirdFullFixedCenterTransverseGerm_at_center244
    (thirdFullAxisSixCenter244 i)
    (thirdFullPositiveWindowPolarization244 A B C i) hTrans hNonzero

/-- The third entry of each sharp frequency vector is definitionally
zero; use this after reducing the six center labels to literal vectors. -/
private theorem thirdFullSharpVec_last_zero244 (x y : ℝ) :
    (![x, y, (0 : ℝ)] : Fin 3 → ℝ) 2 = 0 := by
  rfl

/-- The dependent middle frequency of every positive sharp-center pair is
literally the remaining sharp center. This is finite integer lattice
arithmetic transported to the actual physical Axis carrier. -/
theorem thirdFullPositiveSector_center_resonance244 (n : Fin 6) :
    thirdFullMiddleFrequency244
      (thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).1,
       thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).2) =
    thirdFullAxisSixCenter244 (thirdFullPositiveMiddleLabel244 n) := by
  funext d
  -- `Axis Depth.three` is a recursive positive-depth axis, not `Fin 3`.
  -- Eliminate its three constructors as in `thirdFullPhysicalTriad_solenoidal244`.
  -- Each remaining case is closed by the six literal lattice identities.
  cases d with
  | first =>
      fin_cases n <;>
        norm_num [thirdFullMiddleFrequency244,
          thirdFullAxisSixCenter244, thirdFullPositiveMiddleLabel244,
          lowNormalQuarterCoherentLabelPair,
          lowNormalSixCenter, lowNormalLatticeEmbedding,
          lowNormalSignedLatticeCenter, axisRank, xAxis, yAxis, zAxis]
  | next d =>
      cases d with
      | first =>
          fin_cases n <;>
            norm_num [thirdFullMiddleFrequency244,
              thirdFullAxisSixCenter244, thirdFullPositiveMiddleLabel244,
              lowNormalQuarterCoherentLabelPair,
              lowNormalSixCenter, lowNormalLatticeEmbedding,
              lowNormalSignedLatticeCenter, axisRank, xAxis, yAxis, zAxis]
      | next d =>
          cases d with
          | first =>
              fin_cases n <;>
                norm_num [thirdFullMiddleFrequency244,
                  thirdFullAxisSixCenter244, thirdFullPositiveMiddleLabel244,
                  lowNormalQuarterCoherentLabelPair,
                  lowNormalSixCenter, lowNormalLatticeEmbedding,
                  lowNormalSignedLatticeCenter, axisRank, xAxis, yAxis, zAxis] <;>
                simp only [thirdFullSharpVec_last_zero244] <;>
                norm_num

/-- Exactly the ACTUAL interpolation core at a coherent sharp triple;
no six-symbol surrogate is substituted. All three center equalities,
transversality and nonvanishing are explicit. -/
theorem thirdFullPositiveSectorInterpolationCore_at_center244
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
    thirdFullPositiveSectorInterpolationCore244 A B C n z =
      thirdFullSharpInterpolationOrdered244
        (thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).1)
        (thirdFullAxisSixCenter244 (thirdFullPositiveMiddleLabel244 n))
        (thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).2)
        (thirdFullPositiveWindowPolarization244 A B C
          (lowNormalQuarterCoherentLabelPair false n).1)
        (thirdFullPositiveWindowPolarization244 A B C
          (thirdFullPositiveMiddleLabel244 n))
        (thirdFullPositiveWindowPolarization244 A B C
          (lowNormalQuarterCoherentLabelPair false n).2) := by
  unfold thirdFullPositiveSectorInterpolationCore244
    thirdFullSharpInterpolationOrdered244
  dsimp only
  rw [hp, hr, hq]
  have hLabels := thirdFullPositiveLabels_primary244 n
  rw [thirdFullPositiveSectorBareGerm_at_center244 A B C _
       (hTrans _ hLabels.2.1) (hNonzero _),
      thirdFullPositiveSectorBareGerm_at_center244 A B C _
       (hTrans _ hLabels.1) (hNonzero _),
      thirdFullPositiveSectorBareGerm_at_center244 A B C _
       (hTrans _ hLabels.2.2) (hNonzero _)]

end
end PrimeTensor.FirstMonomialTriad
