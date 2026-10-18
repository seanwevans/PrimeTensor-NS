import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSixPermutationSymbol244
import Mathlib.Tactic

/-!
# Corrected physical third-commutator symbol and Hermitian Fourier-phase orbit

The OLD ordered polynomial was not a literal single-order gradient symbol:
its three last gradient terms use a different velocity-polarization pairing
from the first gradient term. This module corrects that difference exactly.

The corrected ordered polynomial is
 (A·C)(B·r) (a³+3a²b) + 3(A·B)(C·q) a²b,
 where a=p·q and b=p·r.

The corrected and previously audited six-permutation polynomials agree:
their differences cancel pairwise under q/r exchange, for EVERY triad and
EVERY polarization, without incompressibility assumptions.

For the physical solenoidal witness the SIX CORRECTED ordered values are
 -16, 28, 33, -81, -60, 0, with total -96.

We also account for the actual odd Fourier-derivative phase I^7 and the
Hermitian reflected orbit. A complex polarization-product phase z=I makes
the phase/reflection sum -192. The physical 2(2π)^7 prefactor can be applied.

IMPORTANT: these are polynomial and finite-Hermitian-orbit identities.
This file does NOT assert the Schwartz Fourier integral equals the orbit sum,
or that a Schwartz packet localizes to this triad. Those require independent
analytic localization and a Fourier bridge for the full gradient functional.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 500000

private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeFullThirdPhase244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- One ordered symbol with the EXACT gradient-component contractions:
the first gradient term and all three interpolation terms have (A·C)(B·r),
but the last three gradient terms have (A·B)(C·q). -/
noncomputable def thirdFullPhysicalOrderedSymbol244
    (p q r A B C : A3 → ℝ) : ℝ :=
  let a := thirdTriadAxisDot244 p q
  let b := thirdTriadAxisDot244 p r
  (thirdTriadAxisDot244 A C * thirdTriadAxisDot244 B r) *
      (a ^ 3 + 3 * a ^ 2 * b) +
    (thirdTriadAxisDot244 A B * thirdTriadAxisDot244 C q) *
      (3 * a ^ 2 * b)

/-- Exact paired equality: swapping only the second and third modes restores
the old algebraic symbol after summation, though each OLD ordered value was
not itself the physical gradient contribution. -/
theorem thirdFullPhysicalOrdered_pair_eq_old244
    (p q r A B C : A3 → ℝ) :
    thirdFullPhysicalOrderedSymbol244 p q r A B C +
      thirdFullPhysicalOrderedSymbol244 p r q A C B =
    thirdFullOrderedTriadRealSymbol244 p q r A B C +
      thirdFullOrderedTriadRealSymbol244 p r q A C B := by
  unfold thirdFullPhysicalOrderedSymbol244
  rw [thirdFullOrderedTriadRealSymbol_eq244,
    thirdFullOrderedTriadRealSymbol_eq244]
  ring

/-- All six simultaneous permutations, with each ordering's correct velocity
polarizations, before any conjugate reflection or integration. -/
noncomputable def thirdFullPhysicalSixSymbol244
    (p q r A B C : A3 → ℝ) : ℝ :=
  thirdFullPhysicalOrderedSymbol244 p q r A B C +
  thirdFullPhysicalOrderedSymbol244 p r q A C B +
  thirdFullPhysicalOrderedSymbol244 q p r B A C +
  thirdFullPhysicalOrderedSymbol244 q r p B C A +
  thirdFullPhysicalOrderedSymbol244 r p q C A B +
  thirdFullPhysicalOrderedSymbol244 r q p C B A

/-- Exact six-orbit equality, without solenoidality or momentum assumptions.
The first-order symbol error does NOT affect the fully symmetrized result. -/
theorem thirdFullPhysicalSix_eq_prior_six244
    (p q r A B C : A3 → ℝ) :
    thirdFullPhysicalSixSymbol244 p q r A B C =
      thirdFullSixPermutationSymbol244 p q r A B C := by
  unfold thirdFullPhysicalSixSymbol244 thirdFullSixPermutationSymbol244
  calc
    _ =
      (thirdFullPhysicalOrderedSymbol244 p q r A B C +
        thirdFullPhysicalOrderedSymbol244 p r q A C B) +
      (thirdFullPhysicalOrderedSymbol244 q p r B A C +
        thirdFullPhysicalOrderedSymbol244 q r p B C A) +
      (thirdFullPhysicalOrderedSymbol244 r p q C A B +
        thirdFullPhysicalOrderedSymbol244 r q p C B A) := by ring
    _ =
      (thirdFullOrderedTriadRealSymbol244 p q r A B C +
        thirdFullOrderedTriadRealSymbol244 p r q A C B) +
      (thirdFullOrderedTriadRealSymbol244 q p r B A C +
        thirdFullOrderedTriadRealSymbol244 q r p B C A) +
      (thirdFullOrderedTriadRealSymbol244 r p q C A B +
        thirdFullOrderedTriadRealSymbol244 r q p C B A) := by
      rw [thirdFullPhysicalOrdered_pair_eq_old244 p q r A B C,
        thirdFullPhysicalOrdered_pair_eq_old244 q p r B A C,
        thirdFullPhysicalOrdered_pair_eq_old244 r p q C A B]
    _ = _ := by ring

/-- Frequency reflection negates the complete corrected real derivative
symbol. This is needed when coupling Fourier modes to their Hermitian mates. -/
theorem thirdFullPhysicalSix_reflection244
    (p q r A B C : A3 → ℝ) :
    thirdFullPhysicalSixSymbol244
      (fun i => -p i) (fun i => -q i) (fun i => -r i) A B C =
      -thirdFullPhysicalSixSymbol244 p q r A B C := by
  calc
    _ = thirdFullSixPermutationSymbol244
        (fun i => -p i) (fun i => -q i) (fun i => -r i) A B C :=
      thirdFullPhysicalSix_eq_prior_six244 _ _ _ _ _ _
    _ = -thirdFullSixPermutationSymbol244 p q r A B C :=
      thirdFullSixPermutationSymbol_reflect_frequencies244 _ _ _ _ _ _
    _ = -thirdFullPhysicalSixSymbol244 p q r A B C := by
      rw [thirdFullPhysicalSix_eq_prior_six244]

/-- Canonical positive-depth three-coordinate functions, matching the
previously audited explicit momentum-conserving triad. -/
private def physicalCoord244 (x y z : ℝ) (i : A3) : ℝ :=
  if axisRank i = 0 then x else if axisRank i = 1 then y else z

private def pPhys244 : A3 → ℝ := physicalCoord244 1 0 0
private def qPhys244 : A3 → ℝ := physicalCoord244 1 1 0
private def rPhys244 : A3 → ℝ := physicalCoord244 (-2) (-1) 0
private def APhys244 : A3 → ℝ := physicalCoord244 0 1 0
private def BPhys244 : A3 → ℝ := physicalCoord244 1 (-1) 0
private def CPhys244 : A3 → ℝ := physicalCoord244 1 (-2) 0

private theorem physicalCoord_dot244 (ax ay az bx byCoord bz : ℝ) :
    thirdTriadAxisDot244 (physicalCoord244 ax ay az)
      (physicalCoord244 bx byCoord bz) =
      ax * bx + ay * byCoord + az * bz := by
  classical
  unfold thirdTriadAxisDot244
  rw [axis_sum_three]
  norm_num [physicalCoord244, axisRank, xAxis, yAxis, zAxis]; ring

/-- All three frequencies sum to zero and each complexifiable polarization
is perpendicular to its own momentum. -/
theorem thirdFullPhysicalTriad_solenoidal244 :
    (∀ i : A3, pPhys244 i + qPhys244 i + rPhys244 i = 0) ∧
      thirdTriadAxisDot244 APhys244 pPhys244 = 0 ∧
      thirdTriadAxisDot244 BPhys244 qPhys244 = 0 ∧
      thirdTriadAxisDot244 CPhys244 rPhys244 = 0 := by
  constructor
  · intro i
    cases i with
    | first =>
        norm_num [pPhys244, qPhys244, rPhys244, physicalCoord244, axisRank]
    | next i =>
        cases i with
        | first =>
            norm_num [pPhys244, qPhys244, rPhys244, physicalCoord244, axisRank]
        | next i =>
            cases i with
            | first =>
                norm_num [pPhys244, qPhys244, rPhys244, physicalCoord244, axisRank]
  · constructor
    · norm_num [APhys244, pPhys244, physicalCoord_dot244]
    · constructor
      · norm_num [BPhys244, qPhys244, physicalCoord_dot244]
      · norm_num [CPhys244, rPhys244, physicalCoord_dot244]

/-- The *corrected* six ordered coefficients, including the gradient
polarization changes. These are NOT the previously reported six old values. -/
theorem thirdFullPhysicalSix_each_corrected244 :
    thirdFullPhysicalOrderedSymbol244 pPhys244 qPhys244 rPhys244
      APhys244 BPhys244 CPhys244 = -16 ∧
    thirdFullPhysicalOrderedSymbol244 pPhys244 rPhys244 qPhys244
      APhys244 CPhys244 BPhys244 = 28 ∧
    thirdFullPhysicalOrderedSymbol244 qPhys244 pPhys244 rPhys244
      BPhys244 APhys244 CPhys244 = 33 ∧
    thirdFullPhysicalOrderedSymbol244 qPhys244 rPhys244 pPhys244
      BPhys244 CPhys244 APhys244 = -81 ∧
    thirdFullPhysicalOrderedSymbol244 rPhys244 pPhys244 qPhys244
      CPhys244 APhys244 BPhys244 = -60 ∧
    thirdFullPhysicalOrderedSymbol244 rPhys244 qPhys244 pPhys244
      CPhys244 BPhys244 APhys244 = 0 := by
  simp only [thirdFullPhysicalOrderedSymbol244]
  simp only [pPhys244, qPhys244, rPhys244, APhys244, BPhys244,
    CPhys244, physicalCoord_dot244]
  norm_num

/-- The physical third-order six-permutation coefficient remains -96. -/
theorem thirdFullPhysicalSix_nonzero244 :
    thirdFullPhysicalSixSymbol244 pPhys244 qPhys244 rPhys244
      APhys244 BPhys244 CPhys244 = -96 := by
  rcases thirdFullPhysicalSix_each_corrected244 with
    ⟨h1, h2, h3, h4, h5, h6⟩
  unfold thirdFullPhysicalSixSymbol244
  rw [h1, h2, h3, h4, h5, h6]
  norm_num

/-- The phase-correct finite Hermitian pair: seven Fourier derivatives
supply I^7 = -I, and the reflected real momentum symbol is negative.
This is algebra, not an identity for a Schwartz integral. -/
noncomputable def thirdFullPhysicalHermitianOrbit244
    (p q r A B C : A3 → ℝ) (z : ℂ) : ℝ :=
  (((Complex.I ^ 7) *
      (thirdFullPhysicalSixSymbol244 p q r A B C : ℂ) * z) +
    ((Complex.I ^ 7) *
      (thirdFullPhysicalSixSymbol244
        (fun i => -p i) (fun i => -q i) (fun i => -r i) A B C : ℂ) *
      star z)).re

/-- Elementary phase computation, isolated from the six large coordinate
sums. With seven derivatives the Fourier phase is `-I`; the reflected
frequency polynomial has the opposite sign. The two Hermitian terms
therefore add to twice the imaginary part. -/
private theorem thirdFullPhysicalHermitian_scalar_identity244
    (s : ℝ) (z : ℂ) :
    (((-Complex.I) * (s : ℂ) * z +
       (-Complex.I) * (-(s : ℂ)) * star z)).re =
      2 * s * z.im := by
  calc
    _ = (Complex.I * (s : ℂ) * (star z - z)).re := by
      congr 1
      ring
    _ = 2 * s * z.im := by
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
        Complex.sub_im, Complex.star_def, Complex.conj_im]
      -- The first simplification leaves (I * ↑s).im; `ring` cannot
      -- reduce a complex projection. Evaluate it explicitly.
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, one_mul] <;> ring

/-- The exact imaginary-phase condition: the Hermitian-reflected orbit gives
TWICE the signed six-permutation coefficient times Im(z). There is no
automatic odd-phase cancellation when the polarization product is imaginary. -/
theorem thirdFullPhysicalHermitianOrbit_eq244
    (p q r A B C : A3 → ℝ) (z : ℂ) :
    thirdFullPhysicalHermitianOrbit244 p q r A B C z =
      2 * thirdFullPhysicalSixSymbol244 p q r A B C * z.im := by
  have hI : Complex.I ^ 7 = -Complex.I := by
    calc
      Complex.I ^ 7 = (Complex.I ^ 2) ^ 3 * Complex.I := by ring
      _ = -Complex.I := by rw [Complex.I_sq]; norm_num
  unfold thirdFullPhysicalHermitianOrbit244
  rw [thirdFullPhysicalSix_reflection244, hI]
  simpa only [Complex.ofReal_neg] using
    (thirdFullPhysicalHermitian_scalar_identity244
      (thirdFullPhysicalSixSymbol244 p q r A B C) z)

/-- With a 90-degree relative Fourier polarization-product phase, the
Hermitian orbit is nonzero and equals -192, not zero. -/
theorem thirdFullPhysicalHermitianOrbit_explicit244 :
    thirdFullPhysicalHermitianOrbit244
      pPhys244 qPhys244 rPhys244 APhys244 BPhys244 CPhys244
      Complex.I = -192 := by
  rw [thirdFullPhysicalHermitianOrbit_eq244,
    thirdFullPhysicalSix_nonzero244]
  norm_num [Complex.I_im]

/-- The physical scalar Fourier factor (2π)^7 is strictly positive;
multiplying the explicit nonzero Hermitian orbit by it retains strict sign. -/
theorem thirdFullPhysicalHermitianOrbit_physical_phase_nonzero244 :
    2 * (2 * Real.pi) ^ 7 *
      thirdFullPhysicalHermitianOrbit244
        pPhys244 qPhys244 rPhys244 APhys244 BPhys244 CPhys244
        Complex.I < 0 := by
  rw [thirdFullPhysicalHermitianOrbit_explicit244]
  have hpi : 0 < (2 * Real.pi) ^ 7 :=
    pow_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) 7
  nlinarith

end
end PrimeTensor.FirstMonomialTriad
