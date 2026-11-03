import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSixthPowerFlux
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadDivergence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadPhysicalShell
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdActualStaticAbsorptionObstruction244
import Mathlib.Tactic

/-!
# Full physical H³ sixth-power flux with genuinely complex Fourier polarizations

The previous signed six-orbit flux was expressed for real polarizations and
special polynomial Leray germs. An arbitrary real Schwartz velocity has COMPLEX
Fourier amplitudes; it is not legitimate to substitute those amplitudes into
that real theorem. Here the corrected six-order physical polynomial is extended
to arbitrary complex transverse vectors, with NO conjugation in the cubic
Fourier product. Conservation and complex incompressibility give the SAME exact
sixth-power frequency flux. It applies pointwise to the unrestricted Fourier
polarization of any divergence-free complexified Schwartz velocity.

This module does not claim that the unrestricted gradient-plus-interpolation
Fourier coefficient has already been symmetrized into the complex six-symbol.
That distinct measure-preserving integral identification remains necessary.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean
open scoped BigOperators FourierTransform SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeComplexSixthPowerFlux (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Bilinear, NOT Hermitian, polarization contraction in the actual Fourier
triple product. Conjugating one slot here would corrupt the H³ transport. -/
noncomputable def thirdFullComplexPolarizationDot244
    (A B : A3 → ℂ) : ℂ :=
  ∑ i : A3, A i * B i

/-- The original corrected gradient-plus-interpolation ordered coefficient,
now with complex spectral polarizations and real physical momenta. -/
noncomputable def thirdFullComplexOrderedSymbol244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ) : ℂ :=
  let a : ℂ := (thirdTriadAxisDot244 p q : ℂ)
  let b : ℂ := (thirdTriadAxisDot244 p r : ℂ)
  (thirdFullComplexPolarizationDot244 A C * mixedDot r B) *
    (a ^ 3 + 3 * a ^ 2 * b) +
  (thirdFullComplexPolarizationDot244 A B * mixedDot q C) *
    (3 * a ^ 2 * b)

/-- All SIX genuinely complex ordered terms, with simultaneous exchange of
momentum and the corresponding spectral polarization in each slot. -/
noncomputable def thirdFullComplexSixSymbol244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ) : ℂ :=
  thirdFullComplexOrderedSymbol244 p q r A B C +
  thirdFullComplexOrderedSymbol244 p r q A C B +
  thirdFullComplexOrderedSymbol244 q p r B A C +
  thirdFullComplexOrderedSymbol244 q r p B C A +
  thirdFullComplexOrderedSymbol244 r p q C A B +
  thirdFullComplexOrderedSymbol244 r q p C B A

/-- Exact sixth-power flux for COMPLEX physical polarizations. There is no
artificial modulus, complex conjugation, or division by zero frequency. -/
noncomputable def thirdFullComplexSixthPowerFlux244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ) : ℂ :=
  (thirdFullComplexPolarizationDot244 A C * mixedDot r B) *
    ((thirdTriadAxisDot244 r r : ℂ) ^ 3 -
      (thirdTriadAxisDot244 p p : ℂ) ^ 3) +
  (thirdFullComplexPolarizationDot244 A B * mixedDot q C) *
    ((thirdTriadAxisDot244 q q : ℂ) ^ 3 -
      (thirdTriadAxisDot244 p p : ℂ) ^ 3) +
  (thirdFullComplexPolarizationDot244 B C * mixedDot r A) *
    ((thirdTriadAxisDot244 r r : ℂ) ^ 3 -
      (thirdTriadAxisDot244 q q : ℂ) ^ 3)

private theorem thirdFullComplexPolarizationDot_comm244
    (A B : A3 → ℂ) :
    thirdFullComplexPolarizationDot244 A B =
      thirdFullComplexPolarizationDot244 B A := by
  unfold thirdFullComplexPolarizationDot244
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Momentum conservation contracts against a complex polarization by
COMPLEX bilinearity; no order argument or spectral regularity is used. -/
theorem thirdFullComplex_momentum_dot244
    (p q r : A3 → ℝ) (A : A3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0) :
    mixedDot p A + mixedDot q A + mixedDot r A = 0 := by
  change (∑ i : A3, (p i : ℂ) * A i) +
    (∑ i : A3, (q i : ℂ) * A i) +
    (∑ i : A3, (r i : ℂ) * A i) = 0
  calc
    _ = ∑ i : A3, ((p i : ℂ) + (q i : ℂ) + (r i : ℂ)) * A i := by
      simp only [add_mul, Finset.sum_add_distrib]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : (p i : ℂ) + (q i : ℂ) + (r i : ℂ) = 0 := by
        exact_mod_cast hm i
      rw [hi]
      ring

/-- The polynomial heart of the complex six-order cancellation, independent
of frequencies, polarizations, and the order structure of real numbers. -/
private theorem thirdFullComplex_six_scalar_flux244
    (a b c X Y Z t s u : ℂ) :
    (X * t) * (a ^ 3 + 3 * a ^ 2 * b) +
      (Y * s) * (3 * a ^ 2 * b) +
    (Y * s) * (b ^ 3 + 3 * b ^ 2 * a) +
      (X * t) * (3 * b ^ 2 * a) +
    (Z * u) * (a ^ 3 + 3 * a ^ 2 * c) +
      (Y * (-s)) * (3 * a ^ 2 * c) +
    (Y * (-s)) * (c ^ 3 + 3 * c ^ 2 * a) +
      (Z * u) * (3 * c ^ 2 * a) +
    (Z * (-u)) * (b ^ 3 + 3 * b ^ 2 * c) +
      (X * (-t)) * (3 * b ^ 2 * c) +
    (X * (-t)) * (c ^ 3 + 3 * c ^ 2 * b) +
      (Z * (-u)) * (3 * c ^ 2 * b) =
    (X * t) * ((-(b + c)) ^ 3 - (-(a + b)) ^ 3) +
    (Y * s) * ((-(a + c)) ^ 3 - (-(a + b)) ^ 3) +
    (Z * u) * ((-(b + c)) ^ 3 - (-(a + c)) ^ 3) := by
  ring

/-- The COMPLETE six-order H³ cubic for arbitrary COMPLEX Fourier
polarizations is a sum of three exact sixth-power radius fluxes. -/
theorem thirdFullComplexSix_sixthPowerFlux244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0)
    (hA : mixedDot p A = 0)
    (hB : mixedDot q B = 0)
    (hC : mixedDot r C = 0) :
    thirdFullComplexSixSymbol244 p q r A B C =
      thirdFullComplexSixthPowerFlux244 p q r A B C := by
  have hmA := thirdFullComplex_momentum_dot244 p q r A hm
  have hmB := thirdFullComplex_momentum_dot244 p q r B hm
  have hmC := thirdFullComplex_momentum_dot244 p q r C hm
  have hAq : mixedDot q A = -mixedDot r A := by
    calc
      _ = (mixedDot p A + mixedDot q A + mixedDot r A) -
            mixedDot p A - mixedDot r A := by ring
      _ = -mixedDot r A := by rw [hmA, hA]; ring
  have hBp : mixedDot p B = -mixedDot r B := by
    calc
      _ = (mixedDot p B + mixedDot q B + mixedDot r B) -
            mixedDot q B - mixedDot r B := by ring
      _ = -mixedDot r B := by rw [hmB, hB]; ring
  have hCp : mixedDot p C = -mixedDot q C := by
    calc
      _ = (mixedDot p C + mixedDot q C + mixedDot r C) -
            mixedDot q C - mixedDot r C := by ring
      _ = -mixedDot q C := by rw [hmC, hC]; ring
  have hqp := thirdFullAxisDot_comm244 q p
  have hrp := thirdFullAxisDot_comm244 r p
  have hrq := thirdFullAxisDot_comm244 r q
  have hBA := thirdFullComplexPolarizationDot_comm244 B A
  have hCA := thirdFullComplexPolarizationDot_comm244 C A
  have hCB := thirdFullComplexPolarizationDot_comm244 C B
  let a : ℂ := (thirdTriadAxisDot244 p q : ℂ)
  let b : ℂ := (thirdTriadAxisDot244 p r : ℂ)
  let c : ℂ := (thirdTriadAxisDot244 q r : ℂ)
  let P : ℂ := (thirdTriadAxisDot244 p p : ℂ)
  let Q : ℂ := (thirdTriadAxisDot244 q q : ℂ)
  let R : ℂ := (thirdTriadAxisDot244 r r : ℂ)
  let X : ℂ := thirdFullComplexPolarizationDot244 A C
  let Y : ℂ := thirdFullComplexPolarizationDot244 A B
  let Z : ℂ := thirdFullComplexPolarizationDot244 B C
  let t : ℂ := mixedDot r B
  let s : ℂ := mixedDot q C
  let u : ℂ := mixedDot r A
  have hpRaw := momentum_dot p q r p hm
  have hqRaw := momentum_dot p q r q hm
  have hrRaw := momentum_dot p q r r hm
  change thirdTriadAxisDot244 p p + thirdTriadAxisDot244 q p +
    thirdTriadAxisDot244 r p = 0 at hpRaw
  change thirdTriadAxisDot244 p q + thirdTriadAxisDot244 q q +
    thirdTriadAxisDot244 r q = 0 at hqRaw
  change thirdTriadAxisDot244 p r + thirdTriadAxisDot244 q r +
    thirdTriadAxisDot244 r r = 0 at hrRaw
  rw [hqp, hrp] at hpRaw
  rw [hrq] at hqRaw
  have hpC : P + a + b = 0 := by
    dsimp only [P, a, b]
    exact_mod_cast hpRaw
  have hqC : a + Q + c = 0 := by
    dsimp only [a, Q, c]
    exact_mod_cast hqRaw
  have hrC : b + c + R = 0 := by
    dsimp only [b, c, R]
    exact_mod_cast hrRaw
  have hP : P = -(a + b) := by
    calc
      P = (P + a + b) - (a + b) := by ring
      _ = -(a + b) := by rw [hpC]; ring
  have hQ : Q = -(a + c) := by
    calc
      Q = (a + Q + c) - (a + c) := by ring
      _ = -(a + c) := by rw [hqC]; ring
  have hR : R = -(b + c) := by
    calc
      R = (b + c + R) - (b + c) := by ring
      _ = -(b + c) := by rw [hrC]; ring
  -- Identify the actual six POLARIZATION permutations with the universal
  -- complex polynomial, without silently replacing a complex amplitude by
  -- its real part or conjugate.
  have hSix : thirdFullComplexSixSymbol244 p q r A B C =
      (X * t) * (a ^ 3 + 3 * a ^ 2 * b) +
        (Y * s) * (3 * a ^ 2 * b) +
      (Y * s) * (b ^ 3 + 3 * b ^ 2 * a) +
        (X * t) * (3 * b ^ 2 * a) +
      (Z * u) * (a ^ 3 + 3 * a ^ 2 * c) +
        (Y * (-s)) * (3 * a ^ 2 * c) +
      (Y * (-s)) * (c ^ 3 + 3 * c ^ 2 * a) +
        (Z * u) * (3 * c ^ 2 * a) +
      (Z * (-u)) * (b ^ 3 + 3 * b ^ 2 * c) +
        (X * (-t)) * (3 * b ^ 2 * c) +
      (X * (-t)) * (c ^ 3 + 3 * c ^ 2 * b) +
        (Z * (-u)) * (3 * c ^ 2 * b) := by
    unfold thirdFullComplexSixSymbol244 thirdFullComplexOrderedSymbol244
    simp only [hqp, hrp, hrq, hBA, hCA, hCB, hAq, hBp, hCp]
    dsimp only [a, b, c, X, Y, Z, t, s, u]
    ring
  have hFlux : thirdFullComplexSixthPowerFlux244 p q r A B C =
      (X * t) * (R ^ 3 - P ^ 3) +
      (Y * s) * (Q ^ 3 - P ^ 3) +
      (Z * u) * (R ^ 3 - Q ^ 3) := by
    rfl
  rw [hSix, hFlux, hP, hQ, hR]
  exact thirdFullComplex_six_scalar_flux244 a b c X Y Z t s u

/-- Two matching squared radii do not annihilate the interaction: precisely
one complex two-shell transfer survives. -/
theorem thirdFullComplexSix_twoEqualRadii_flux244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0)
    (hA : mixedDot p A = 0)
    (hB : mixedDot q B = 0)
    (hC : mixedDot r C = 0)
    (hPQ : thirdTriadAxisDot244 p p = thirdTriadAxisDot244 q q) :
    thirdFullComplexSixSymbol244 p q r A B C =
      ((thirdTriadAxisDot244 r r : ℂ) ^ 3 -
        (thirdTriadAxisDot244 p p : ℂ) ^ 3) *
      (thirdFullComplexPolarizationDot244 A C * mixedDot r B +
        thirdFullComplexPolarizationDot244 B C * mixedDot r A) := by
  rw [thirdFullComplexSix_sixthPowerFlux244 p q r A B C hm hA hB hC]
  unfold thirdFullComplexSixthPowerFlux244
  rw [← hPQ]
  ring

/-- A balanced-radius triad is exactly invisible to the full complex
third-order Fourier energy transfer, including arbitrary complex phases. -/
theorem thirdFullComplexSix_equalRadius_cancellation244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0)
    (hA : mixedDot p A = 0)
    (hB : mixedDot q B = 0)
    (hC : mixedDot r C = 0)
    (hPQ : thirdTriadAxisDot244 p p = thirdTriadAxisDot244 q q)
    (hPR : thirdTriadAxisDot244 p p = thirdTriadAxisDot244 r r) :
    thirdFullComplexSixSymbol244 p q r A B C = 0 := by
  rw [thirdFullComplexSix_sixthPowerFlux244 p q r A B C hm hA hB hC]
  unfold thirdFullComplexSixthPowerFlux244
  rw [← hPQ, ← hPR]
  ring

/-- The six-order complex polynomial evaluated on the ACTUAL Fourier
transforms of one Schwartz field, rather than on frozen real polarizations. -/
noncomputable def thirdFullSchwartzComplexSixSymbol244
    (f : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) : ℂ :=
  let U := h3SchwartzTriadPolarization f
  thirdFullComplexSixSymbol244
    (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2))) (WithLp.ofLp z.2)
    (U (WithLp.ofLp z.1))
    (U (WithLp.ofLp (-(z.1 + z.2))))
    (U (WithLp.ofLp z.2))

/-- Same actual Fourier data, expressed as three SIXTH-POWER radial fluxes. -/
noncomputable def thirdFullSchwartzComplexSixthPowerFlux244
    (f : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) : ℂ :=
  let U := h3SchwartzTriadPolarization f
  thirdFullComplexSixthPowerFlux244
    (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2))) (WithLp.ofLp z.2)
    (U (WithLp.ofLp z.1))
    (U (WithLp.ofLp (-(z.1 + z.2))))
    (U (WithLp.ofLp z.2))

/-- Pointwise exact sixth-power flux for arbitrary solenoidal COMPLEX
Schwartz Fourier amplitudes. The only premise is physical incompressibility;
there are no selected packets, real-polarization substitutions, or time gates. -/
theorem thirdFullSchwartzComplexSix_eq_sixthPowerFlux244
    (f : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ ξ : A3 → ℝ, mixedDot ξ (h3SchwartzTriadPolarization f ξ) = 0)
    (z : V3 × V3) :
    thirdFullSchwartzComplexSixSymbol244 f z =
      thirdFullSchwartzComplexSixthPowerFlux244 f z := by
  let p : A3 → ℝ := WithLp.ofLp z.1
  let q : A3 → ℝ := WithLp.ofLp (-(z.1 + z.2))
  let r : A3 → ℝ := WithLp.ofLp z.2
  have hm : ∀ i, p i + q i + r i = 0 := by
    intro i
    change (WithLp.ofLp z.1) i +
      (WithLp.ofLp (-(z.1 + z.2))) i + (WithLp.ofLp z.2) i = 0
    simp only [WithLp.ofLp_neg, WithLp.ofLp_add, Pi.neg_apply, Pi.add_apply]
    abel
  exact thirdFullComplexSix_sixthPowerFlux244 p q r
    (h3SchwartzTriadPolarization f p)
    (h3SchwartzTriadPolarization f q)
    (h3SchwartzTriadPolarization f r)
    hm (hDiv p) (hDiv q) (hDiv r)

/-- PHYSICAL real Schwartz divergence, on the genuine positive-depth Point3
carrier, forces the exact complex sixth-power H³ spectral flux. We transport
through the existing scalar line-derivative / Fourier-divergence bridge; no
independent complex spectral solenoidality premise remains. -/
theorem thirdFullRealSchwartz_sixthPowerFlux_of_point3Solenoidal244
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (z : V3 × V3) :
    thirdFullSchwartzComplexSixSymbol244
      (fun j => h3SchwartzComplexify (f j)) z =
    thirdFullSchwartzComplexSixthPowerFlux244
      (fun j => h3SchwartzComplexify (f j)) z := by
  have hDeriv : ∀ y : V3,
      ∑ j : A3, fderiv ℝ (h3SchwartzComplexify (f j)) y
        (h3FourierAxisDirection j) = 0 := by
    intro y
    have hr := hDiv (WithLp.ofLp y)
    simp only [h3SchwartzPoint3Scalar_spatial_d,
      h3SchwartzPoint3Scalar] at hr
    have hr' : (∑ j : A3,
        (∂_{h3FourierAxisDirection j} (f j)) y) = 0 := hr
    simp only [← SchwartzMap.lineDerivOp_apply_eq_fderiv,
      h3TriadComplexify_lineDeriv, h3SchwartzComplexify_apply]
    exact_mod_cast hr'
  exact thirdFullSchwartzComplexSix_eq_sixthPowerFlux244
    (fun j => h3SchwartzComplexify (f j))
    (h3SchwartzTriadPolarization_divergence_zero _ hDeriv) z

end
end PrimeTensor.FirstMonomialTriad
