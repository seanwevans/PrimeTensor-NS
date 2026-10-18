import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealPositiveSectorSpectra244
import Mathlib.Tactic

/-!
# Exact imaginary-phase extraction from physical positive-sector Fourier triples

The complete real physical H3 commutator is an integral of the imaginary
part of its unphased kernel over six positive coherent sectors. The previous
module identifies the three ACTUAL Fourier factors at every sector point
where the recovered Schwartz triple mass does not vanish.

Here we factor their phase without changing any cutoff or moving transverse
polarization. All six orders have the same total complex phase I, while the
real scalar coefficient retains the *three distinct smooth windows* and the
*three frequency-dependent solenoidal polynomial germs*. This gives an exact
imaginary part for each real Fourier-triple component and each genuine
seven-derivative 3+3+1 gradient slot.

We also substitute the actual three isolated Fourier packets into the TRUE
3+2+2 interpolation kernel. No assertion about the full six-sector integral
sign, nor the sharp six-order polynomial identification, is made here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 1500000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev PairV244 := H3FourierPoint3 × H3FourierPoint3

noncomputable local instance axisFintypeSectorPhase244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Three real scalar cutoffs and three real solenoidal germ components have
exactly the product phase of their three complex Fourier factors. Neither a
conjugate nor a sign is inserted in this purely algebraic statement. -/
theorem thirdFullThreeWindowFactors_phase244
    (wp wq wr gp gq gr : ℝ) (α β γ : ℂ)
    (hPhase : α * β * γ = Complex.I) :
    (((wp : ℂ) * α * (gp : ℂ)) *
      ((wq : ℂ) * β * (gq : ℂ))) *
      ((wr : ℂ) * γ * (gr : ℂ)) =
    (((wp * gp) * (wq * gq) * (wr * gr) : ℝ) : ℂ) * Complex.I := by
  calc
    _ = (((wp * gp) * (wq * gq) * (wr * gr) : ℝ) : ℂ) *
        (α * β * γ) := by
          push_cast
          ring
    _ = _ := by rw [hPhase]

/-- The full windowed triple's imaginary part is the unmodified real
product, because the single surviving cubic phase is exactly I. -/
theorem thirdFullThreeWindowFactors_imag244
    (wp wq wr gp gq gr : ℝ) (α β γ : ℂ)
    (hPhase : α * β * γ = Complex.I) :
    ((((wp : ℂ) * α * (gp : ℂ)) *
      ((wq : ℂ) * β * (gq : ℂ))) *
      ((wr : ℂ) * γ * (gr : ℂ))).im =
    (wp * gp) * (wq * gq) * (wr * gr) := by
  rw [thirdFullThreeWindowFactors_phase244 wp wq wr gp gq gr α β γ hPhase]
  simp [Complex.mul_im]

/-- Real factor of the actual three-frequency Fourier component. Every
window is evaluated at its OWN momentum; every transverse germ uses its OWN
frequency and fixed-center normalization. -/
noncomputable def thirdFullPositiveSectorRealTripleFactor244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (n : Fin 6) (z : PairV244) (a b c : A3) : ℝ :=
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  let labels := lowNormalQuarterCoherentLabelPair false n
  let middle := thirdFullPositiveMiddleLabel244 n
  let wp : ℝ := (thirdFullAxisWindowBump244 ρ hρ labels.1 : Freq244 → ℝ) p
  let wq : ℝ := (thirdFullAxisWindowBump244 ρ hρ middle : Freq244 → ℝ) q
  let wr : ℝ := (thirdFullAxisWindowBump244 ρ hρ labels.2 : Freq244 → ℝ) r
  let gp : ℝ := thirdFullFixedCenterTransverseGerm244
    (thirdFullAxisSixCenter244 labels.1) p
    (thirdFullPositiveWindowPolarization244 A B C labels.1) a
  let gq : ℝ := thirdFullFixedCenterTransverseGerm244
    (thirdFullAxisSixCenter244 middle) q
    (thirdFullPositiveWindowPolarization244 A B C middle) b
  let gr : ℝ := thirdFullFixedCenterTransverseGerm244
    (thirdFullAxisSixCenter244 labels.2) r
    (thirdFullPositiveWindowPolarization244 A B C labels.2) c
  (wp * gp) * (wq * gq) * (wr * gr)

/-- On any nonzero actual physical triple in a positive coherent sector,
its literal complex Fourier component is I times the REAL six-window/germ
product. This is exact at VARIABLE Fourier momenta, not only at the sharp
centers. It retains the correct order of the three factors. -/
theorem thirdFullPositiveSector_actual_triple_eq_real_mul_I244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0)
    (a b c : A3) :
    let p := WithLp.ofLp z.1
    let r := WithLp.ofLp z.2
    let q := thirdFullMiddleFrequency244 (p, r)
    (thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C p a *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C q b) *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C r c =
    (thirdFullPositiveSectorRealTripleFactor244 ρ hρ A B C n z a b c : ℂ) *
      Complex.I := by
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  let labels := lowNormalQuarterCoherentLabelPair false n
  let middle := thirdFullPositiveMiddleLabel244 n
  have ht := thirdFullPositiveSector_actual_triple_component244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass a b c
  dsimp only at ht ⊢
  rw [ht]
  simpa only [thirdFullPositiveSectorRealTripleFactor244,
      thirdFullAxisComplexWindowPacket244] using
    (thirdFullThreeWindowFactors_phase244
      ((thirdFullAxisWindowBump244 ρ hρ labels.1 : Freq244 → ℝ) p)
      ((thirdFullAxisWindowBump244 ρ hρ middle : Freq244 → ℝ) q)
      ((thirdFullAxisWindowBump244 ρ hρ labels.2 : Freq244 → ℝ) r)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 labels.1) p
        (thirdFullPositiveWindowPolarization244 A B C labels.1) a)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 middle) q
        (thirdFullPositiveWindowPolarization244 A B C middle) b)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 labels.2) r
        (thirdFullPositiveWindowPolarization244 A B C labels.2) c)
      (thirdFullPositiveWindowPhase244 labels.1)
      (thirdFullPositiveWindowPhase244 middle)
      (thirdFullPositiveWindowPhase244 labels.2)
      (thirdFullPositiveSector_phase_product244 n))

/-- The imaginary part of each *actual* nonzero Fourier triple is exactly
its real windowed-germ factor; no orientation-dependent complex phase is
left unresolved. -/
theorem thirdFullPositiveSector_actual_triple_imag244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0)
    (a b c : A3) :
    let p := WithLp.ofLp z.1
    let r := WithLp.ofLp z.2
    let q := thirdFullMiddleFrequency244 (p, r)
    ((thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C p a *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C q b) *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C r c).im =
      thirdFullPositiveSectorRealTripleFactor244 ρ hρ A B C n z a b c := by
  -- The goal has `let p`, `let r`, `let q`; expose those before rewriting.
  dsimp only at ⊢
  rw [thirdFullPositiveSector_actual_triple_eq_real_mul_I244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass a b c]
  simp [Complex.mul_im]

/-- The REAL part of the true three-frequency Fourier component is zero
on all six positive orientations, even when the I-phase is on the first or
middle Fourier variable rather than the third. -/
theorem thirdFullPositiveSector_actual_triple_re_zero244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0)
    (a b c : A3) :
    let p := WithLp.ofLp z.1
    let r := WithLp.ofLp z.2
    let q := thirdFullMiddleFrequency244 (p, r)
    ((thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C p a *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C q b) *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C r c).re = 0 := by
  -- The theorem's product is definitionally equal, but `rw` does not zeta-
  -- reduce goal-local `let` bindings on its own.
  dsimp only at ⊢
  rw [thirdFullPositiveSector_actual_triple_eq_real_mul_I244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass a b c]
  simp [Complex.mul_re]

/-- The actual 3+2+2 interpolation kernel is, on every nonzero triple in
a positive sector, the preexisting complex coefficient contracted against
the THREE isolated frequency-dependent transverse germs. This is not an
auxiliary polynomial substituted for the physical Schwartz kernel. -/
theorem thirdFullPositiveSector_actual_interpolation244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0) :
    let p := WithLp.ofLp z.1
    let r := WithLp.ofLp z.2
    let q := thirdFullMiddleFrequency244 (p, r)
    let labels := lowNormalQuarterCoherentLabelPair false n
    let middle := thirdFullPositiveMiddleLabel244 n
    thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z =
      complexCoefficient p q r
        (thirdFullAxisComplexWindowPacket244 ρ hρ middle
          (thirdFullPositiveWindowPolarization244 A B C middle)
          (thirdFullPositiveWindowPhase244 middle) q) *
      amplitudeDot
        (thirdFullAxisComplexWindowPacket244 ρ hρ labels.1
          (thirdFullPositiveWindowPolarization244 A B C labels.1)
          (thirdFullPositiveWindowPhase244 labels.1) p)
        (thirdFullAxisComplexWindowPacket244 ρ hρ labels.2
          (thirdFullPositiveWindowPolarization244 A B C labels.2)
          (thirdFullPositiveWindowPhase244 labels.2) r) := by
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  have hSpectra := thirdFullPositiveSector_actual_triple_spectra244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass
  obtain ⟨hP, hQ, hR⟩ := hSpectra
  dsimp only at hP hQ hR ⊢
  rw [thirdFullAxisRealInterpolationKernel_eq_amplitude244]
  change complexCoefficient p q r
      (thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C q) *
      amplitudeDot
        (thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C p)
        (thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C r) = _
  rw [hP, hQ, hR]

/-- For the true 3+3+1 gradient slot, the seven-derivative complex weight
still multiplies the real window/germ factor; it has not been replaced by
the earlier sharp six-order coefficient. -/
theorem thirdFullPositiveSector_gradient_slot_phase244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0)
    (j m t : A3) (a b c d e k v : H3FourierPoint3) :
    thirdFullAxisRealGradientSlot244 ρ hρ A B C j m t a b c d e k v z =
      thirdFullGradientSevenWeight244 a b c d e k v z *
        ((thirdFullPositiveSectorRealTripleFactor244 ρ hρ A B C n z j m t : ℂ) *
          Complex.I) := by
  rw [thirdFullAxisRealGradientSlot_factor244]
  rw [thirdFullPositiveSector_actual_triple_eq_real_mul_I244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass j m t]

/-- The actual seven-derivative gradient weight is REAL as a complex
number. This follows from its committed conjugation theorem, not by
discarding its frequency contractions. -/
theorem thirdFullGradientSevenWeight_im_zero244
    (a b c d e k v : H3FourierPoint3) (z : PairV244) :
    (thirdFullGradientSevenWeight244 a b c d e k v z).im = 0 := by
  have h := congrArg Complex.im (thirdFullGradientSevenWeight_star244
    a b c d e k v z)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

/-- The imaginary part of EVERY actual nonzero 3+3+1 gradient-slot kernel
is exactly its ORIGINAL real seventh-derivative weight times the real
windowed-germ triple. This identity is the analytical handoff to the full
five-index summation; no fixed-sign hypothesis is used. -/
theorem thirdFullPositiveSector_gradient_slot_imag244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0)
    (j m t : A3) (a b c d e k v : H3FourierPoint3) :
    (thirdFullAxisRealGradientSlot244 ρ hρ A B C
      j m t a b c d e k v z).im =
      (thirdFullGradientSevenWeight244 a b c d e k v z).re *
        thirdFullPositiveSectorRealTripleFactor244 ρ hρ A B C n z j m t := by
  rw [thirdFullPositiveSector_gradient_slot_phase244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass j m t a b c d e k v]
  have hw := thirdFullGradientSevenWeight_im_zero244 a b c d e k v z
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, add_zero]
  rw [hw]
  ring

end
end PrimeTensor.FirstMonomialTriad
