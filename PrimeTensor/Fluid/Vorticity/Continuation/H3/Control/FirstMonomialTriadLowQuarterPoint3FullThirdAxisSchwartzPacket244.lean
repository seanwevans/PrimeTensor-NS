import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdWindowedLocalIntegral244
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic

/-!
# Actual compact smooth full-third Hermitian Fourier packets

The earlier strictly negative integral involved a single labelled windowed
coefficient. This file constructs an ACTUAL complex three-component Schwartz
map on the positive-depth `Axis Depth.three` carrier: three smooth positive
frequency windows, three globally polynomial fixed-center solenoidal germs,
and their conjugate-reflected partners. One selected polarization has phase I.

We prove the finished Fourier packet is smooth, compactly supported,
divergence-free at every frequency and Hermitian under frequency reflection.
These statements do not yet identify the packet's inverse Fourier transform
with the physical real Schwartz field or prove that the complete third-order
commutator integral equals the previously signed local integral. In particular,
no global noncancellation or Navier--Stokes continuation follows here.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology ContDiff SchwartzMap

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev CPol244 := A3 → ℂ

noncomputable local instance axisFintypeFullThirdPacket244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Complex Fourier divergence on the ACTUAL positive-depth carrier. -/
def thirdFullAxisComplexDot244 (ξ : Freq244) (v : CPol244) : ℂ :=
  ∑ i : A3, (ξ i : ℂ) * v i

private theorem thirdFullAxisComplexDot_add244
    (ξ : Freq244) (u v : CPol244) :
    thirdFullAxisComplexDot244 ξ (fun i => u i + v i) =
      thirdFullAxisComplexDot244 ξ u + thirdFullAxisComplexDot244 ξ v := by
  unfold thirdFullAxisComplexDot244
  simp only [mul_add, Finset.sum_add_distrib]

private theorem thirdFullAxisComplexDot_neg_freq244
    (ξ : Freq244) (v : CPol244) :
    thirdFullAxisComplexDot244 (-ξ) v =
      -thirdFullAxisComplexDot244 ξ v := by
  unfold thirdFullAxisComplexDot244
  simp only [Pi.neg_apply, Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib]

private theorem thirdFullAxisComplexDot_star244
    (ξ : Freq244) (v : CPol244) :
    thirdFullAxisComplexDot244 ξ (fun i => star (v i)) =
      star (thirdFullAxisComplexDot244 ξ v) := by
  change thirdFullAxisComplexDot244 ξ
    (fun i => (starRingEnd ℂ) (v i)) =
      (starRingEnd ℂ) (thirdFullAxisComplexDot244 ξ v)
  simp [thirdFullAxisComplexDot244, map_sum, map_mul, Complex.conj_ofReal]

/-- A real fixed-center transverse germ, multiplied by a complex scalar
phase and an actual smooth compact frequency window. -/
noncomputable def thirdFullAxisComplexWindowPacket244
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6)
    (a : Freq244) (phase : ℂ) (ξ : Freq244) (d : A3) : ℂ :=
  ((thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) ξ : ℂ) *
    phase *
    (thirdFullFixedCenterTransverseGerm244
      (thirdFullAxisSixCenter244 i) ξ a d : ℂ)

/-- Complex Fourier divergence of every individual windowed packet is
exactly zero, including at the origin. There is no |ξ|² denominator. -/
theorem thirdFullAxisComplexWindowPacket_solenoidal244
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6)
    (a : Freq244) (phase : ℂ) (ξ : Freq244) :
    thirdFullAxisComplexDot244 ξ
      (thirdFullAxisComplexWindowPacket244 ρ hρ i a phase ξ) = 0 := by
  let G : A3 → ℝ :=
    thirdFullFixedCenterTransverseGerm244 (thirdFullAxisSixCenter244 i) ξ a
  let t : ℂ :=
    ((thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) ξ : ℂ) * phase
  have hG : thirdTriadAxisDot244 ξ G = 0 :=
    thirdFullFixedCenterTransverseGerm_solenoidal244 _ _ _
  change (∑ d : A3, (ξ d : ℂ) * (t * (G d : ℂ))) = 0
  calc
    _ = t * (∑ d : A3, ((ξ d * G d : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      push_cast
      ring
    _ = t * (thirdTriadAxisDot244 ξ G : ℂ) := by
      congr 1
      -- The sum must be transported across the real-to-complex cast.
      -- A ring normalization alone cannot commute a ring hom with a sum.
      simp only [thirdTriadAxisDot244]
      push_cast <;> rfl
    _ = 0 := by
      simp [hG]

/-- Smoothness of the scalar squared frequency norm, on the physical
positive-depth three-axis carrier. -/
private theorem thirdFullAxisSquared_smooth244 :
    ContDiff ℝ ∞ (fun ξ : Freq244 => thirdTriadAxisDot244 ξ ξ) := by
  have hx : ContDiff ℝ ∞ (fun ξ : Freq244 => ξ xAxis) :=
    contDiff_apply ℝ ℝ xAxis
  have hy : ContDiff ℝ ∞ (fun ξ : Freq244 => ξ yAxis) :=
    contDiff_apply ℝ ℝ yAxis
  have hz : ContDiff ℝ ∞ (fun ξ : Freq244 => ξ zAxis) :=
    contDiff_apply ℝ ℝ zAxis
  simpa only [thirdTriadAxisDot244, axis_sum_three] using
    (hx.mul hx).add ((hy.mul hy).add (hz.mul hz))

/-- Smoothness of the linear frequency/polarization pairing. -/
private theorem thirdFullAxisMixed_smooth244 (a : Freq244) :
    ContDiff ℝ ∞ (fun ξ : Freq244 => thirdTriadAxisDot244 ξ a) := by
  have hx : ContDiff ℝ ∞ (fun ξ : Freq244 => ξ xAxis) :=
    contDiff_apply ℝ ℝ xAxis
  have hy : ContDiff ℝ ∞ (fun ξ : Freq244 => ξ yAxis) :=
    contDiff_apply ℝ ℝ yAxis
  have hz : ContDiff ℝ ∞ (fun ξ : Freq244 => ξ zAxis) :=
    contDiff_apply ℝ ℝ zAxis
  simpa only [thirdTriadAxisDot244, axis_sum_three] using
    (hx.mul (contDiff_const : ContDiff ℝ ∞ (fun _ : Freq244 => a xAxis))).add
      ((hy.mul (contDiff_const : ContDiff ℝ ∞ (fun _ : Freq244 => a yAxis))).add
       (hz.mul (contDiff_const : ContDiff ℝ ∞ (fun _ : Freq244 => a zAxis))))

/-- Globally smooth fixed-center polynomial projection. Unlike an ordinary
Leray projection it has no singularity at zero frequency. -/
theorem thirdFullFixedCenterTransverseGerm_contDiff244
    (η a : Freq244) :
    ContDiff ℝ ∞ (fun ξ : Freq244 => thirdFullFixedCenterTransverseGerm244 η ξ a) := by
  apply contDiff_pi'
  intro d
  change ContDiff ℝ ∞ (fun ξ : Freq244 =>
    (thirdTriadAxisDot244 η η)⁻¹ *
      (thirdTriadAxisDot244 ξ ξ * a d -
        thirdTriadAxisDot244 ξ a * ξ d))
  exact (contDiff_const : ContDiff ℝ ∞
    (fun _ : Freq244 => (thirdTriadAxisDot244 η η)⁻¹)).mul
    ((thirdFullAxisSquared_smooth244.mul contDiff_const).sub
      ((thirdFullAxisMixed_smooth244 a).mul (contDiff_apply ℝ ℝ d)))

/-- A smooth complex scalar window times a polynomial transverse germ is
smooth in every complex Fourier component. -/
theorem thirdFullAxisComplexWindowPacket_contDiff244
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6)
    (a : Freq244) (phase : ℂ) :
    ContDiff ℝ ∞ (thirdFullAxisComplexWindowPacket244 ρ hρ i a phase) := by
  apply contDiff_pi'
  intro d
  have hWindow : ContDiff ℝ ∞ (fun ξ : Freq244 =>
      ((thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) ξ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (thirdFullAxisWindowBump_contDiff244 ρ hρ i)
  have hGerm : ContDiff ℝ ∞ (fun ξ : Freq244 =>
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 i) ξ a d : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_apply ℝ ℝ d).comp
        (thirdFullFixedCenterTransverseGerm_contDiff244
          (thirdFullAxisSixCenter244 i) a))
  exact (hWindow.mul contDiff_const).mul hGerm

/-- The full vector packet has compact support because its scalar window
does. The polynomial growth of the projection does not enlarge support. -/
theorem thirdFullAxisComplexWindowPacket_hasCompactSupport244
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6)
    (a : Freq244) (phase : ℂ) :
    HasCompactSupport (thirdFullAxisComplexWindowPacket244 ρ hρ i a phase) := by
  have h := (thirdFullAxisWindowBump_hasCompactSupport244 ρ hρ i).smul_right
    (f' := fun ξ : Freq244 => fun d : A3 =>
      phase * (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 i) ξ a d : ℂ))
  convert h using 1
  funext ξ d
  change ((thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) ξ : ℂ) *
      phase * (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 i) ξ a d : ℂ) =
    ((thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) ξ : ℝ) •
      (phase * (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 i) ξ a d : ℂ))
  rw [← Complex.coe_smul, smul_eq_mul]
  ring

/-- The three positive-frequency packets with separately chosen phases. -/
noncomputable def thirdFullAxisPositiveThreePacket244
    (ρ : ℝ) (hρ : 0 < ρ)
    (A B C : Freq244) (s t u : ℂ) (ξ : Freq244) (d : A3) : ℂ :=
  (thirdFullAxisComplexWindowPacket244 ρ hρ 0 A s ξ d +
    thirdFullAxisComplexWindowPacket244 ρ hρ 1 B t ξ d) +
    thirdFullAxisComplexWindowPacket244 ρ hρ 2 C u ξ d

theorem thirdFullAxisPositiveThreePacket_solenoidal244
    (ρ : ℝ) (hρ : 0 < ρ)
    (A B C : Freq244) (s t u : ℂ) (ξ : Freq244) :
    thirdFullAxisComplexDot244 ξ
      (thirdFullAxisPositiveThreePacket244 ρ hρ A B C s t u ξ) = 0 := by
  change thirdFullAxisComplexDot244 ξ
    (fun d => (thirdFullAxisComplexWindowPacket244 ρ hρ 0 A s ξ d +
      thirdFullAxisComplexWindowPacket244 ρ hρ 1 B t ξ d) +
      thirdFullAxisComplexWindowPacket244 ρ hρ 2 C u ξ d) = 0
  rw [thirdFullAxisComplexDot_add244, thirdFullAxisComplexDot_add244,
    thirdFullAxisComplexWindowPacket_solenoidal244,
    thirdFullAxisComplexWindowPacket_solenoidal244,
    thirdFullAxisComplexWindowPacket_solenoidal244]
  ring

theorem thirdFullAxisPositiveThreePacket_contDiff244
    (ρ : ℝ) (hρ : 0 < ρ)
    (A B C : Freq244) (s t u : ℂ) :
    ContDiff ℝ ∞ (thirdFullAxisPositiveThreePacket244 ρ hρ A B C s t u) :=
  ((thirdFullAxisComplexWindowPacket_contDiff244 ρ hρ 0 A s).add
    (thirdFullAxisComplexWindowPacket_contDiff244 ρ hρ 1 B t)).add
    (thirdFullAxisComplexWindowPacket_contDiff244 ρ hρ 2 C u)

theorem thirdFullAxisPositiveThreePacket_hasCompactSupport244
    (ρ : ℝ) (hρ : 0 < ρ)
    (A B C : Freq244) (s t u : ℂ) :
    HasCompactSupport (thirdFullAxisPositiveThreePacket244 ρ hρ A B C s t u) :=
  ((thirdFullAxisComplexWindowPacket_hasCompactSupport244 ρ hρ 0 A s).add
    (thirdFullAxisComplexWindowPacket_hasCompactSupport244 ρ hρ 1 B t)).add
    (thirdFullAxisComplexWindowPacket_hasCompactSupport244 ρ hρ 2 C u)

/-- Hermitianization by complex conjugation at the reflected frequency. -/
noncomputable def thirdFullAxisHermitianize244
    (G : Freq244 → CPol244) (ξ : Freq244) (d : A3) : ℂ :=
  G ξ d + star (G (-ξ) d)

/-- Exact Fourier reality involution for any complex vector field. -/
theorem thirdFullAxisHermitianize_reality244
    (G : Freq244 → CPol244) (ξ : Freq244) :
    thirdFullAxisHermitianize244 G (-ξ) =
      fun d => star (thirdFullAxisHermitianize244 G ξ d) := by
  funext d
  simp [thirdFullAxisHermitianize244, star_add, add_comm]

/-- Hermitianization preserves the complex frequency divergence equation. -/
theorem thirdFullAxisHermitianize_solenoidal244
    (G : Freq244 → CPol244)
    (hG : ∀ ξ, thirdFullAxisComplexDot244 ξ (G ξ) = 0)
    (ξ : Freq244) :
    thirdFullAxisComplexDot244 ξ (thirdFullAxisHermitianize244 G ξ) = 0 := by
  have hOpp : thirdFullAxisComplexDot244 ξ (G (-ξ)) = 0 := by
    have h := hG (-ξ)
    rw [thirdFullAxisComplexDot_neg_freq244] at h
    exact neg_eq_zero.mp h
  change thirdFullAxisComplexDot244 ξ
    (fun d => G ξ d + star (G (-ξ) d)) = 0
  rw [thirdFullAxisComplexDot_add244,
    thirdFullAxisComplexDot_star244, hG ξ, hOpp]
  simp

/-- The reflected-conjugate packet is smooth, with no regularity lost at
frequency zero. -/
theorem thirdFullAxisHermitianize_contDiff244
    (G : Freq244 → CPol244) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (thirdFullAxisHermitianize244 G) := by
  have hReflect : ContDiff ℝ ∞ (fun ξ : Freq244 => G (-ξ)) :=
    hG.comp contDiff_id.neg
  have hConj : ContDiff ℝ ∞
      (fun ξ : Freq244 => fun d : A3 => star (G (-ξ) d)) := by
    apply contDiff_pi'
    intro d
    have hComponent : ContDiff ℝ ∞ (fun ξ : Freq244 => G (-ξ) d) :=
      (contDiff_apply ℝ ℂ d).comp hReflect
    have h := Complex.conjCLE.contDiff.comp hComponent
    simpa only [Function.comp_def, Complex.conjCLE_apply, Complex.star_def] using h
  exact hG.add hConj

/-- Reflected compact supports remain compact. -/
theorem thirdFullAxisHermitianize_hasCompactSupport244
    (G : Freq244 → CPol244) (hG : HasCompactSupport G) :
    HasCompactSupport (thirdFullAxisHermitianize244 G) := by
  have hReflect : HasCompactSupport (fun ξ : Freq244 => G (-ξ)) := by
    simpa only [Function.comp_def, Homeomorph.coe_neg] using
      hG.comp_homeomorph (Homeomorph.neg Freq244)
  have hConj : HasCompactSupport
      (fun ξ : Freq244 => fun d : A3 => star (G (-ξ) d)) := by
    let J : CPol244 → CPol244 := fun v d => star (v d)
    have hJ0 : J 0 = 0 := by
      funext d
      simp [J]
    have h := hReflect.comp_left (g := J) hJ0
    simpa only [J, Function.comp_def] using h
  exact hG.add hConj

/-- The six-packet field with phase product I at the primary triad. -/
noncomputable def thirdFullAxisSixFourierPacket244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    Freq244 → CPol244 :=
  thirdFullAxisHermitianize244
    (thirdFullAxisPositiveThreePacket244 ρ hρ A B C 1 1 Complex.I)

theorem thirdFullAxisSixFourierPacket_solenoidal244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : Freq244) :
    thirdFullAxisComplexDot244 ξ (thirdFullAxisSixFourierPacket244 ρ hρ A B C ξ) = 0 :=
  thirdFullAxisHermitianize_solenoidal244 _
    (thirdFullAxisPositiveThreePacket_solenoidal244 ρ hρ A B C 1 1 Complex.I) ξ

theorem thirdFullAxisSixFourierPacket_reality244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : Freq244) :
    thirdFullAxisSixFourierPacket244 ρ hρ A B C (-ξ) =
      fun d => star (thirdFullAxisSixFourierPacket244 ρ hρ A B C ξ d) :=
  thirdFullAxisHermitianize_reality244 _ ξ

theorem thirdFullAxisSixFourierPacket_contDiff244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    ContDiff ℝ ∞ (thirdFullAxisSixFourierPacket244 ρ hρ A B C) :=
  thirdFullAxisHermitianize_contDiff244 _
    (thirdFullAxisPositiveThreePacket_contDiff244 ρ hρ A B C 1 1 Complex.I)

theorem thirdFullAxisSixFourierPacket_hasCompactSupport244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    HasCompactSupport (thirdFullAxisSixFourierPacket244 ρ hρ A B C) :=
  thirdFullAxisHermitianize_hasCompactSupport244 _
    (thirdFullAxisPositiveThreePacket_hasCompactSupport244 ρ hρ A B C 1 1 Complex.I)

/-- A genuine complex vector Schwartz map on `Axis Depth.three`, with
compactly supported Fourier profile. -/
noncomputable def thirdFullAxisSixSchwartzPacket244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    𝓢(Freq244, CPol244) :=
  (thirdFullAxisSixFourierPacket_hasCompactSupport244 ρ hρ A B C).toSchwartzMap
    (thirdFullAxisSixFourierPacket_contDiff244 ρ hρ A B C)

@[simp] theorem thirdFullAxisSixSchwartzPacket_apply244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : Freq244) :
    thirdFullAxisSixSchwartzPacket244 ρ hρ A B C ξ =
      thirdFullAxisSixFourierPacket244 ρ hρ A B C ξ := rfl

theorem thirdFullAxisSixSchwartzPacket_solenoidal244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : Freq244) :
    thirdFullAxisComplexDot244 ξ (thirdFullAxisSixSchwartzPacket244 ρ hρ A B C ξ) = 0 := by
  rw [thirdFullAxisSixSchwartzPacket_apply244]
  exact thirdFullAxisSixFourierPacket_solenoidal244 ρ hρ A B C ξ

theorem thirdFullAxisSixSchwartzPacket_reality244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : Freq244) :
    thirdFullAxisSixSchwartzPacket244 ρ hρ A B C (-ξ) =
      fun d => star (thirdFullAxisSixSchwartzPacket244 ρ hρ A B C ξ d) := by
  simp only [thirdFullAxisSixSchwartzPacket_apply244]
  exact thirdFullAxisSixFourierPacket_reality244 ρ hρ A B C ξ

end
end PrimeTensor.FirstMonomialTriad
