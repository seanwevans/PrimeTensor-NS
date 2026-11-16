import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3WienerOrderedConvolution
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# Complex Euclidean Leray multiplier and uniform Z3 ordered-source bound

The physical Fourier polarization norm is the Euclidean ℓ² norm of
`EuclideanSpace ℂ (Fin 3)`, NOT the coordinatewise sup norm. At each actual
integer frequency `n`, the Leray multiplier is the complex orthogonal
projection off the span of the real frequency vector. Its operator norm is
at most one, including the zero-frequency case.

The ordered Navier--Stokes transport term is `-i (q·u_p) v_q`, followed by
the Leray projection at `p+q`. Cauchy--Schwarz and contraction show its
norm is at most `‖q‖₂ * ‖u_p‖₂ * ‖v_q‖₂` without any finite-support factor.

The last theorem composes that exact complex Hilbert-space bound with the
previous genuine Z3 weighted ordered convolution, CONDITIONAL ONLY on the
scalar comparison `‖q‖₂ ≤ |q|₁` for the finite second support. Establishing
that lattice inequality in Lean, the coordinate formula for this projector,
Galerkin norm differentiation, and the PDE limit are separate obligations.

This does not add a native additive operation to prime-multiset tensors or
assert a Navier--Stokes continuation theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

private abbrev ComplexBand244 := EuclideanSpace ℂ (Fin 3)

/-- The physical complexification of an actual Z3 frequency. -/
def thirdFullThreeBandZ3ComplexFrequency244
    (n : thirdFullThreeBandZ3Index244) : ComplexBand244 :=
  WithLp.toLp 2 (fun j : Fin 3 => (n j : ℂ))

/-- The genuine Euclidean Leray multiplier, orthogonal to the frequency line.
At n=0 the projection is the identity; nonzero mode is the usual Leray map. -/
def thirdFullThreeBandZ3ComplexLeray244
    (n : thirdFullThreeBandZ3Index244) :
    ComplexBand244 →L[ℂ] ComplexBand244 :=
  ((ℂ ∙ thirdFullThreeBandZ3ComplexFrequency244 n)ᗮ).starProjection

/-- The complex Euclidean Leray multiplier is a contraction at every lattice
frequency; no dimension or cutoff constant appears. -/
theorem thirdFullThreeBand_z3ComplexLeray_norm_le244
    (n : thirdFullThreeBandZ3Index244) (F : ComplexBand244) :
    ‖thirdFullThreeBandZ3ComplexLeray244 n F‖ ≤ ‖F‖ := by
  exact Submodule.norm_starProjection_apply_le
    ((ℂ ∙ thirdFullThreeBandZ3ComplexFrequency244 n)ᗮ) F

/-- The full complex-linear multiplier has operator norm at most one. -/
theorem thirdFullThreeBand_z3ComplexLeray_operatorNorm_le244
    (n : thirdFullThreeBandZ3Index244) :
    ‖thirdFullThreeBandZ3ComplexLeray244 n‖ ≤ 1 := by
  exact Submodule.starProjection_norm_le
    ((ℂ ∙ thirdFullThreeBandZ3ComplexFrequency244 n)ᗮ)

/-- One ordered complex Navier--Stokes quadratic Fourier interaction,
projected at its OUTPUT mode: `-i P_n [(q·u_p) v_q]`.
The usual `q·u_p` is the complex inner product with the REAL lattice q. -/
def thirdFullThreeBandZ3ComplexTransport244
    (n q : thirdFullThreeBandZ3Index244)
    (u v : ComplexBand244) : ComplexBand244 :=
  thirdFullThreeBandZ3ComplexLeray244 n
    ((-Complex.I * inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 q) u) • v)

/-- Contractivity plus complex Cauchy--Schwarz for the TRUE ordered source.
The multiplier depends on the output n, not on either input mode. -/
theorem thirdFullThreeBand_z3ComplexTransport_norm_le244
    (n q : thirdFullThreeBandZ3Index244)
    (u v : ComplexBand244) :
    ‖thirdFullThreeBandZ3ComplexTransport244 n q u v‖ ≤
      ‖thirdFullThreeBandZ3ComplexFrequency244 q‖ * ‖u‖ * ‖v‖ := by
  unfold thirdFullThreeBandZ3ComplexTransport244
  calc
    ‖thirdFullThreeBandZ3ComplexLeray244 n
       ((-Complex.I * inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 q) u) • v)‖
        ≤ ‖(-Complex.I * inner ℂ
              (thirdFullThreeBandZ3ComplexFrequency244 q) u) • v‖ :=
          thirdFullThreeBand_z3ComplexLeray_norm_le244 n _
    _ = ‖inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 q) u‖ * ‖v‖ := by
      simp [norm_smul, norm_mul]
    _ ≤ (‖thirdFullThreeBandZ3ComplexFrequency244 q‖ * ‖u‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (norm_inner_le_norm (thirdFullThreeBandZ3ComplexFrequency244 q) u)
        (norm_nonneg v)
    _ = ‖thirdFullThreeBandZ3ComplexFrequency244 q‖ * ‖u‖ * ‖v‖ := by
      ring

/-- All projected ordered pairs satisfy the exact W_r D_r bound, provided
the (explicit) Fourier lattice l2-to-l1 comparison has been supplied.
Every pair survives even if its output is absent from both input supports. -/
theorem thirdFullThreeBand_z3ComplexOrderedWienerBound244
    (r : ℝ) (hr : 0 ≤ r)
    (s t : Finset thirdFullThreeBandZ3Index244)
    (u v : thirdFullThreeBandZ3Index244 → ComplexBand244)
    (hFrequency : ∀ q ∈ t,
      ‖thirdFullThreeBandZ3ComplexFrequency244 q‖ ≤
        thirdFullThreeBandZ3Degree244 q) :
    (∑ p ∈ s, ∑ q ∈ t,
      thirdFullThreeBandZ3Weight244 r (p + q) *
        ‖thirdFullThreeBandZ3ComplexTransport244 (p + q) q (u p) (v q)‖) ≤
      (∑ p ∈ s, thirdFullThreeBandZ3Weight244 r p * ‖u p‖) *
      (∑ q ∈ t, thirdFullThreeBandZ3Weight244 r q *
        thirdFullThreeBandZ3Degree244 q * ‖v q‖) := by
  classical
  apply thirdFullThreeBand_z3GalerkinSourceMajorant244
    r hr s t (fun p => ‖u p‖) (fun q => ‖v q‖)
    (fun p q => thirdFullThreeBandZ3Weight244 r (p + q) *
      ‖thirdFullThreeBandZ3ComplexTransport244 (p + q) q (u p) (v q)‖)
    (fun p => norm_nonneg (u p)) (fun q => norm_nonneg (v q))
  intro p hp q hq
  have hSrc := thirdFullThreeBand_z3ComplexTransport_norm_le244
    (p + q) q (u p) (v q)
  have hFreq := hFrequency q hq
  have hPair :
      ‖thirdFullThreeBandZ3ComplexTransport244 (p + q) q (u p) (v q)‖ ≤
        thirdFullThreeBandZ3Degree244 q * ‖u p‖ * ‖v q‖ := by
    calc
      _ ≤ ‖thirdFullThreeBandZ3ComplexFrequency244 q‖ * ‖u p‖ * ‖v q‖ := hSrc
      _ = ‖thirdFullThreeBandZ3ComplexFrequency244 q‖ *
            (‖u p‖ * ‖v q‖) := by ring
      _ ≤ thirdFullThreeBandZ3Degree244 q *
            (‖u p‖ * ‖v q‖) :=
          mul_le_mul_of_nonneg_right hFreq
            (mul_nonneg (norm_nonneg (u p)) (norm_nonneg (v q)))
      _ = _ := by ring
  calc
    _ ≤ thirdFullThreeBandZ3Weight244 r (p + q) *
          (thirdFullThreeBandZ3Degree244 q * ‖u p‖ * ‖v q‖) :=
        mul_le_mul_of_nonneg_left hPair
          (thirdFullThreeBand_z3Weight_pos244 r (p + q)).le
    _ = _ := by ring

end
end PrimeTensor.FirstMonomialTriad
