import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdAxisSchwartzPacket244
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Exact inverse Fourier realization of the full-third Hermitian axis packet

The preceding module constructs an actual Schwartz Fourier field on the
coordinate carrier `Axis Depth.three → ℝ`.  The exact third-order physical
Fourier identity instead lives on the Euclidean Hilbert carrier
`H3FourierPoint3`.  We transport each Schwartz coordinate component through
the standard PiLp continuous linear equivalence and take its inverse Fourier
transform.  Mathlib Fourier inversion then proves that the recovered spectral
vector is EXACTLY the six-packet field, with its physical axis indices,
Hermitian symmetry and frequency divergence unchanged.

In particular, this is an actual complex spatial Schwartz field whose
Fourier transform is the frequency-localized packet—not merely a pointwise
polynomial symbol.  The separate converse Hermitian-to-real argument and the
full signed 12-sector physical integral are not claimed here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped SchwartzMap FourierTransform Topology

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev CPol244 := A3 → ℂ
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdInverse244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Extract an actual scalar Schwartz Fourier component from the
vector-valued full-third axis packet. -/
noncomputable def thirdFullAxisSixFourierComponent244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (j : A3) :
    𝓢(Freq244, ℂ) :=
  (SchwartzMap.postcompCLM (𝕜 := ℝ)
    (ContinuousLinearMap.proj j : CPol244 →L[ℝ] ℂ))
      (thirdFullAxisSixSchwartzPacket244 ρ hρ A B C)

@[simp] theorem thirdFullAxisSixFourierComponent_apply244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j : A3) (ξ : Freq244) :
    thirdFullAxisSixFourierComponent244 ρ hρ A B C j ξ =
      thirdFullAxisSixFourierPacket244 ρ hρ A B C ξ j := rfl

/-- Transfer coordinate-frequency data to precisely the Euclidean carrier
used by the H3 Schwartz Fourier integration theorems. -/
noncomputable def thirdFullAxisHilbertFourierComponent244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (j : A3) :
    𝓢(V3, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : A3 => ℝ))
    (thirdFullAxisSixFourierComponent244 ρ hρ A B C j)

@[simp] theorem thirdFullAxisHilbertFourierComponent_apply244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j : A3) (ξ : V3) :
    thirdFullAxisHilbertFourierComponent244 ρ hρ A B C j ξ =
      thirdFullAxisSixFourierPacket244 ρ hρ A B C (WithLp.ofLp ξ) j := by
  change thirdFullAxisSixFourierComponent244 ρ hρ A B C j (WithLp.ofLp ξ) = _
  exact thirdFullAxisSixFourierComponent_apply244 ρ hρ A B C j (WithLp.ofLp ξ)

/-- The physical-space complex Schwartz component obtained by INVERSE
Fourier transform of the compact Hermitian axis spectrum. -/
noncomputable def thirdFullAxisInverseSchwartzComponent244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (j : A3) :
    𝓢(V3, ℂ) :=
  𝓕⁻ (thirdFullAxisHilbertFourierComponent244 ρ hρ A B C j)

/-- Exact Fourier inversion on the real three-dimensional Hilbert carrier.
No density limit and no formal inverse at the polynomial level are used. -/
theorem thirdFullAxisInverseSchwartz_fourier_component244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (j : A3) :
    𝓕 (thirdFullAxisInverseSchwartzComponent244 ρ hρ A B C j) =
      thirdFullAxisHilbertFourierComponent244 ρ hρ A B C j :=
  FourierTransform.fourier_fourierInv_eq _

/-- Pointwise recovery of the ENTIRE vector frequency profile, with the
original physical axis order and no Fourier normalization discrepancy. -/
theorem thirdFullAxisInverseSchwartz_fourier_vector244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : V3) :
    (fun j : A3 =>
      𝓕 (thirdFullAxisInverseSchwartzComponent244 ρ hρ A B C j) ξ) =
      thirdFullAxisSixFourierPacket244 ρ hρ A B C (WithLp.ofLp ξ) := by
  funext j
  rw [thirdFullAxisInverseSchwartz_fourier_component244]
  exact thirdFullAxisHilbertFourierComponent_apply244 ρ hρ A B C j ξ

/-- The actual spatial inverse field has a solenoidal Fourier transform at
EVERY Hilbert frequency (including the origin). -/
theorem thirdFullAxisInverseSchwartz_fourier_divergence244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : V3) :
    thirdFullAxisComplexDot244 (WithLp.ofLp ξ)
      (fun j : A3 =>
        𝓕 (thirdFullAxisInverseSchwartzComponent244 ρ hρ A B C j) ξ) = 0 := by
  rw [thirdFullAxisInverseSchwartz_fourier_vector244]
  exact thirdFullAxisSixFourierPacket_solenoidal244 ρ hρ A B C (WithLp.ofLp ξ)

/-- The recovered spectral vector is exactly Hermitian on the physical
Hilbert carrier.  This is the frequency-space reality condition that a
subsequent theorem can use to construct a *real*-valued spatial field. -/
theorem thirdFullAxisInverseSchwartz_fourier_hermitian244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : V3) :
    (fun j : A3 =>
      𝓕 (thirdFullAxisInverseSchwartzComponent244 ρ hρ A B C j) (-ξ)) =
      (fun j : A3 =>
        star (𝓕 (thirdFullAxisInverseSchwartzComponent244 ρ hρ A B C j) ξ)) := by
  funext j
  simp only [thirdFullAxisInverseSchwartz_fourier_component244,
    thirdFullAxisHilbertFourierComponent_apply244, WithLp.ofLp_neg]
  exact congrFun
    (thirdFullAxisSixFourierPacket_reality244 ρ hρ A B C (WithLp.ofLp ξ)) j

end
end PrimeTensor.FirstMonomialTriad
