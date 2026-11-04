import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSchwartzOrderedIntegrability
import Mathlib.Tactic

/-!
# Reindex the actual five-axis full-third Schwartz Fourier density

For every complex Schwartz field, all four original 3+3+1 gradient patterns
and the full 3+2+2 interpolation pattern can be combined only after the
three independent derivative axes have been summed. This module proves the
exact reindexing without a real-polarization substitution, frequency cutoff,
extra conjugation or spectral localization. The result identifies the
*unphased half-physical frequency density* with the previously established
corrected ordered kernel, and therefore with its sixth-power flux integral.

This does not yet equate the unphased density's integral to the original
spatial fullSchwartzThirdCommutator244: the common Fourier phase, physical
energy coefficient two, and original integral/sum interchange remain to be
matched in a subsequent theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypePhysicalSeven244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

private noncomputable def physicalG1 (u : A3 → SchwartzMap V3 ℂ)
    (j m i k l : A3) (z : V3 × V3) : ℂ :=
  thirdGradientSchwartzKernel244 (u j) (u m) (u j)
    (h3FourierAxisDirection i) (h3FourierAxisDirection k)
    (h3FourierAxisDirection l) (h3FourierAxisDirection i)
    (h3FourierAxisDirection k) (h3FourierAxisDirection l)
    (h3FourierAxisDirection m) z

private noncomputable def physicalG2 (u : A3 → SchwartzMap V3 ℂ)
    (j m i k l : A3) (z : V3 × V3) : ℂ :=
  thirdGradientSchwartzKernel244 (u j) (u j) (u m)
    (h3FourierAxisDirection i) (h3FourierAxisDirection k)
    (h3FourierAxisDirection l) (h3FourierAxisDirection i)
    (h3FourierAxisDirection k) (h3FourierAxisDirection m)
    (h3FourierAxisDirection l) z

private noncomputable def physicalG3 (u : A3 → SchwartzMap V3 ℂ)
    (j m i k l : A3) (z : V3 × V3) : ℂ :=
  thirdGradientSchwartzKernel244 (u j) (u j) (u m)
    (h3FourierAxisDirection i) (h3FourierAxisDirection k)
    (h3FourierAxisDirection l) (h3FourierAxisDirection i)
    (h3FourierAxisDirection m) (h3FourierAxisDirection l)
    (h3FourierAxisDirection k) z

private noncomputable def physicalG4 (u : A3 → SchwartzMap V3 ℂ)
    (j m i k l : A3) (z : V3 × V3) : ℂ :=
  thirdGradientSchwartzKernel244 (u j) (u j) (u m)
    (h3FourierAxisDirection i) (h3FourierAxisDirection k)
    (h3FourierAxisDirection l) (h3FourierAxisDirection m)
    (h3FourierAxisDirection k) (h3FourierAxisDirection l)
    (h3FourierAxisDirection i) z

private noncomputable def physicalI (u : A3 → SchwartzMap V3 ℂ)
    (j m i k l : A3) (z : V3 × V3) : ℂ :=
  h3FirstMonomialSchwartzKernel (u j) (u m) (u j)
    (h3FourierAxisDirection i) (h3FourierAxisDirection k)
    (h3FourierAxisDirection l) (h3FourierAxisDirection m) z

/-- The literal FOUR physical gradient placements plus THREE copies of the
interpolation density, before the common factor `2*(2*pi*I)^7`.
All five indices remain explicit. -/
noncomputable def thirdFullSchwartzPhysicalHalfSevenKernel244
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) : ℂ :=
  ∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
    (physicalG1 u j m i k l z + physicalG2 u j m i k l z +
      physicalG3 u j m i k l z + physicalG4 u j m i k l z +
      3 * physicalI u j m i k l z)

private theorem triple_swap_last (F : A3 → A3 → A3 → ℂ) :
    (∑ i : A3, ∑ k : A3, ∑ l : A3, F i l k) =
      ∑ i : A3, ∑ k : A3, ∑ l : A3, F i k l := by
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

private theorem triple_swap_first_last (F : A3 → A3 → A3 → ℂ) :
    (∑ i : A3, ∑ k : A3, ∑ l : A3, F l k i) =
      ∑ i : A3, ∑ k : A3, ∑ l : A3, F i k l := by
  calc
    _ = ∑ k : A3, ∑ i : A3, ∑ l : A3, F l k i := Finset.sum_comm
    _ = ∑ k : A3, ∑ l : A3, ∑ i : A3, F l k i := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = ∑ l : A3, ∑ k : A3, ∑ i : A3, F l k i := Finset.sum_comm
    _ = _ := rfl

private theorem triple_rotate (F : A3 → A3 → A3 → ℂ) :
    (∑ i : A3, ∑ k : A3, ∑ l : A3, F l i k) =
      ∑ i : A3, ∑ k : A3, ∑ l : A3, F i k l := by
  calc
    _ = ∑ i : A3, ∑ l : A3, ∑ k : A3, F l i k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ l : A3, ∑ i : A3, ∑ k : A3, F l i k := Finset.sum_comm
    _ = _ := rfl

/-- The third gradient placement is the second with its k/l derivative
indices exchanged. The equality is pointwise in momentum, but not generally
at the same index triple. -/
private theorem physicalG3_rotate
    (u : A3 → SchwartzMap V3 ℂ) (j m i k l : A3) (z : V3 × V3) :
    physicalG3 u j m i k l z = physicalG2 u j m i l k z := by
  unfold physicalG3 physicalG2 thirdGradientSchwartzKernel244
  simp only [inner_h3FourierAxisDirection]
  ring

/-- The fourth gradient placement is likewise the second with its outer
and inner derivative indices exchanged. -/
private theorem physicalG4_rotate
    (u : A3 → SchwartzMap V3 ℂ) (j m i k l : A3) (z : V3 × V3) :
    physicalG4 u j m i k l z = physicalG2 u j m l k i z := by
  unfold physicalG4 physicalG2 thirdGradientSchwartzKernel244
  simp only [inner_h3FourierAxisDirection]
  ring

/-- FINITE-INDEX BRIDGE. The physical four-gradient/three-interpolation
unphased density agrees with the corrected ordered Schwartz Fourier symbol
for all complex Schwartz Fourier amplitudes, without assuming divergence.
The three gradient derivative placements are reindexed BEFORE combining. -/
theorem thirdFullSchwartzPhysicalHalfSeven_eq_ordered244
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) :
    thirdFullSchwartzPhysicalHalfSevenKernel244 u z =
      thirdFullSchwartzComplexOrderedKernel244 u z := by
  have hOrdered := thirdFullSchwartzComplexOrdered_eq_sevenKernel244 u z
  rw [hOrdered]
  have hG3 (j m : A3) :
      (∑ i : A3, ∑ k : A3, ∑ l : A3, physicalG3 u j m i k l z) =
        ∑ i : A3, ∑ k : A3, ∑ l : A3, physicalG2 u j m i k l z := by
    calc
      _ = ∑ i : A3, ∑ k : A3, ∑ l : A3,
          physicalG2 u j m i l k z := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        exact physicalG3_rotate u j m i k l z
      _ = _ := triple_swap_last (fun i k l => physicalG2 u j m i k l z)
  have hG4 (j m : A3) :
      (∑ i : A3, ∑ k : A3, ∑ l : A3, physicalG4 u j m i k l z) =
        ∑ i : A3, ∑ k : A3, ∑ l : A3, physicalG2 u j m i k l z := by
    calc
      _ = ∑ i : A3, ∑ k : A3, ∑ l : A3,
          physicalG2 u j m l k i z := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        exact physicalG4_rotate u j m i k l z
      _ = _ := triple_swap_first_last
        (fun i k l => physicalG2 u j m i k l z)
  have hI (j m : A3) :
      (∑ i : A3, ∑ k : A3, ∑ l : A3, physicalI u j m i k l z) =
        ∑ i : A3, ∑ k : A3, ∑ l : A3, physicalI u j m l i k z := by
    exact (triple_rotate (fun i k l => physicalI u j m i k l z)).symm
  have hSummands (j m : A3) :
      (∑ i : A3, ∑ k : A3, ∑ l : A3,
        (physicalG1 u j m i k l z + physicalG2 u j m i k l z +
          physicalG3 u j m i k l z + physicalG4 u j m i k l z +
          3 * physicalI u j m i k l z)) =
      ∑ i : A3, ∑ k : A3, ∑ l : A3,
        (physicalG1 u j m i k l z +
          3 * physicalI u j m l i k z +
          3 * physicalG2 u j m i k l z) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hG3 j m, hG4 j m, hI j m]
    ring
  unfold thirdFullSchwartzPhysicalHalfSevenKernel244
    thirdFullSchwartzOrderedSevenKernel244
  change (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
    (physicalG1 u j m i k l z + physicalG2 u j m i k l z +
      physicalG3 u j m i k l z + physicalG4 u j m i k l z +
      3 * physicalI u j m i k l z)) =
    ∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
      (physicalG1 u j m i k l z +
        3 * physicalI u j m l i k z +
        3 * physicalG2 u j m i k l z)
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro m _
  exact hSummands j m

/-- Genuine absolute integrability of the full four-pattern plus
interpolation physical Fourier density, for every Schwartz field. -/
theorem thirdFullSchwartzPhysicalHalfSeven_integrable244
    (u : A3 → SchwartzMap V3 ℂ) :
    Integrable (thirdFullSchwartzPhysicalHalfSevenKernel244 u)
      (volume.prod volume) := by
  exact (thirdFullSchwartzComplexOrderedKernel_integrable244 u).congr
    (Filter.Eventually.of_forall (fun z =>
      (thirdFullSchwartzPhysicalHalfSeven_eq_ordered244 u z).symm))

/-- The unrestricted complex sixth-power flux is exactly six times the
integral of the original FOUR physical gradient placements together with
THREE interpolation copies, after the five index sums. The common physical
Fourier phase and outer energy factor are not applied in this theorem. -/
theorem thirdFullSchwartzPhysicalHalfSeven_flux_integral244
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ ξ : A3 → ℝ,
      mixedDot ξ (h3SchwartzTriadPolarization u ξ) = 0) :
    (∫ z : V3 × V3,
      thirdFullSchwartzComplexSixthPowerFlux244 u z
        ∂volume.prod volume) =
      6 * ∫ z : V3 × V3,
        thirdFullSchwartzPhysicalHalfSevenKernel244 u z
          ∂volume.prod volume := by
  rw [thirdFullSchwartzComplexSixthPowerFlux_integral244 u hDiv]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z =>
    (thirdFullSchwartzPhysicalHalfSeven_eq_ordered244 u z).symm)

/-- No spectral divergence hypothesis for a REAL physical solenoidal
Schwartz field: reuse the already proved Point3-to-Fourier divergence bridge. -/
theorem thirdFullRealSchwartzPhysicalHalfSeven_flux_integral244
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f) :
    (∫ z : V3 × V3,
      thirdFullSchwartzComplexSixthPowerFlux244
        (fun j => h3SchwartzComplexify (f j)) z
        ∂volume.prod volume) =
      6 * ∫ z : V3 × V3,
        thirdFullSchwartzPhysicalHalfSevenKernel244
          (fun j => h3SchwartzComplexify (f j)) z
          ∂volume.prod volume := by
  rw [thirdFullRealSchwartz_sixthPowerFlux_integral244 f hDiv]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z =>
    (thirdFullSchwartzPhysicalHalfSeven_eq_ordered244
      (fun j => h3SchwartzComplexify (f j)) z).symm)

end
end PrimeTensor.FirstMonomialTriad
