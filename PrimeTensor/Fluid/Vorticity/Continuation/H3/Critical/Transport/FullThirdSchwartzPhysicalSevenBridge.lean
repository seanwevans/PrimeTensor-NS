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


/-! ## Exact physical Fourier phase and five-index integral normalization -/

/-- The four genuinely distinct gradient placements, prior to the common
physical coefficient `2 * (2*pi*I)^7`. -/
private noncomputable def physicalGradientHalfKernel
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) : ℂ :=
  ∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
    (physicalG1 u j m i k l z + physicalG2 u j m i k l z +
      physicalG3 u j m i k l z + physicalG4 u j m i k l z)

private theorem physicalGradient_integrabilities
    (u : A3 → SchwartzMap V3 ℂ) (j m i k l : A3) :
    Integrable (physicalG1 u j m i k l) (volume.prod volume) ∧
    Integrable (physicalG2 u j m i k l) (volume.prod volume) ∧
    Integrable (physicalG3 u j m i k l) (volume.prod volume) ∧
    Integrable (physicalG4 u j m i k l) (volume.prod volume) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact thirdGradientSchwartzKernel_integrable244 (u j) (u m) (u j)
      (h3FourierAxisDirection i) (h3FourierAxisDirection k)
      (h3FourierAxisDirection l) (h3FourierAxisDirection i)
      (h3FourierAxisDirection k) (h3FourierAxisDirection l)
      (h3FourierAxisDirection m)
  · exact thirdGradientSchwartzKernel_integrable244 (u j) (u j) (u m)
      (h3FourierAxisDirection i) (h3FourierAxisDirection k)
      (h3FourierAxisDirection l) (h3FourierAxisDirection i)
      (h3FourierAxisDirection k) (h3FourierAxisDirection m)
      (h3FourierAxisDirection l)
  · exact thirdGradientSchwartzKernel_integrable244 (u j) (u j) (u m)
      (h3FourierAxisDirection i) (h3FourierAxisDirection k)
      (h3FourierAxisDirection l) (h3FourierAxisDirection i)
      (h3FourierAxisDirection m) (h3FourierAxisDirection l)
      (h3FourierAxisDirection k)
  · exact thirdGradientSchwartzKernel_integrable244 (u j) (u j) (u m)
      (h3FourierAxisDirection i) (h3FourierAxisDirection k)
      (h3FourierAxisDirection l) (h3FourierAxisDirection m)
      (h3FourierAxisDirection k) (h3FourierAxisDirection l)
      (h3FourierAxisDirection i)

private theorem physicalGradientSlot_integrable
    (u : A3 → SchwartzMap V3 ℂ) (j m i k l : A3) :
    Integrable (fun z : V3 × V3 =>
      physicalG1 u j m i k l z + physicalG2 u j m i k l z +
      physicalG3 u j m i k l z + physicalG4 u j m i k l z)
      (volume.prod volume) := by
  obtain ⟨h1, h2, h3, h4⟩ := physicalGradient_integrabilities u j m i k l
  exact ((h1.add h2).add h3).add h4

private theorem physicalGradientSlot_integral
    (u : A3 → SchwartzMap V3 ℂ) (j m i k l : A3) :
    (∫ z : V3 × V3,
      (physicalG1 u j m i k l z + physicalG2 u j m i k l z +
       physicalG3 u j m i k l z + physicalG4 u j m i k l z)
        ∂volume.prod volume) =
    (((∫ z : V3 × V3, physicalG1 u j m i k l z ∂volume.prod volume) +
       (∫ z : V3 × V3, physicalG2 u j m i k l z ∂volume.prod volume)) +
       (∫ z : V3 × V3, physicalG3 u j m i k l z ∂volume.prod volume)) +
       (∫ z : V3 × V3, physicalG4 u j m i k l z ∂volume.prod volume) := by
  obtain ⟨h1, h2, h3, h4⟩ := physicalGradient_integrabilities u j m i k l
  -- Work with literal Pi-function addition.  Rewriting under the outer
  -- integral-add equality is fragile: the nested integral is not an actual
  -- subexpression of its left side.  Apply each integral-add equality at
  -- the corresponding stage, using congrArg for the surrounding sums.
  let μ : Measure (V3 × V3) := volume.prod volume
  let g1 : V3 × V3 → ℂ := physicalG1 u j m i k l
  let g2 : V3 × V3 → ℂ := physicalG2 u j m i k l
  let g3 : V3 × V3 → ℂ := physicalG3 u j m i k l
  let g4 : V3 × V3 → ℂ := physicalG4 u j m i k l
  have i1 : Integrable g1 μ := h1
  have i2 : Integrable g2 μ := h2
  have i3 : Integrable g3 μ := h3
  have i4 : Integrable g4 μ := h4
  change (∫ z : V3 × V3, (g1 + g2 + g3 + g4) z ∂μ) =
    (((∫ z : V3 × V3, g1 z ∂μ) +
      (∫ z : V3 × V3, g2 z ∂μ)) +
      (∫ z : V3 × V3, g3 z ∂μ)) +
      (∫ z : V3 × V3, g4 z ∂μ)
  calc
    _ = (∫ z : V3 × V3, (g1 + g2 + g3) z ∂μ) +
        (∫ z : V3 × V3, g4 z ∂μ) :=
      integral_add ((i1.add i2).add i3) i4
    _ = ((∫ z : V3 × V3, (g1 + g2) z ∂μ) +
          (∫ z : V3 × V3, g3 z ∂μ)) +
          (∫ z : V3 × V3, g4 z ∂μ) :=
      congrArg (fun w : ℂ =>
        w + (∫ z : V3 × V3, g4 z ∂μ))
        (integral_add (i1.add i2) i3)
    _ = _ :=
      congrArg (fun w : ℂ =>
        (w + (∫ z : V3 × V3, g3 z ∂μ)) +
          (∫ z : V3 × V3, g4 z ∂μ))
        (integral_add i1 i2)

/-- Reorder all five *finite* physical coordinate sums, putting the advecting
velocity component back into its original position. -/
private theorem physicalFiveSum_moveSecond
    (F : A3 → A3 → A3 → A3 → A3 → ℂ) :
    (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
      F j m i k l) =
    ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ m : A3,
      F j m i k l := by
  calc
    _ = ∑ j : A3, ∑ i : A3, ∑ m : A3, ∑ k : A3, ∑ l : A3,
          F j m i k l := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ m : A3, ∑ l : A3,
          F j m i k l := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm

private theorem physicalGradientHalf_integrable
    (u : A3 → SchwartzMap V3 ℂ) :
    Integrable (physicalGradientHalfKernel u) (volume.prod volume) := by
  unfold physicalGradientHalfKernel
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro m _
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro l _
  exact physicalGradientSlot_integrable u j m i k l

/-- All five gradient sums commute with the Fourier integral. The resulting
coefficient is precisely the original `thirdGradientFourierTotalComplex244`,
including its physical factor two and its exact seventh-order phase. -/
theorem thirdFullSchwartzGradientFourier_eq_halfIntegral244
    (u : A3 → SchwartzMap V3 ℂ) :
    thirdGradientFourierTotalComplex244 u =
      (2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
        ∫ z : V3 × V3, physicalGradientHalfKernel u z
          ∂volume.prod volume := by
  let c : ℂ := 2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7
  have hSlot (j m i k l : A3) :
      thirdGradientSchwartzAxisFourier244 u j i k l m =
        c * (∫ z : V3 × V3,
          (physicalG1 u j m i k l z + physicalG2 u j m i k l z +
            physicalG3 u j m i k l z + physicalG4 u j m i k l z)
            ∂volume.prod volume) := by
    change c *
      (((∫ z : V3 × V3, physicalG1 u j m i k l z ∂volume.prod volume) +
         (∫ z : V3 × V3, physicalG2 u j m i k l z ∂volume.prod volume)) +
         (∫ z : V3 × V3, physicalG3 u j m i k l z ∂volume.prod volume) +
         (∫ z : V3 × V3, physicalG4 u j m i k l z ∂volume.prod volume)) = _
    rw [physicalGradientSlot_integral u j m i k l]
  have h4 (j m i k : A3) := integrable_finsetSum Finset.univ
    (fun l _ => physicalGradientSlot_integrable u j m i k l)
  have h3 (j m i : A3) := integrable_finsetSum Finset.univ
    (fun k _ => h4 j m i k)
  have h2 (j m : A3) := integrable_finsetSum Finset.univ
    (fun i _ => h3 j m i)
  have h1 (j : A3) := integrable_finsetSum Finset.univ
    (fun m _ => h2 j m)
  have hSumIntegral :
      (∫ z : V3 × V3, physicalGradientHalfKernel u z
        ∂volume.prod volume) =
      ∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
        ∫ z : V3 × V3,
          (physicalG1 u j m i k l z + physicalG2 u j m i k l z +
            physicalG3 u j m i k l z + physicalG4 u j m i k l z)
            ∂volume.prod volume := by
    unfold physicalGradientHalfKernel
    rw [integral_finsetSum Finset.univ (fun j _ => h1 j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum Finset.univ (fun m _ => h2 j m)]
    apply Finset.sum_congr rfl
    intro m _
    rw [integral_finsetSum Finset.univ (fun i _ => h3 j m i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun k _ => h4 j m i k)]
    apply Finset.sum_congr rfl
    intro k _
    exact integral_finsetSum Finset.univ
      (fun l _ => physicalGradientSlot_integrable u j m i k l)
  change thirdGradientFourierTotalComplex244 u =
    c * (∫ z : V3 × V3, physicalGradientHalfKernel u z
      ∂volume.prod volume)
  calc
    thirdGradientFourierTotalComplex244 u =
        ∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
          thirdGradientSchwartzAxisFourier244 u j i k l m := by
      unfold thirdGradientFourierTotalComplex244
      exact (physicalFiveSum_moveSecond
        (fun j m i k l => thirdGradientSchwartzAxisFourier244
          u j i k l m)).symm
    _ = ∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
          c * (∫ z : V3 × V3,
            (physicalG1 u j m i k l z + physicalG2 u j m i k l z +
              physicalG3 u j m i k l z + physicalG4 u j m i k l z)
              ∂volume.prod volume) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      exact hSlot j m i k l
    _ = c * (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
          ∫ z : V3 × V3,
            (physicalG1 u j m i k l z + physicalG2 u j m i k l z +
              physicalG3 u j m i k l z + physicalG4 u j m i k l z)
              ∂volume.prod volume) := by
      simp only [Finset.mul_sum]
    _ = _ := by rw [hSumIntegral]

/-- The five-index interpolation sum is exactly the preexisting trilinear
Schwartz Fourier kernel; the distinct order of its five dummy indices is
explicitly reindexed. -/
private theorem physicalInterpolationSum_eq_triad
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) :
    (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
      physicalI u j m i k l z) =
      h3SchwartzTriadKernel u z := by
  rw [h3SchwartzTriadKernel_eq_sum]
  change
    (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
      h3SchwartzFirstMonomialSlotKernel u i k l m j z) =
      ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ m : A3, ∑ j : A3,
        h3SchwartzFirstMonomialSlotKernel u i k l m j z
  simp only [axis_sum_three]
  ac_rfl

/-- Complete unphased, half-normalized physical density, separated into
its original four-gradient and interpolation contributions. -/
theorem thirdFullSchwartzPhysicalHalfSeven_eq_gradient_add_triad244
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) :
    thirdFullSchwartzPhysicalHalfSevenKernel244 u z =
      physicalGradientHalfKernel u z +
        3 * h3SchwartzTriadKernel u z := by
  calc
    _ = physicalGradientHalfKernel u z +
        3 * (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
          physicalI u j m i k l z) := by
      unfold thirdFullSchwartzPhysicalHalfSevenKernel244
        physicalGradientHalfKernel
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by rw [physicalInterpolationSum_eq_triad]

/-- **Unrestricted complex Fourier normalization.** The original four
physical gradient placements and the original interpolation coefficient six
are exactly twice the full corrected ordered density with the same seventh-
derivative phase. No solenoidality is needed for this analytic identity. -/
theorem thirdFullSchwartzPhysicalHalfSeven_fourierCoefficient244
    (u : A3 → SchwartzMap V3 ℂ) :
    thirdGradientFourierTotalComplex244 u +
      6 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        (∫ z : V3 × V3, h3SchwartzTriadKernel u z
          ∂volume.prod volume) =
      2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        (∫ z : V3 × V3,
          thirdFullSchwartzPhysicalHalfSevenKernel244 u z
          ∂volume.prod volume) := by
  have hG : Integrable (physicalGradientHalfKernel u)
      (volume.prod volume) := physicalGradientHalf_integrable u
  have hI : Integrable (h3SchwartzTriadKernel u)
      (volume.prod volume) := h3SchwartzTriadKernel_integrable u
  have hSum :
      (∫ z : V3 × V3,
          thirdFullSchwartzPhysicalHalfSevenKernel244 u z
            ∂volume.prod volume) =
        (∫ z : V3 × V3, physicalGradientHalfKernel u z
          ∂volume.prod volume) +
        3 * (∫ z : V3 × V3, h3SchwartzTriadKernel u z
          ∂volume.prod volume) := by
    calc
      _ = ∫ z : V3 × V3,
            (physicalGradientHalfKernel u z +
              3 * h3SchwartzTriadKernel u z)
              ∂volume.prod volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (thirdFullSchwartzPhysicalHalfSeven_eq_gradient_add_triad244 u)
      _ = (∫ z : V3 × V3, physicalGradientHalfKernel u z
            ∂volume.prod volume) +
          ∫ z : V3 × V3, 3 * h3SchwartzTriadKernel u z
            ∂volume.prod volume := integral_add hG (hI.const_mul (3 : ℂ))
      _ = _ := by rw [integral_const_mul]
  rw [thirdFullSchwartzGradientFourier_eq_halfIntegral244 u, hSum]
  ring

end
end PrimeTensor.FirstMonomialTriad
