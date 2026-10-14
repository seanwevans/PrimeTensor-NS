import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterCanonicalAxisReal
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Transport the noncancelling quarter-scale Fourier integral to the canonical axes

The constructed real Schwartz velocity is already on the physical H3 Hilbert
carrier. Here the two independent frequency variables are transported from
canonical Euclidean coordinates to the original Fin 3 coordinates. The change
of variables is product-volume-preserving: no Jacobian or Fourier phase is
inserted by reindexing. The complete six-order symbol is invariant under the
simultaneous permutation of frequency and polarization coordinates.

The final lemma identifies the full physically phased six-order integral on
the canonical carrier with the strictly negative integral established earlier
on Fin 3. No assertion about an arbitrary Navier--Stokes path is made here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory
open scoped SchwartzMap FourierTransform BigOperators

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3
private abbrev VFin := Fin 3 → ℝ
private abbrev PFin := VFin × VFin
private abbrev P3 := V3 × V3
private abbrev axes : Fin 3 ≃ A3 :=
  PrimeTensor.Bridge.Euclidean.h3Fin3EquivAxisThree

noncomputable local instance axisFintypeQuarterCanonicalIntegral (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Coordinate permutation on real frequencies preserves their product volume. -/
theorem lowNormalQuarterAxisToFin_measurePreserving :
    MeasurePreserving
      (lowNormalQuarterAxisToFin : (A3 → ℝ) → (Fin 3 → ℝ))
      volume volume := by
  have h := (volume_measurePreserving_piCongrLeft
    (fun _ : A3 => ℝ) axes).symm
      (MeasurableEquiv.piCongrLeft (fun _ : A3 => ℝ) axes)
  exact h

/-- The existing Euclidean-to-coordinate map is volume preserving, including
its canonical Hilbert norm. -/
theorem lowNormalQuarterAxisHilbertToFin_measurePreserving :
    MeasurePreserving (lowNormalQuarterAxisHilbertToFin : V3 → VFin)
      volume volume := by
  have h := lowNormalQuarterAxisToFin_measurePreserving.comp
    (PiLp.volume_preserving_ofLp A3)
  exact h

/-- The TWO momentum variables are transported with no multiplicative
Jacobian. -/
theorem lowNormalQuarterAxisHilbertToFin_prod_measurePreserving :
    MeasurePreserving
      (Prod.map lowNormalQuarterAxisHilbertToFin
        lowNormalQuarterAxisHilbertToFin : P3 → PFin)
      (volume.prod volume) (volume.prod volume) :=
  MeasurePreserving.prod
    lowNormalQuarterAxisHilbertToFin_measurePreserving
    lowNormalQuarterAxisHilbertToFin_measurePreserving

private theorem sum_axis_reindex {M : Type*} [AddCommMonoid M] (g : A3 → M) :
    (∑ j : A3, g j) = ∑ i : Fin 3, g (axes i) := by
  exact (Fintype.sum_equiv axes (fun i : Fin 3 => g (axes i)) g
    (fun i => rfl)).symm

private theorem dot_axis_reindex (p r : A3 → ℝ) :
    dot p r = dot (fun i : Fin 3 => p (axes i))
      (fun i : Fin 3 => r (axes i)) := by
  unfold dot
  exact sum_axis_reindex (fun j : A3 => p j * r j)

private theorem mixedDot_axis_reindex (p : A3 → ℝ) (a : A3 → ℂ) :
    mixedDot p a = mixedDot (fun i : Fin 3 => p (axes i))
      (fun i : Fin 3 => a (axes i)) := by
  unfold mixedDot
  exact sum_axis_reindex (fun j : A3 => (p j : ℂ) * a j)

private theorem amplitudeDot_axis_reindex (a b : A3 → ℂ) :
    amplitudeDot a b = amplitudeDot (fun i : Fin 3 => a (axes i))
      (fun i : Fin 3 => b (axes i)) := by
  unfold amplitudeDot
  exact sum_axis_reindex (fun j : A3 => a j * b j)

/-- The WHOLE six-order coefficient, not one selected term, is invariant
under simultaneous permutation of its six frequency/polarization inputs. -/
theorem lowNormalQuarter_sixOrder_axis_reindex
    (p q r : A3 → ℝ) (a b c : A3 → ℂ) :
    sixOrderTriadCoefficient p q r a b c =
      sixOrderTriadCoefficient
        (fun i : Fin 3 => p (axes i))
        (fun i : Fin 3 => q (axes i))
        (fun i : Fin 3 => r (axes i))
        (fun i : Fin 3 => a (axes i))
        (fun i : Fin 3 => b (axes i))
        (fun i : Fin 3 => c (axes i)) := by
  simp only [sixOrderTriadCoefficient, orderedTriadCoefficient,
    complexCoefficient, dot_axis_reindex,
    mixedDot_axis_reindex, amplitudeDot_axis_reindex]

private theorem lowNormalQuarterAxisHilbertToFin_middle (p r : V3) :
    lowNormalQuarterAxisHilbertToFin (-(p + r)) =
      middleFrequency (lowNormalQuarterAxisHilbertToFin p)
        (lowNormalQuarterAxisHilbertToFin r) := by
  funext i
  change (WithLp.ofLp (-(p + r))) (axes i) =
    -((WithLp.ofLp p) (axes i) + (WithLp.ofLp r) (axes i))
  simp only [WithLp.ofLp_neg, WithLp.ofLp_add, Pi.neg_apply, Pi.add_apply]

/-- At every canonical Hilbert frequency, the concrete real Schwartz field's
complexified Fourier polarization is EXACTLY the reindexed windowed packet. -/
theorem lowNormalQuarterAxisRealSchwartz_polarization_apply
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : V3) (j : A3) :
    PrimeTensor.Bridge.Euclidean.h3SchwartzTriadPolarization
      (fun k : A3 => PrimeTensor.Bridge.Euclidean.h3SchwartzComplexify
        (lowNormalQuarterAxisRealSchwartzComponent ρ hρ k))
      (WithLp.ofLp ξ) j =
    lowNormalQuarterWeightedFourier (lowNormalQuarterEvenWindow ρ hρ)
      (lowNormalQuarterAxisHilbertToFin ξ) (axes.symm j) := by
  change 𝓕 (PrimeTensor.Bridge.Euclidean.h3SchwartzComplexify
    (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)) ξ = _
  rw [lowNormalQuarterAxisRealSchwartz_fourier_component,
    lowNormalQuarterAxisFourierComponent_apply]
  have hc : (fun i : Fin 3 => ξ (axes i)) =
      lowNormalQuarterAxisHilbertToFin ξ := by
    funext i
    exact (lowNormalQuarterAxisHilbertToFin_apply ξ i).symm
  rw [hc]

/-- Pointwise exact matching of the complete, seven-derivative PHYSICAL
Fourier phase on both coordinate carriers. -/
theorem lowNormalQuarterCanonical_physicalPhaseKernel_eq
    (ρ : ℝ) (hρ : 0 < ρ) (z : P3) :
    (((2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
      PrimeTensor.Bridge.Euclidean.h3SchwartzTriadSixOrderKernel
        (fun j : A3 => PrimeTensor.Bridge.Euclidean.h3SchwartzComplexify
          (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)) z).re =
    lowNormalQuarterPhysicalPhaseKernel (lowNormalQuarterEvenWindow ρ hρ)
      (lowNormalQuarterAxisHilbertToFin z.1,
        lowNormalQuarterAxisHilbertToFin z.2) := by
  let F : A3 → SchwartzMap V3 ℂ := fun j =>
    PrimeTensor.Bridge.Euclidean.h3SchwartzComplexify
      (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)
  let w := lowNormalQuarterEvenWindow ρ hρ
  let p : A3 → ℝ := WithLp.ofLp z.1
  let q : A3 → ℝ := WithLp.ofLp (-(z.1 + z.2))
  let r : A3 → ℝ := WithLp.ofLp z.2
  have hA : (fun i : Fin 3 =>
      (PrimeTensor.Bridge.Euclidean.h3SchwartzTriadPolarization F p) (axes i)) =
      lowNormalQuarterWeightedFourier w
        (lowNormalQuarterAxisHilbertToFin z.1) := by
    funext i
    simpa only [Equiv.symm_apply_apply] using
      (lowNormalQuarterAxisRealSchwartz_polarization_apply ρ hρ z.1 (axes i))
  have hB : (fun i : Fin 3 =>
      (PrimeTensor.Bridge.Euclidean.h3SchwartzTriadPolarization F q) (axes i)) =
      lowNormalQuarterWeightedFourier w
        (lowNormalQuarterAxisHilbertToFin (-(z.1 + z.2))) := by
    funext i
    simpa only [Equiv.symm_apply_apply] using
      (lowNormalQuarterAxisRealSchwartz_polarization_apply ρ hρ
        (-(z.1 + z.2)) (axes i))
  have hC : (fun i : Fin 3 =>
      (PrimeTensor.Bridge.Euclidean.h3SchwartzTriadPolarization F r) (axes i)) =
      lowNormalQuarterWeightedFourier w
        (lowNormalQuarterAxisHilbertToFin z.2) := by
    funext i
    simpa only [Equiv.symm_apply_apply] using
      (lowNormalQuarterAxisRealSchwartz_polarization_apply ρ hρ z.2 (axes i))
  change (((2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
    sixOrderTriadCoefficient p q r
      (PrimeTensor.Bridge.Euclidean.h3SchwartzTriadPolarization F p)
      (PrimeTensor.Bridge.Euclidean.h3SchwartzTriadPolarization F q)
      (PrimeTensor.Bridge.Euclidean.h3SchwartzTriadPolarization F r)).re = _
  rw [lowNormalQuarter_sixOrder_axis_reindex]
  rw [hA, hB, hC]
  rw [lowNormalQuarterAxisHilbertToFin_middle]
  have hp : (fun i : Fin 3 => p (axes i)) =
      lowNormalQuarterAxisHilbertToFin z.1 := by
    funext i
    exact (lowNormalQuarterAxisHilbertToFin_apply z.1 i).symm
  have hq : (fun i : Fin 3 => q (axes i)) =
      middleFrequency (lowNormalQuarterAxisHilbertToFin z.1)
        (lowNormalQuarterAxisHilbertToFin z.2) := by
    funext i
    simpa only [lowNormalQuarterAxisHilbertToFin_apply] using
      congrFun (lowNormalQuarterAxisHilbertToFin_middle z.1 z.2) i
  have hr : (fun i : Fin 3 => r (axes i)) =
      lowNormalQuarterAxisHilbertToFin z.2 := by
    funext i
    exact (lowNormalQuarterAxisHilbertToFin_apply z.2 i).symm
  simp only [hp, hq, hr]
  rfl

/-- The physically phased full six-order Fourier integral is unchanged
when both independent frequency variables are carried onto the canonical
Axis/H3 Hilbert coordinates. -/
theorem lowNormalQuarterCanonical_physicalPhase_integral_eq
    (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ z : P3,
      (((2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
        PrimeTensor.Bridge.Euclidean.h3SchwartzTriadSixOrderKernel
          (fun j : A3 => PrimeTensor.Bridge.Euclidean.h3SchwartzComplexify
            (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)) z).re
          ∂(volume.prod volume)) =
      ∫ z : PFin,
        lowNormalQuarterPhysicalPhaseKernel (lowNormalQuarterEvenWindow ρ hρ) z
          ∂(volume.prod volume) := by
  let T := Prod.map lowNormalQuarterAxisHilbertToFin
    lowNormalQuarterAxisHilbertToFin
  have he : MeasurableEmbedding (T : P3 → PFin) :=
    (lowNormalQuarterAxisHilbertToFin.toHomeomorph.measurableEmbedding).prodMap
      (lowNormalQuarterAxisHilbertToFin.toHomeomorph.measurableEmbedding)
  calc
    _ = ∫ z : P3,
        lowNormalQuarterPhysicalPhaseKernel (lowNormalQuarterEvenWindow ρ hρ)
          (T z) ∂(volume.prod volume) := by
            apply integral_congr_ae
            filter_upwards with z
            exact lowNormalQuarterCanonical_physicalPhaseKernel_eq ρ hρ z
    _ = _ := lowNormalQuarterAxisHilbertToFin_prod_measurePreserving.integral_comp
      he (lowNormalQuarterPhysicalPhaseKernel (lowNormalQuarterEvenWindow ρ hρ))

/-- The explicit REAL canonical-axis Schwartz velocity realizes a strictly
NEGATIVE complete first-monomial Fourier phase integral. This is not a
claim of Navier--Stokes singularity. -/
theorem lowNormalQuarterCanonical_exists_negative_physicalPhase_integral :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      (∫ z : P3,
        (((2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
          PrimeTensor.Bridge.Euclidean.h3SchwartzTriadSixOrderKernel
            (fun j : A3 => PrimeTensor.Bridge.Euclidean.h3SchwartzComplexify
              (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)) z).re
            ∂(volume.prod volume)) < 0 := by
  obtain ⟨ρ, hρ, _, hNeg⟩ :=
    lowNormalQuarterEvenWindow_exists_negative_physicalPhase_integral
  refine ⟨ρ, hρ, ?_⟩
  rw [lowNormalQuarterCanonical_physicalPhase_integral_eq]
  exact hNeg

end
end PrimeTensor.FirstMonomialTriad
