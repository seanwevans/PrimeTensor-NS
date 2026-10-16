import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3HomogeneousSobolevLimit
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzQuarticL2L6
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadPhysicalTransport
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Quantitative H¹ → L⁶ for every actual second-order Schwartz jet

The homogeneous Sobolev inequality has now been proved on `Point3`. Its
function-space input cannot simply be identified with the Euclidean carrier
`H3FourierPoint3`: the two spaces have distinct normed-space instances.

We use `SchwartzMap.compCLMOfContinuousLinearEquiv` for the *actual* coordinate
pullback. This constructs a Schwartz function on `Point3` and therefore proves,
rather than assumes, both `L²` conditions (field and Fréchet derivative).
The volume-preserving `WithLp.toLp 2` then identifies the *L⁶* norms.

Every ordered `j,i,k` second-order jet is covered with the SAME dimension-three
Sobolev constant. The comparison between the physical Fréchet derivative norm
and the 81-slot third-order energy is a separate, still-required inequality.
This module does not assert a Navier–Stokes regularity conclusion.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped SchwartzMap LineDeriv ENNReal NNReal

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSecondJetHomSob (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The genuine Schwartz pullback through the physical-to-Euclidean
coordinate equivalence, rather than an unbundled function composition. -/
noncomputable def lowNormalSchwartz_point3Pullback
    (g : SchwartzMap V3 ℝ) : SchwartzMap Point3 ℝ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : A3 => ℝ)).symm) g

/-- Pullback agrees with PrimeTensor's already-used physical scalar field. -/
theorem lowNormalSchwartz_point3Pullback_eq
    (g : SchwartzMap V3 ℝ) :
    (lowNormalSchwartz_point3Pullback g : Point3 → ℝ) =
      h3SchwartzPoint3Scalar g := by
  funext x
  change g ((WithLp.toLp 2 : Point3 → V3) x) =
    g (h3Point3ToFourierCLM x)
  rw [h3Point3ToFourierCLM_apply]

/-- The physical pullback of an arbitrary Euclidean Schwartz function
satisfies the homogeneous L⁶ bound, without extra regularity hypotheses. -/
theorem lowNormalSchwartz_point3Pullback_homogeneousSobolev
    (g : SchwartzMap V3 ℝ) :
    eLpNorm (h3SchwartzPoint3Scalar g)
        (ENNReal.ofReal 6) (volume : Measure Point3) ≤
      ((MeasureTheory.SNormLESNormFDerivOfEqConst
        ℝ (volume : Measure Point3) (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (fun x : Point3 =>
          fderiv ℝ (h3SchwartzPoint3Scalar g) x)
          (ENNReal.ofReal 2) (volume : Measure Point3) := by
  let G : SchwartzMap Point3 ℝ := lowNormalSchwartz_point3Pullback g
  have hC1 : SpatialC1 (G : Point3 → ℝ) := G.smooth 1
  have hG2 : MemLp (G : Point3 → ℝ)
      (ENNReal.ofReal 2) (volume : Measure Point3) :=
    G.memLp (ENNReal.ofReal 2) (volume : Measure Point3)
  have hDG2 : MemLp (fun x : Point3 =>
      fderiv ℝ (G : Point3 → ℝ) x)
      (ENNReal.ofReal 2) (volume : Measure Point3) := by
    -- Different elaboration paths can select different topology instances
    -- for continuous linear maps. Transfer integrability through the real
    -- pointwise norm, which has a fixed codomain topology.
    have hDerivativeMeas : AEStronglyMeasurable
        (fun x : Point3 => fderiv ℝ (G : Point3 → ℝ) x)
        (volume : Measure Point3) :=
      (hC1.continuous_fderiv (by norm_num)).aestronglyMeasurable
    have hSchwartzNorm : MemLp (fun x : Point3 =>
        ‖(SchwartzMap.fderivCLM ℝ Point3 ℝ G) x‖)
        (ENNReal.ofReal 2) (volume : Measure Point3) :=
      ((SchwartzMap.fderivCLM ℝ Point3 ℝ G).memLp
        (ENNReal.ofReal 2) (volume : Measure Point3)).norm
    have hDerivativeNorm : MemLp (fun x : Point3 =>
        ‖fderiv ℝ (G : Point3 → ℝ) x‖)
        (ENNReal.ofReal 2) (volume : Measure Point3) := by
      simpa only [SchwartzMap.fderivCLM_apply] using hSchwartzNorm
    exact (memLp_norm_iff hDerivativeMeas).mp hDerivativeNorm
  have h := wholeSpaceC1FDerivL2ToL6_homogeneous_quantitative
    hC1 hG2 hDG2
  simpa only [G, lowNormalSchwartz_point3Pullback_eq] using h

/-- All 27 actual ordered second-derivative Schwartz slots satisfy the
same quantitative homogeneous Sobolev inequality on the physical carrier. -/
theorem lowNormalRealSchwartz_secondJet_physicalHomogeneousSobolev
    (f : A3 → SchwartzMap V3 ℝ) (j i k : A3) :
    eLpNorm
        (h3SchwartzPoint3Scalar
          (∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection k} (f j))))
        (ENNReal.ofReal 6) (volume : Measure Point3) ≤
      ((MeasureTheory.SNormLESNormFDerivOfEqConst
        ℝ (volume : Measure Point3) (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (fun x : Point3 =>
          fderiv ℝ
            (h3SchwartzPoint3Scalar
              (∂_{h3FourierAxisDirection i}
                (∂_{h3FourierAxisDirection k} (f j)))) x)
          (ENNReal.ofReal 2) (volume : Measure Point3) := by
  exact lowNormalSchwartz_point3Pullback_homogeneousSobolev
    (∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k} (f j)))

/-- The actual Euclidean Schwartz `L⁶` norm is identical to the physical
pullback `L⁶` norm: this step uses volume preservation, not a tacit carrier
identification. -/
theorem lowNormalSchwartz_point3Pullback_eLpNorm_eq
    (g : SchwartzMap V3 ℝ) (p : ℝ≥0∞) :
    eLpNorm (h3SchwartzPoint3Scalar g) p (volume : Measure Point3) =
      eLpNorm (g : V3 → ℝ) p (volume : Measure V3) := by
  have h := eLpNorm_comp_measurePreserving
    (μ := (volume : Measure Point3))
    (g := (g : V3 → ℝ))
    (p := p)
    g.continuous.aestronglyMeasurable
    (PiLp.volume_preserving_toLp A3)
  change eLpNorm
      ((g : V3 → ℝ) ∘ (WithLp.toLp 2 : Point3 → V3))
      p (volume : Measure Point3) =
        eLpNorm (g : V3 → ℝ) p (volume : Measure V3)
  exact h

/-- Pointwise-in-slot 27-fold homogeneous Sobolev with a genuine Euclidean
L⁶ left side and physical third-derivative Frechet norm on the right. -/
theorem lowNormalRealSchwartz_secondJet_euclideanL6_le_physicalDerivativeL2
    (f : A3 → SchwartzMap V3 ℝ) (j i k : A3) :
    eLpNorm
        (∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} (f j)) : SchwartzMap V3 ℝ)
        (ENNReal.ofReal 6) (volume : Measure V3) ≤
      ((MeasureTheory.SNormLESNormFDerivOfEqConst
        ℝ (volume : Measure Point3) (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (fun x : Point3 =>
          fderiv ℝ
            (h3SchwartzPoint3Scalar
              (∂_{h3FourierAxisDirection i}
                (∂_{h3FourierAxisDirection k} (f j)))) x)
          (ENNReal.ofReal 2) (volume : Measure Point3) := by
  rw [← lowNormalSchwartz_point3Pullback_eLpNorm_eq
    (∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k} (f j))) (ENNReal.ofReal 6)]
  exact lowNormalRealSchwartz_secondJet_physicalHomogeneousSobolev f j i k

end
end PrimeTensor.FirstMonomialTriad
