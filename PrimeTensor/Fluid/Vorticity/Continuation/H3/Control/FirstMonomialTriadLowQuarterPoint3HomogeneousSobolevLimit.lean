import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3QuantitativeSplitSobolev
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Quantitative homogeneous whole-space Sobolev on the physical Point3 carrier

The preceding radius-dependent estimate gives, for every R > 0,

  ‖χ_R g‖₆ ≤ S (‖Dg‖₂ + ‖C/R‖ₑ ‖g‖₂).

Here the fixed cutoff constant C and Mathlib's compact-support Sobolev
constant S are independent of R. We take R = n + 1, use eventual *equality*
of the cutoff field with g at each physical point, and apply the existing
lower semicontinuity of eLpNorm under almost-everywhere convergence.

As n → ∞ the numerical cutoff error vanishes. Consequently

  ‖g‖₆ ≤ S ‖Dg‖₂.

This is the unconditional quantitative (not membership-only) whole-space
Sobolev inequality for C¹ fields in L² whose physical Frechet derivative
belongs to L². No incompressibility or Navier--Stokes evolution is assumed.

The subsequent 27-slot second-derivative Gagliardo--Nirenberg assembly is
separate; this theorem does not by itself assert a nonlinear critical-half
estimate or global Navier--Stokes regularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3CriticalHomogeneousSobolev
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The *homogeneous* whole-space `H¹ → L⁶` Sobolev inequality on the
actual three-dimensional physical carrier, retaining exactly Mathlib's
compact-support constant. The `L²` assumption permits cutoff approximation,
but its norm does not appear in the conclusion. -/
theorem wholeSpaceC1FDerivL2ToL6_homogeneous_quantitative
    {g : ScalarField3}
    (hC1 : SpatialC1 g)
    (hg2 : MemLp g (ENNReal.ofReal 2) volume)
    (hDg2 : MemLp (fun x : Point3 => fderiv ℝ g x)
      (ENNReal.ofReal 2) volume) :
    eLpNorm g (ENNReal.ofReal 6) volume ≤
      ((MeasureTheory.SNormLESNormFDerivOfEqConst
        ℝ (volume : Measure Point3) (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (fun x : Point3 => fderiv ℝ g x)
          (ENNReal.ofReal 2) volume := by
  obtain ⟨C, hCutoff⟩ :=
    exists_uniform_radius_cutoff_quantitative_split_L6 hC1 hg2 hDg2
  let radius : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hRadiusPos (n : ℕ) : 0 < radius n := by
    dsimp [radius]
    positivity
  let sobolevConst : ℝ≥0∞ :=
    ((MeasureTheory.SNormLESNormFDerivOfEqConst
      ℝ (volume : Measure Point3) (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞)
  let derivativeMass : ℝ≥0∞ :=
    eLpNorm (fun x : Point3 => fderiv ℝ g x)
      (ENNReal.ofReal 2) volume
  let baseMass : ℝ≥0∞ := eLpNorm g (ENNReal.ofReal 2) volume
  have hSobolevFinite : sobolevConst ≠ ∞ := by
    dsimp [sobolevConst]
    exact ENNReal.coe_ne_top
  have hBaseFinite : baseMass ≠ ∞ := by
    dsimp [baseMass]
    exact ne_of_lt hg2.eLpNorm_lt_top
  have hRadiusTop : Tendsto radius atTop atTop := by
    change Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop
    exact Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
  have hRadiusInverse :
      Tendsto (fun n : ℕ => (radius n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hRadiusTop
  have hCoefficient :
      Tendsto (fun n : ℕ => (C : ℝ) / radius n)
        atTop (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun n : ℕ => (C : ℝ) * (radius n)⁻¹)
        atTop (𝓝 ((C : ℝ) * 0)) :=
      tendsto_const_nhds.mul hRadiusInverse
    simpa [div_eq_mul_inv] using h
  have hCoefficientEnorm :
      Tendsto (fun n : ℕ => ‖(C : ℝ) / radius n‖ₑ)
        atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, enorm_zero] using
      (continuous_enorm.tendsto (0 : ℝ)).comp hCoefficient
  have hErrorTendsto :
      Tendsto (fun n : ℕ => ‖(C : ℝ) / radius n‖ₑ * baseMass)
        atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa using
      (ENNReal.Tendsto.mul_const hCoefficientEnorm (Or.inr hBaseFinite))
  have hSumTendsto :
      Tendsto (fun n : ℕ =>
        derivativeMass + ‖(C : ℝ) / radius n‖ₑ * baseMass)
        atTop (𝓝 derivativeMass) := by
    have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => derivativeMass) atTop (𝓝 derivativeMass)).add
        hErrorTendsto
    simpa using h
  have hBoundTendsto :
      Tendsto (fun n : ℕ =>
        sobolevConst * (derivativeMass +
          ‖(C : ℝ) / radius n‖ₑ * baseMass))
        atTop (𝓝 (sobolevConst * derivativeMass)) := by
    exact ENNReal.Tendsto.const_mul hSumTendsto (Or.inr hSobolevFinite)
  have hCutoffMeas (n : ℕ) :
      AEStronglyMeasurable
        (h3LandauCutoffField (radius n) (hRadiusPos n) g)
        volume :=
    (h3LandauCutoffField_spatialC1 (hRadiusPos n) hC1).continuous.aestronglyMeasurable
  have hPointwise :
      ∀ᵐ x : Point3 ∂volume,
        Tendsto (fun n : ℕ =>
          h3LandauCutoffField (radius n) (hRadiusPos n) g x)
          atTop (𝓝 (g x)) := by
    filter_upwards with x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    have hEventually :
        (fun n : ℕ =>
          h3LandauCutoffField (radius n) (hRadiusPos n) g x)
          =ᶠ[atTop] (fun _ : ℕ => g x) := by
      exact eventually_atTop.2 ⟨N, by
        intro n hn
        apply h3LandauCutoffField_eq_of_norm_le (hRadiusPos n)
        calc
          ‖x‖ ≤ (N : ℝ) := le_of_lt hN
          _ ≤ (n : ℝ) := by exact_mod_cast hn
          _ ≤ radius n := by
            dsimp [radius]
            linarith⟩
    exact tendsto_const_nhds.congr' hEventually.symm
  have hFatou :
      eLpNorm g (ENNReal.ofReal 6) volume ≤
        atTop.liminf (fun n : ℕ =>
          eLpNorm (h3LandauCutoffField (radius n) (hRadiusPos n) g)
            (ENNReal.ofReal 6) volume) :=
    MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm
      hCutoffMeas g hPointwise
  have hUpper (n : ℕ) :
      eLpNorm (h3LandauCutoffField (radius n) (hRadiusPos n) g)
          (ENNReal.ofReal 6) volume ≤
        sobolevConst * (derivativeMass +
          ‖(C : ℝ) / radius n‖ₑ * baseMass) :=
    hCutoff (hRadiusPos n)
  have hLiminf :
      atTop.liminf (fun n : ℕ =>
        eLpNorm (h3LandauCutoffField (radius n) (hRadiusPos n) g)
          (ENNReal.ofReal 6) volume) ≤
      atTop.liminf (fun n : ℕ =>
        sobolevConst * (derivativeMass +
          ‖(C : ℝ) / radius n‖ₑ * baseMass)) :=
    Filter.liminf_le_liminf (Filter.Eventually.of_forall hUpper)
  calc
    eLpNorm g (ENNReal.ofReal 6) volume ≤
      atTop.liminf (fun n : ℕ =>
        eLpNorm (h3LandauCutoffField (radius n) (hRadiusPos n) g)
          (ENNReal.ofReal 6) volume) := hFatou
    _ ≤ atTop.liminf (fun n : ℕ =>
        sobolevConst * (derivativeMass +
          ‖(C : ℝ) / radius n‖ₑ * baseMass)) := hLiminf
    _ = sobolevConst * derivativeMass := hBoundTendsto.liminf_eq
    _ = _ := rfl

end
end Euclidean
end Bridge
end PrimeTensor
