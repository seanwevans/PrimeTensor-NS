import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdRadialDefect
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdProjectedHermitianGerm244
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Integrated radial-defect gain for the true frequency-transverse H³ symbol

This module uses the actual six-permutation gradient-plus-interpolation symbol,
the genuine momentum plane q = -p-r, and three frequency-varying solenoidal
polynomial Leray germs. The phase-correct Hermitian kernel is EXACTLY twice
that six-symbol. Its local absolute integral inherits the radial defect factor
without applying termwise triangle inequalities before symmetrization.

This is a genuine six-dimensional Fourier-pair integral for the physical
projected kernel. It is not yet an equality with the unrestricted trilinear
Fourier integral of an arbitrary Schwartz velocity; that separate bridge is
still needed. No terminal continuation or new a priori estimate is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Metric Set
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 1800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Pair244 := (A3 → ℝ) × (A3 → ℝ)

noncomputable local instance axisFintypeProjectedRadialIntegral (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance frequencyMeasureProjectedRadialIntegral :
    MeasureSpace (A3 → ℝ) :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The three explicit absolute polarization multipliers left by exact
six-order symmetrization, with the ORIGINAL moving transverse germs. -/
noncomputable def thirdFullProjectedRadialAmplitude244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) : ℝ :=
  let p := z.1
  let q := thirdFullMiddleFrequency244 z
  let r := z.2
  let U := thirdFullFixedCenterTransverseGerm244 p₀ p A
  let V := thirdFullFixedCenterTransverseGerm244 q₀ q B
  let W := thirdFullFixedCenterTransverseGerm244 r₀ r C
  let a := thirdTriadAxisDot244 p q
  let b := thirdTriadAxisDot244 p r
  let c := thirdTriadAxisDot244 q r
  |thirdTriadAxisDot244 U W * thirdTriadAxisDot244 V r *
      thirdFullRadialDefectMultiplier244 a c b| +
  |thirdTriadAxisDot244 U V * thirdTriadAxisDot244 W q *
      thirdFullRadialDefectMultiplier244 b c a| +
  |thirdTriadAxisDot244 V W * thirdTriadAxisDot244 U r *
      thirdFullRadialDefectMultiplier244 a b c|

/-- A physical frequency-momentum triple in the projected kernel is exactly
solenoidal at every frequency, including zero, because all three polarizations
are the previously constructed polynomial transverse germs. -/
theorem thirdFullProjectedHermitian_nearEqualRadius_bound244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) (ρ : ℝ)
    (hRP : |thirdTriadAxisDot244 z.2 z.2 -
      thirdTriadAxisDot244 z.1 z.1| ≤ ρ)
    (hQP : |thirdTriadAxisDot244
        (thirdFullMiddleFrequency244 z) (thirdFullMiddleFrequency244 z) -
      thirdTriadAxisDot244 z.1 z.1| ≤ ρ)
    (hRQ : |thirdTriadAxisDot244 z.2 z.2 -
      thirdTriadAxisDot244
        (thirdFullMiddleFrequency244 z) (thirdFullMiddleFrequency244 z)| ≤ ρ) :
    |thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z| ≤
      2 * ρ * thirdFullProjectedRadialAmplitude244 p₀ q₀ r₀ A B C z := by
  let q := thirdFullMiddleFrequency244 z
  let U := thirdFullFixedCenterTransverseGerm244 p₀ z.1 A
  let V := thirdFullFixedCenterTransverseGerm244 q₀ q B
  let W := thirdFullFixedCenterTransverseGerm244 r₀ z.2 C
  have hm : ∀ i : A3, z.1 i + q i + z.2 i = 0 := by
    intro i
    dsimp [q, thirdFullMiddleFrequency244]
    ring
  have ht := thirdFullProjectedHermitianKernel_transverse244
    p₀ q₀ r₀ A B C z
  have hU : thirdTriadAxisDot244 U z.1 = 0 := by
    rw [thirdFullAxisDot_comm244]
    exact ht.1
  have hV : thirdTriadAxisDot244 V q = 0 := by
    rw [thirdFullAxisDot_comm244]
    exact ht.2.1
  have hW : thirdTriadAxisDot244 W z.2 = 0 := by
    rw [thirdFullAxisDot_comm244]
    exact ht.2.2
  have hSix := thirdFullPhysicalSix_nearEqualRadius_bound244
    z.1 q z.2 U V W ρ hm hU hV hW hRP hQP hRQ
  have hKernel : thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z =
      2 * thirdFullPhysicalSixSymbol244 z.1 q z.2 U V W := by
    unfold thirdFullProjectedHermitianKernel244
    rw [thirdFullHermitianMomentumKernel_eq244]
  have hTwo : (0 : ℝ) ≤ 2 := by norm_num
  calc
    |thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z| =
        2 * |thirdFullPhysicalSixSymbol244 z.1 q z.2 U V W| := by
          rw [hKernel, abs_mul, abs_of_nonneg hTwo]
    _ ≤ 2 * (ρ * (
        |thirdTriadAxisDot244 U W * thirdTriadAxisDot244 V z.2 *
          thirdFullRadialDefectMultiplier244
            (thirdTriadAxisDot244 z.1 q)
            (thirdTriadAxisDot244 q z.2)
            (thirdTriadAxisDot244 z.1 z.2)| +
        |thirdTriadAxisDot244 U V * thirdTriadAxisDot244 W q *
          thirdFullRadialDefectMultiplier244
            (thirdTriadAxisDot244 z.1 z.2)
            (thirdTriadAxisDot244 q z.2)
            (thirdTriadAxisDot244 z.1 q)| +
        |thirdTriadAxisDot244 V W * thirdTriadAxisDot244 U z.2 *
          thirdFullRadialDefectMultiplier244
            (thirdTriadAxisDot244 z.1 q)
            (thirdTriadAxisDot244 z.1 z.2)
            (thirdTriadAxisDot244 q z.2)|)) :=
          mul_le_mul_of_nonneg_left hSix hTwo
    _ = 2 * ρ * thirdFullProjectedRadialAmplitude244 p₀ q₀ r₀ A B C z := by
      dsimp only [thirdFullProjectedRadialAmplitude244, q, U, V, W]
      ring

/-- The radial-amplitude multiplier is continuous on the actual six-dimensional
momentum plane. In particular its compact-region integral is finite, rather
than being posited as a new analytic premise. -/
theorem thirdFullProjectedRadialAmplitude_continuous244
    (p₀ q₀ r₀ A B C : A3 → ℝ) :
    Continuous (thirdFullProjectedRadialAmplitude244 p₀ q₀ r₀ A B C) := by
  let p : Pair244 → A3 → ℝ := fun z => z.1
  let q : Pair244 → A3 → ℝ := thirdFullMiddleFrequency244
  let r : Pair244 → A3 → ℝ := fun z => z.2
  let U : Pair244 → A3 → ℝ := fun z =>
    thirdFullFixedCenterTransverseGerm244 p₀ (p z) A
  let V : Pair244 → A3 → ℝ := fun z =>
    thirdFullFixedCenterTransverseGerm244 q₀ (q z) B
  let W : Pair244 → A3 → ℝ := fun z =>
    thirdFullFixedCenterTransverseGerm244 r₀ (r z) C
  have hp : Continuous p := continuous_fst
  have hq : Continuous q := thirdFullMiddleFrequency_continuous244
  have hr : Continuous r := continuous_snd
  have hU : Continuous U :=
    (thirdFullFixedCenterTransverseGerm_continuous244 p₀ A).comp hp
  have hV : Continuous V :=
    (thirdFullFixedCenterTransverseGerm_continuous244 q₀ B).comp hq
  have hW : Continuous W :=
    (thirdFullFixedCenterTransverseGerm_continuous244 r₀ C).comp hr
  let a : Pair244 → ℝ := fun z => thirdTriadAxisDot244 (p z) (q z)
  let b : Pair244 → ℝ := fun z => thirdTriadAxisDot244 (p z) (r z)
  let c : Pair244 → ℝ := fun z => thirdTriadAxisDot244 (q z) (r z)
  have ha : Continuous a := thirdTriadAxisDot_continuous_of_continuous244 p q hp hq
  have hb : Continuous b := thirdTriadAxisDot_continuous_of_continuous244 p r hp hr
  have hc : Continuous c := thirdTriadAxisDot_continuous_of_continuous244 q r hq hr
  let α : Pair244 → ℝ := fun z => thirdTriadAxisDot244 (U z) (W z)
  let β : Pair244 → ℝ := fun z => thirdTriadAxisDot244 (V z) (r z)
  let γ : Pair244 → ℝ := fun z => thirdTriadAxisDot244 (U z) (V z)
  let δ : Pair244 → ℝ := fun z => thirdTriadAxisDot244 (W z) (q z)
  let ε : Pair244 → ℝ := fun z => thirdTriadAxisDot244 (V z) (W z)
  let ζ : Pair244 → ℝ := fun z => thirdTriadAxisDot244 (U z) (r z)
  have hα : Continuous α := thirdTriadAxisDot_continuous_of_continuous244 U W hU hW
  have hβ : Continuous β := thirdTriadAxisDot_continuous_of_continuous244 V r hV hr
  have hγ : Continuous γ := thirdTriadAxisDot_continuous_of_continuous244 U V hU hV
  have hδ : Continuous δ := thirdTriadAxisDot_continuous_of_continuous244 W q hW hq
  have hε : Continuous ε := thirdTriadAxisDot_continuous_of_continuous244 V W hV hW
  have hζ : Continuous ζ := thirdTriadAxisDot_continuous_of_continuous244 U r hU hr
  have hG1 : Continuous (fun z => thirdFullRadialDefectMultiplier244 (a z) (c z) (b z)) := by
    unfold thirdFullRadialDefectMultiplier244
    fun_prop
  have hG2 : Continuous (fun z => thirdFullRadialDefectMultiplier244 (b z) (c z) (a z)) := by
    unfold thirdFullRadialDefectMultiplier244
    fun_prop
  have hG3 : Continuous (fun z => thirdFullRadialDefectMultiplier244 (a z) (b z) (c z)) := by
    unfold thirdFullRadialDefectMultiplier244
    fun_prop
  change Continuous (fun z : Pair244 =>
    |α z * β z * thirdFullRadialDefectMultiplier244 (a z) (c z) (b z)| +
    |γ z * δ z * thirdFullRadialDefectMultiplier244 (b z) (c z) (a z)| +
    |ε z * ζ z * thirdFullRadialDefectMultiplier244 (a z) (b z) (c z)|)
  exact ((((hα.mul hβ).mul hG1).abs.add
    ((hγ.mul hδ).mul hG2).abs).add
    ((hε.mul hζ).mul hG3).abs)

/-- The local SIX-DIMENSIONAL physical Fourier integral inherits the factor
measuring squared-radius imbalance. This uses a compact set so all integrals
are automatic: the multiplier is a continuous polynomial of the actual
momentum and the actual moving Leray germs. -/
theorem thirdFullProjectedHermitian_compact_radialIntegral_bound244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z₀ : Pair244) (σ ρ : ℝ)
    (hRP : ∀ z ∈ Metric.closedBall z₀ σ,
      |thirdTriadAxisDot244 z.2 z.2 - thirdTriadAxisDot244 z.1 z.1| ≤ ρ)
    (hQP : ∀ z ∈ Metric.closedBall z₀ σ,
      |thirdTriadAxisDot244
        (thirdFullMiddleFrequency244 z) (thirdFullMiddleFrequency244 z) -
        thirdTriadAxisDot244 z.1 z.1| ≤ ρ)
    (hRQ : ∀ z ∈ Metric.closedBall z₀ σ,
      |thirdTriadAxisDot244 z.2 z.2 - thirdTriadAxisDot244
        (thirdFullMiddleFrequency244 z) (thirdFullMiddleFrequency244 z)| ≤ ρ) :
    |∫ z in Metric.closedBall z₀ σ,
      thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z
        ∂(volume.prod volume)| ≤
      2 * ρ * (∫ z in Metric.closedBall z₀ σ,
        thirdFullProjectedRadialAmplitude244 p₀ q₀ r₀ A B C z
          ∂(volume.prod volume)) := by
  let S : Set Pair244 := Metric.closedBall z₀ σ
  let K : Pair244 → ℝ := thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C
  let H : Pair244 → ℝ := thirdFullProjectedRadialAmplitude244 p₀ q₀ r₀ A B C
  have hCompact : IsCompact S := isCompact_closedBall _ _
  have hMeas : MeasurableSet S := measurableSet_closedBall
  have hK : IntegrableOn K S (volume.prod volume) :=
    (thirdFullProjectedHermitianKernel_continuous244 p₀ q₀ r₀ A B C).continuousOn.integrableOn_compact hCompact
  have hH : IntegrableOn H S (volume.prod volume) :=
    (thirdFullProjectedRadialAmplitude_continuous244 p₀ q₀ r₀ A B C).continuousOn.integrableOn_compact hCompact
  have hAbs : IntegrableOn (fun z => |K z|) S (volume.prod volume) := hK.abs
  have hScaled : IntegrableOn (fun z => 2 * ρ * H z) S (volume.prod volume) :=
    hH.const_mul (2 * ρ)
  have hAlmost : ∀ᵐ z ∂(volume.prod volume).restrict S,
      |K z| ≤ 2 * ρ * H z := by
    filter_upwards [ae_restrict_mem hMeas] with z hz
    exact thirdFullProjectedHermitian_nearEqualRadius_bound244
      p₀ q₀ r₀ A B C z ρ (hRP z hz) (hQP z hz) (hRQ z hz)
  calc
    |∫ z in S, K z ∂(volume.prod volume)| ≤
        ∫ z in S, |K z| ∂(volume.prod volume) :=
          abs_integral_le_integral_abs
    _ ≤ ∫ z in S, 2 * ρ * H z ∂(volume.prod volume) :=
      integral_mono_ae hAbs hScaled hAlmost
    _ = 2 * ρ * (∫ z in S, H z ∂(volume.prod volume)) := by
      rw [integral_const_mul]

end
end PrimeTensor.FirstMonomialTriad
