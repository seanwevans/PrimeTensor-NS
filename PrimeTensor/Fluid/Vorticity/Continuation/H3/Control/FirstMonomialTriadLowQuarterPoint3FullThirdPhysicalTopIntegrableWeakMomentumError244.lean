import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopQuantitativeSolenoidalResidual244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopPointwiseSolenoidalMomentum244
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Physical projected FTC from time-integrable solenoidal derivative errors

The quantitative compact-solenoidal density theorem controls the true
physical Hilbert FTC defect by its test-dual scalar residual. This module
connects that scalar residual to an *integrable time-dependent* error in the
differentiated weak momentum equation.

For a compact solenoidal test phi we assume a scalar error e_phi with

  d/dt <phi,U(t)> = <phi,R(t)> + e_phi(t),
  |e_phi(t)| <= g(t) ||phi||_L2.

Here g can vary in time; no pointwise-in-space bound on the old temporal
derivative or L2 pressure gradient is involved. The actual U and R are known
strongly continuous on strict windows. Scalar FTC and interval-integral
norm control imply

  ||D(a,r)||_L2 <= integral_a^r g(t) dt.

The differentiated weak momentum assumption is NOT derived here from the
separately continuous classical preterminal PDE. In particular the module
does not establish unconditional Navier--Stokes continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A common time-varying nonnegative majorant for scalar differentiated
solenoidal momentum errors. The individual scalar error is continuous on
the strict compact window; it is not required to be an L2 spatial vector. -/
def h3PathIntegrableSolenoidalWeakDerivativeErrorOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    ∃ e : ℝ → ℝ,
      ContinuousOn e (Set.Icc a b) ∧
      (∀ s : ℝ, s ∈ Set.Ioo a b →
        HasDerivAt
          (fun r : ℝ =>
            inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
              (h3AuditInitialOldPhysicalHilbertTotal hH3 r))
          (inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PathActualProjectedMomentumSource244 hH3 s) + e s) s) ∧
      (∀ s : ℝ, s ∈ Set.Icc a b →
        |e s| ≤ g s * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖)

/-- Scalar FTC converts an integrable time-profile of differentiated
solenoidal momentum error into an integrated test-dual FTC defect bound.
There is no assumption of temporal uniform boundedness for the classical
pointwise spatial PDE terms. -/
theorem h3Path_projectedFTCDefect_pairing_norm_le_integratedWeakError244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc a b))
    (hWeak : h3PathIntegrableSolenoidalWeakDerivativeErrorOn244
      hH3 a b g)
    (r : ℝ) (hr : r ∈ Set.Icc a b)
    (φ : H3WeakTestVector) (hφ : H3WeakTestVectorDivergenceFree φ) :
    ‖inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PathActualProjectedMomentumFTCDefect244 hH3 a r)‖ ≤
      (∫ s in a..r, g s) * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖ := by
  let U : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let R : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ
  obtain ⟨e, heCont, heDeriv, heBound⟩ := hWeak φ hφ
  have hSub : Set.Icc a r ⊆ Set.Icc a b := by
    intro s hs
    exact ⟨hs.1, hs.2.trans hr.2⟩
  have hStrict : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hb⟩
  have hUCont : ContinuousOn U (Set.Icc a r) :=
    ((h3Audit_initialOldPhysicalHilbert_continuousOn hH3).mono hStrict).mono hSub
  have hRCont : ContinuousOn R (Set.Icc a r) :=
    (h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 ha hab hb).mono hSub
  have hUScalar : ContinuousOn
      (fun s : ℝ => inner ℝ ψ (U s)) (Set.Icc a r) := by
    change ContinuousOn (fun s : ℝ => ((innerSL ℝ) ψ) (U s)) (Set.Icc a r)
    exact ((innerSL ℝ) ψ).continuous.comp_continuousOn hUCont
  have hRScalar : ContinuousOn
      (fun s : ℝ => inner ℝ ψ (R s)) (Set.Icc a r) := by
    change ContinuousOn (fun s : ℝ => ((innerSL ℝ) ψ) (R s)) (Set.Icc a r)
    exact ((innerSL ℝ) ψ).continuous.comp_continuousOn hRCont
  have hRInt : IntervalIntegrable
      (fun s : ℝ => inner ℝ ψ (R s)) volume a r :=
    hRScalar.intervalIntegrable_of_Icc hr.1
  have heInt : IntervalIntegrable e volume a r :=
    (heCont.mono hSub).intervalIntegrable_of_Icc hr.1
  have hFTC :
      (∫ s in a..r, inner ℝ ψ (R s) + e s) =
        inner ℝ ψ (U r) - inner ℝ ψ (U a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hr.1 hUScalar
    · intro s hs
      have hsAB : s ∈ Set.Ioo a b :=
        ⟨hs.1, lt_of_lt_of_le hs.2 hr.2⟩
      exact heDeriv s hsAB
    · exact hRInt.add heInt
  rw [intervalIntegral.integral_add hRInt heInt] at hFTC
  have hRVectorInt : IntervalIntegrable R volume a r :=
    hRCont.intervalIntegrable_of_Icc hr.1
  have hComm :
      inner ℝ ψ (∫ s in a..r, R s) =
        ∫ s in a..r, inner ℝ ψ (R s) := by
    change ((innerSL ℝ) ψ) (∫ s in a..r, R s) =
      ∫ s in a..r, ((innerSL ℝ) ψ) (R s)
    exact (((innerSL ℝ) ψ).intervalIntegral_comp_comm hRVectorInt).symm
  have hResidual :
      inner ℝ ψ (h3PathActualProjectedMomentumFTCDefect244 hH3 a r) =
        ∫ s in a..r, e s := by
    change inner ℝ ψ (U r - U a - ∫ s in a..r, R s) = _
    rw [inner_sub_right, inner_sub_right, hComm]
    linarith only [hFTC]
  have hMajorInt : IntervalIntegrable
      (fun s : ℝ => g s * ‖ψ‖) volume a r :=
    (((hg.mono hSub).mul continuousOn_const).intervalIntegrable_of_Icc hr.1)
  have hMajorAE :
      ∀ᵐ s ∂(volume : Measure ℝ),
        s ∈ Set.Ioc a r → ‖e s‖ ≤ g s * ‖ψ‖ := by
    filter_upwards with s
    intro hs
    have hsAB : s ∈ Set.Icc a b :=
      ⟨hs.1.le, hs.2.trans hr.2⟩
    simpa only [Real.norm_eq_abs] using heBound s hsAB
  have hIntBound :
      ‖∫ s in a..r, e s‖ ≤
        ∫ s in a..r, g s * ‖ψ‖ :=
    intervalIntegral.norm_integral_le_of_norm_le hr.1 hMajorAE hMajorInt
  rw [hResidual]
  calc
    ‖∫ s in a..r, e s‖ ≤
        ∫ s in a..r, g s * ‖ψ‖ := hIntBound
    _ = (∫ s in a..r, g s) * ‖ψ‖ := by
      rw [intervalIntegral.integral_mul_const]

/-- Sharp physical Hilbert defect control by the integrated scalar derivative
error profile. The decisive analytic input is an L1-in-time quantity, not an
L-infinity error or a pointwise spatial majorant. -/
theorem h3Path_projectedFTCDefect_norm_le_integratedWeakError244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc a b))
    (hg0 : ∀ s : ℝ, s ∈ Set.Icc a b → 0 ≤ g s)
    (hWeak : h3PathIntegrableSolenoidalWeakDerivativeErrorOn244
      hH3 a b g) :
    ∀ r : ℝ, r ∈ Set.Icc a b →
      ‖h3PathActualProjectedMomentumFTCDefect244 hH3 a r‖ ≤
        ∫ s in a..r, g s := by
  intro r hr
  by_cases har : a < r
  · have hNonneg : 0 ≤ ∫ s in a..r, g s := by
      apply intervalIntegral.integral_nonneg har.le
      intro s hs
      exact hg0 s ⟨hs.1, hs.2.trans hr.2⟩
    apply h3PhysicalL2_norm_le_of_lerayFixed_solenoidalTestBound244
      (h3PathActualProjectedMomentumFTCDefect244 hH3 a r)
      (h3Path_projectedFTCDefect_lerayFixed_onStrict244
        hH3 ha har (lt_of_le_of_lt hr.2 hb)) hNonneg
    intro φ hφ
    exact h3Path_projectedFTCDefect_pairing_norm_le_integratedWeakError244
      hH3 ha hab hb g hg hWeak r hr φ hφ
  · have hra : r = a := le_antisymm (le_of_not_gt har) hr.1
    subst r
    simp [h3PathActualProjectedMomentumFTCDefect244]

/-- A controlled time-dependent profile with small cumulative mass yields
uniform physical L2 FTC-defect control. The scalar derivative error may spike
in time, provided its integral is small. -/
theorem h3Path_projectedFTCDefect_uniform_norm_le_of_integrableWeakError244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b η : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc a b))
    (hg0 : ∀ s : ℝ, s ∈ Set.Icc a b → 0 ≤ g s)
    (hWeak : h3PathIntegrableSolenoidalWeakDerivativeErrorOn244
      hH3 a b g)
    (hMass : ∀ r : ℝ, r ∈ Set.Icc a b → (∫ s in a..r, g s) ≤ η) :
    ∀ r : ℝ, r ∈ Set.Icc a b →
      ‖h3PathActualProjectedMomentumFTCDefect244 hH3 a r‖ ≤ η := by
  intro r hr
  exact (h3Path_projectedFTCDefect_norm_le_integratedWeakError244
    hH3 ha hab hb g hg hg0 hWeak r hr).trans (hMass r hr)

/-- If arbitrarily small cumulative time profiles control the differentiated
weak momentum error, the physical Hilbert FTC defect vanishes on every prefix.
Only the scalar error profiles are required; no vector-valued residual needs
to exist as a physical L2 state. -/
theorem h3Path_solenoidalWeakFTC_of_vanishingIntegrableWeakError244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hSmall : ∀ η : ℝ, 0 < η →
      ∃ g : ℝ → ℝ,
        ContinuousOn g (Set.Icc a b) ∧
        (∀ s : ℝ, s ∈ Set.Icc a b → 0 ≤ g s) ∧
        h3PathIntegrableSolenoidalWeakDerivativeErrorOn244 hH3 a b g ∧
        (∀ r : ℝ, r ∈ Set.Icc a b →
          (∫ s in a..r, g s) ≤ η)) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  apply (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha hab hb).1
  intro r hr
  let D : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumFTCDefect244 hH3 a r
  by_contra hD
  have hPos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hHalf : 0 < ‖D‖ / 2 := by positivity
  obtain ⟨g, hg, hg0, hWeak, hMass⟩ := hSmall (‖D‖ / 2) hHalf
  have hBound :=
    h3Path_projectedFTCDefect_uniform_norm_le_of_integrableWeakError244
      hH3 ha hab hb g hg hg0 hWeak hMass r hr
  change ‖D‖ ≤ ‖D‖ / 2 at hBound
  linarith

end
end PrimeTensor.FirstMonomialTriad
