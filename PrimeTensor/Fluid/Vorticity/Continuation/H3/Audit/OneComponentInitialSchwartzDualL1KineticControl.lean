import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialScalarWeakFTCControl
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Schwartz.Dense

/-!
# Initial physical kinetic control from Schwartz-test weak evolution

Compact/smooth spatial probes are natural for a distributional Navier--Stokes
initial-value formulation. Mere testwise boundedness is NOT enough to bound
the full physical `L²` norm: kinetic mass can escape the probing topology.

Here a single *uniform dual* `L¹` budget closes that missing estimate.
For every three-component physical Schwartz test `Φ`, allow a different
scalar temporal source `gΦ`, but demand a common constant `M` such that

  ∫₀ᵇ |gΦ(r)| dr ≤ M ‖Φ‖_(physical L²).

The exact positive-time scalar increment identity then implies

  |⟪old(t)-old(q), Φ⟫| ≤ 2 M ‖Φ‖_(physical L²),

where `q = b/2`. The already-proved physical Schwartz density extends this
operator-norm bound to ALL physical L² tests. Self-testing then gives

  ‖old(t)‖_(physical L²) ≤ ‖old(q)‖_(physical L²) + 2 M.

This is a genuinely quantitative uniform-dual requirement, not the previous
scalar weak FTC for every physical L² probe. It is not proved from the PDE
here. The vanishing relative-energy residual remains a separate hypothesis,
as does the terminal strong-H³ actual-vorticity endpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- A Bochner integrable real scalar has an absolutely dominated forward
primitive, uniformly over all subintervals starting at zero. -/
theorem h3Audit_initialScalarPrimitive_norm_le_totalAbsMass
    (g : ℝ → ℝ) (b t : ℝ)
    (hb : 0 ≤ b) (ht : t ∈ Set.Icc (0 : ℝ) b)
    (hG : IntervalIntegrable g volume 0 b) :
    ‖∫ r in (0 : ℝ)..t, g r‖ ≤
      ∫ r in (0 : ℝ)..b, |g r| := by
  have hAbs : IntervalIntegrable (fun r : ℝ => |g r|) volume 0 b := by
    simpa only [Real.norm_eq_abs] using hG.norm
  have hAbsT : IntervalIntegrable (fun r : ℝ => |g r|) volume 0 t := by
    apply hAbs.mono_set
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) t := by
      simpa only [Set.uIcc_of_le ht.1] using hx
    have hxb : x ∈ Set.Icc (0 : ℝ) b :=
      ⟨hx'.1, hx'.2.trans ht.2⟩
    simpa only [Set.uIcc_of_le hb] using hxb
  have hPointwise :
      ∀ᵐ r : ℝ ∂volume,
        r ∈ Set.Ioc (0 : ℝ) t → ‖g r‖ ≤ |g r| := by
    filter_upwards [] with r
    intro _
    simp only [Real.norm_eq_abs, le_refl]
  have hNorm :
      ‖∫ r in (0 : ℝ)..t, g r‖ ≤
        ∫ r in (0 : ℝ)..t, |g r| :=
    intervalIntegral.norm_integral_le_of_norm_le
      ht.1 hPointwise hAbsT
  exact hNorm.trans
    (h3Audit_initialResidualPrimitive_le_totalAbsMass g b t ht hAbs)

/-- A common `L¹` dual-norm budget on Schwartz-test scalar derivatives.
Each individual Schwartz test may have its own scalar source and no single
Hilbert-valued time derivative is stipulated. -/
def H3AuditInitialSchwartzDualL1IncrementOn
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b M : ℝ) : Prop :=
  ∀ Φ : H3PhysicalRealFinVectorSchwartz,
    ∃ g : ℝ → ℝ,
      IntervalIntegrable g volume 0 b ∧
      (∫ r in (0 : ℝ)..b, |g r|) ≤
        M * ‖h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ‖ ∧
      ∀ (s t : ℝ),
        s ∈ Set.Ioo (0 : ℝ) b →
        t ∈ Set.Ioo (0 : ℝ) b →
          ((innerSL ℝ) (F t))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) -
            ((innerSL ℝ) (F s))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) =
          ∫ r in s..t, g r

/-- The common scalar-source budget controls every Schwartz pairing
increment from the chosen strictly positive anchor. -/
theorem h3Audit_initialSchwartzDualL1_pairingIncrement_le
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b M : ℝ) (hb : 0 < b)
    (hFTC : H3AuditInitialSchwartzDualL1IncrementOn F b M)
    (q t : ℝ)
    (hq : q ∈ Set.Ioo (0 : ℝ) b)
    (ht : t ∈ Set.Ioo (0 : ℝ) b)
    (Φ : H3PhysicalRealFinVectorSchwartz) :
    ‖((innerSL ℝ) (F t))
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) -
      ((innerSL ℝ) (F q))
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)‖ ≤
      (2 * M) * ‖h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ‖ := by
  obtain ⟨g, hG, hMass, hInc⟩ := hFTC Φ
  have hGlocal (z : ℝ) (hz : z ∈ Set.Ioo (0 : ℝ) b) :
      IntervalIntegrable g volume 0 z := by
    apply hG.mono_set
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) z := by
      simpa only [Set.uIcc_of_le hz.1.le] using hx
    have hxb : x ∈ Set.Icc (0 : ℝ) b :=
      ⟨hx'.1, hx'.2.trans hz.2.le⟩
    simpa only [Set.uIcc_of_le hb.le] using hxb
  have hIntegral :
      (∫ r in q..t, g r) =
        (∫ r in (0 : ℝ)..t, g r) -
          (∫ r in (0 : ℝ)..q, g r) :=
    (intervalIntegral.integral_interval_sub_left
      (hGlocal t ht) (hGlocal q hq)).symm
  have hEq :
      ((innerSL ℝ) (F t))
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) -
        ((innerSL ℝ) (F q))
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) =
      (∫ r in (0 : ℝ)..t, g r) -
        (∫ r in (0 : ℝ)..q, g r) :=
    (hInc q t hq ht).trans hIntegral
  have hBoundT :
      ‖∫ r in (0 : ℝ)..t, g r‖ ≤
        M * ‖h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ‖ :=
    (h3Audit_initialScalarPrimitive_norm_le_totalAbsMass
      g b t hb.le ⟨ht.1.le, ht.2.le⟩ hG).trans hMass
  have hBoundQ :
      ‖∫ r in (0 : ℝ)..q, g r‖ ≤
        M * ‖h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ‖ :=
    (h3Audit_initialScalarPrimitive_norm_le_totalAbsMass
      g b q hb.le ⟨hq.1.le, hq.2.le⟩ hG).trans hMass
  calc
    ‖((innerSL ℝ) (F t))
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) -
      ((innerSL ℝ) (F q))
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)‖ =
        ‖(∫ r in (0 : ℝ)..t, g r) -
          (∫ r in (0 : ℝ)..q, g r)‖ := congrArg norm hEq
    _ ≤ ‖∫ r in (0 : ℝ)..t, g r‖ +
        ‖∫ r in (0 : ℝ)..q, g r‖ := norm_sub_le _ _
    _ ≤ M * ‖h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ‖ +
        M * ‖h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ‖ :=
      add_le_add hBoundT hBoundQ
    _ = (2 * M) * ‖h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ‖ := by
      ring

/-- Density of arbitrary three-component physical Schwartz functions
transfers a single uniform weak pairing bound to the norm of the actual
physical Hilbert-space difference. This is where the common dual budget
is essential. -/
theorem h3Audit_initialSchwartzDense_pairingBound_implies_normBound
    (V W : H3PhysicalRealFinVectorL2Hilbert)
    (M : ℝ) (hM : 0 ≤ M)
    (hProbe : ∀ Φ : H3PhysicalRealFinVectorSchwartz,
      ‖((innerSL ℝ) V)
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) -
        ((innerSL ℝ) W)
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)‖ ≤
        M * ‖h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ‖) :
    ‖V - W‖ ≤ M := by
  let p : H3PhysicalRealFinVectorL2Hilbert → Prop :=
    fun ψ => ‖((innerSL ℝ) (V - W)) ψ‖ ≤ M * ‖ψ‖
  have hClosed : IsClosed {ψ : H3PhysicalRealFinVectorL2Hilbert | p ψ} := by
    dsimp only [p]
    exact isClosed_le
      (((innerSL ℝ) (V - W)).continuous.norm)
      (continuous_const.mul continuous_norm)
  have hAll : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert, p ψ := by
    intro ψ
    apply DenseRange.induction_on
      (p := p)
      denseRange_h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert
      ψ
    · exact hClosed
    · intro Φ
      dsimp only [p]
      change ‖inner ℝ (V - W)
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)‖ ≤
        M * ‖h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ‖
      simpa only [innerSL_apply_apply, inner_sub_left] using hProbe Φ
  have hSelf := hAll (V - W)
  change ‖inner ℝ (V - W) (V - W)‖ ≤ M * ‖V - W‖ at hSelf
  rw [real_inner_self_eq_norm_sq] at hSelf
  have hSquare : ‖V - W‖ ^ 2 ≤ M * ‖V - W‖ := by
    have hSqNonneg : 0 ≤ ‖V - W‖ ^ 2 := sq_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hSqNonneg] using hSelf
  by_cases hZero : ‖V - W‖ = 0
  · simpa only [hZero] using hM
  · have hPos : 0 < ‖V - W‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hZero)
    nlinarith

/-- Full physical Hilbert velocity is bounded at EVERY early positive time
from dense Schwartz-test scalar increments with a shared `L¹` dual budget. -/
theorem h3Audit_initialSchwartzDualL1_uniformOldL2
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b M : ℝ) (hb : 0 < b) (hM : 0 ≤ M)
    (hFTC : H3AuditInitialSchwartzDualL1IncrementOn F b M) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ‖F t‖ ≤ ‖F (b / 2)‖ + 2 * M := by
  have hq : b / 2 ∈ Set.Ioo (0 : ℝ) b := by
    constructor <;> linarith
  intro t ht
  have hDiff : ‖F t - F (b / 2)‖ ≤ 2 * M :=
    h3Audit_initialSchwartzDense_pairingBound_implies_normBound
      (F t) (F (b / 2)) (2 * M) (by positivity)
      (h3Audit_initialSchwartzDualL1_pairingIncrement_le
        F b M hb hFTC (b / 2) t hq ht)
  have hTri : ‖F t‖ ≤ ‖F t - F (b / 2)‖ + ‖F (b / 2)‖ := by
    simpa only [sub_add_cancel] using
      norm_add_le (F t - F (b / 2)) (F (b / 2))
  linarith

/-- Physical initial-value data with a *Schwartz-test* temporal weak FTC
and one uniform dual `L¹` bound. These hypotheses are distinct from the
separate old/selected comparison inequality. -/
def H3AuditInitialCanonicalSchwartzDualL1RelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b : ℝ),
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    ∃ (M K : ℝ),
      0 ≤ M ∧
      H3AuditInitialSchwartzDualL1IncrementOn
        (h3AuditInitialOldPhysicalHilbertTotal hH3) b M ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
          IntervalIntegrable (fun s => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|))

/-- The Schwartz weak-FTC common dual budget manufactures the genuine
cofinal kinetic anchors, using the exact old-physical-velocity kinetic
energy identity from the preceding initial comparison audit. -/
theorem h3Audit_initialSchwartzDualL1_implies_kineticAnchorData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalSchwartzDualL1RelativeEnergyData hH3) :
    H3AuditInitialCanonicalCofinalKineticAnchorsRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, M, K, hM, hFTC, hEpsilon⟩ := hData
  let F := h3AuditInitialOldPhysicalHilbertTotal hH3
  let C : ℝ := ‖F (b / 2)‖ + 2 * M
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hBound : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b → ‖F t‖ ≤ C := by
    exact h3Audit_initialSchwartzDualL1_uniformOldL2 F b M hb hM hFTC
  have hKinetic : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u t ≤ C ^ 2 := by
    intro t ht
    have htT : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨ht.1, lt_trans ht.2 hbT⟩
    have hSq := h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
      hH3 t htT
    calc
      velocityH3Energy0At u t = ‖F t‖ ^ 2 := hSq.symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hBound t ht) 2
  have hSamples : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧
        velocityH3Energy0At u s ≤ C ^ 2 := by
    intro t ht
    have hs : t / 2 ∈ Set.Ioo (0 : ℝ) t := by
      constructor <;> linarith [ht.1]
    have hsB : t / 2 ∈ Set.Ioo (0 : ℝ) b :=
      ⟨hs.1, lt_trans hs.2 ht.2⟩
    exact ⟨t / 2, hs, hKinetic (t / 2) hsB⟩
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, C ^ 2, K, sq_nonneg C, hSamples, hEpsilon⟩

/-- Compact weak-test initial uniqueness from the common dual temporal
Schwartz increment bound and independent vanishing residual comparison. -/
theorem h3Audit_initialSchwartzDualL1_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalSchwartzDualL1RelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialCofinalKineticAnchors_implies_compactWeakComparisonData
    hH3 (h3Audit_initialSchwartzDualL1_implies_kineticAnchorData hH3 hData)

/-- Consequently, the actual initial physical L² and upper H³ traces are
outputs rather than inputs of the selected/old comparison. -/
theorem h3Audit_initialSchwartzDualL1_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalSchwartzDualL1RelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialCofinalKineticAnchors_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialSchwartzDualL1_implies_kineticAnchorData hH3 hData)

/-- The terminal strong-H³ actual-vorticity endpoint is still separate. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialSchwartzDualL1
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalSchwartzDualL1RelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCofinalKineticAnchors
    hH3 hClass i hPhysical
    (h3Audit_initialSchwartzDualL1_implies_kineticAnchorData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
