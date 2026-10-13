import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialFrequentKineticOneDirectionIncrements
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialProjectedRHSWeakFTCControl

/-!
# Lift Schwartz-tested momentum evolution to the initial L² vector

The preceding one-direction initial trace assumes scalar L¹ momentum
increments paired with the actual physical U₀, which need not be Schwartz.

This module instead begins with a COMMON physical Bochner L¹ source G
and the Schwartz-tested Bochner momentum identity. Density of Schwartz
vectors upgrades the test identity to the entire physical Hilbert space.
A bounded real inner-product functional commutes with the Bochner
interval integral, supplying the required U₀ scalar increment identity.

This is a conditional SOURCE-STRENGTH tradeoff: L¹_t L²_x integrability
of the physical source is independently required, not derived from
open-time H³ admissibility. Frequent kinetic sample compatibility and
the one-vector self-pairing sample remain independent inputs. No
unconditional Navier--Stokes regularity or terminal H³ closure follows.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Schwartz-tested equality against one physical Bochner integral
determines the entire Hilbert momentum increment, by exact density. -/
theorem h3Audit_initialSchwartzBochner_extends_hilbertIncrement
    (F G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (s t : ℝ)
    (hWeak : ∀ Φ : H3PhysicalRealFinVectorSchwartz,
      inner ℝ (F t - F s)
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) =
        inner ℝ (∫ r in s..t, G r)
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) :
    F t - F s = ∫ r in s..t, G r := by
  apply DenseRange.eq_of_inner_left ℝ
    denseRange_h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert
  intro Φ
  exact hWeak Φ

/-- Commuting a fixed real L² inner-product functional with a
Bochner interval integral requires no Schwartz regularity of the
fixed vector. -/
theorem h3Audit_initialBochner_intervalInner_comm
    (G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (s t : ℝ)
    (hG : IntervalIntegrable G volume s t)
    (ψ : H3PhysicalRealFinVectorL2Hilbert) :
    inner ℝ (∫ r in s..t, G r) ψ =
      ∫ r in s..t, inner ℝ (G r) ψ := by
  have hComm :
      inner ℝ ψ (∫ r in s..t, G r) =
        ∫ r in s..t, inner ℝ ψ (G r) := by
    change ((innerSL ℝ) ψ) (∫ r in s..t, G r) =
      ∫ r in s..t, ((innerSL ℝ) ψ) (G r)
    exact (((innerSL ℝ) ψ).intervalIntegral_comp_comm hG).symm
  have hIntegrands :
      (fun r : ℝ => inner ℝ ψ (G r)) =
        (fun r : ℝ => inner ℝ (G r) ψ) := by
    funext r
    exact (real_inner_comm ψ (G r)).symm
  calc
    inner ℝ (∫ r in s..t, G r) ψ =
        inner ℝ ψ (∫ r in s..t, G r) := real_inner_comm _ _
    _ = ∫ r in s..t, inner ℝ ψ (G r) := hComm
    _ = ∫ r in s..t, inner ℝ (G r) ψ := by rw [hIntegrands]

/-- With a physical L¹ source, Schwarz-tested Bochner increment
identities pass to ALL physical Hilbert tests, including U₀. -/
theorem h3Audit_initialSchwartzBochner_allPhysicalScalarIncrements
    (F G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hG : IntervalIntegrable G volume 0 b)
    (hWeak : ∀ (Φ : H3PhysicalRealFinVectorSchwartz)
      (s t : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b →
      t ∈ Set.Ioo (0 : ℝ) b →
        inner ℝ (F t - F s)
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) =
        inner ℝ (∫ r in s..t, G r)
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) :
    ∀ (ψ : H3PhysicalRealFinVectorL2Hilbert) (s t : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b →
      t ∈ Set.Ioo (0 : ℝ) b →
        inner ℝ (F t) ψ - inner ℝ (F s) ψ =
          ∫ r in s..t, inner ℝ (G r) ψ := by
  intro ψ s t hs ht
  have hSub : Set.uIcc s t ⊆ Set.uIcc (0 : ℝ) b := by
    intro x hx
    have hxb := h3Audit_positiveUnorderedInterval_subset_initial
      b s t hs ht hx
    simpa only [Set.uIcc_of_le hb.le] using hxb
  have hLocal : IntervalIntegrable G volume s t :=
    hG.mono_set hSub
  have hVec : F t - F s = ∫ r in s..t, G r :=
    h3Audit_initialSchwartzBochner_extends_hilbertIncrement
      F G s t (fun Φ => hWeak Φ s t hs ht)
  calc
    inner ℝ (F t) ψ - inner ℝ (F s) ψ =
        inner ℝ (F t - F s) ψ := by rw [inner_sub_left]
    _ = inner ℝ (∫ r in s..t, G r) ψ := by rw [hVec]
    _ = ∫ r in s..t, inner ℝ (G r) ψ :=
      h3Audit_initialBochner_intervalInner_comm G s t hLocal ψ

/-- The initial-value interface has ONE physical L¹ momentum source,
Schwartz weak Bochner increments, frequent kinetic anchors, and
ONE self-pairing matching sequence. The self-pair scalar FTC is
derived rather than postulated. -/
def H3AuditInitialFrequentKineticSchwartzBochnerData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) : Prop :=
  ∃ (G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (τ σ : ℕ → ℝ),
    IntervalIntegrable G volume 0 b ∧
    (∀ (Φ : H3PhysicalRealFinVectorSchwartz) (s t : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b →
      t ∈ Set.Ioo (0 : ℝ) b →
        inner ℝ
            (h3AuditInitialOldPhysicalHilbertTotal hH3 t -
              h3AuditInitialOldPhysicalHilbertTotal hH3 s)
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) =
          inner ℝ (∫ r in s..t, G r)
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) ∧
    Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        velocityH3Energy0At u (τ n) ≤ velocityH3Energy0At u 0 + ε) ∧
    Tendsto σ atTop (𝓝[>] (0 : ℝ)) ∧
    Tendsto
      (fun n : ℕ =>
        inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 (σ n))
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0))
      atTop
      (𝓝 (‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2))

/-- The initial-datum scalar source g(r)=⟪G(r),U₀⟫ is a
provably integrable CONSEQUENCE of the common Bochner physical
source and Schwartz-tested momentum increments. -/
theorem h3Audit_initialSchwartzBochner_implies_oneDirectionData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) (hb : 0 < b)
    (hData : H3AuditInitialFrequentKineticSchwartzBochnerData
      hH3 hInt0 hMeas0 b) :
    H3AuditInitialFrequentKineticOneDirectionIncrementData
      hH3 hInt0 hMeas0 b := by
  obtain ⟨G, τ, σ, hG, hWeak, hτ, hFrequent, hσ, hSample⟩ := hData
  let U₀ : H3PhysicalRealFinVectorL2Hilbert :=
    h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  have hg : IntervalIntegrable
      (fun r : ℝ => inner ℝ (G r) U₀) volume 0 b := by
    simpa only [innerSL_apply_apply] using
      (h3Audit_initialProjectedRHS_scalarPairing_intervalIntegrable
        G b hb.le hG U₀)
  have hInc : ∀ (s t : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b →
      t ∈ Set.Ioo (0 : ℝ) b →
        inner ℝ (F t) U₀ - inner ℝ (F s) U₀ =
          ∫ r in s..t, inner ℝ (G r) U₀ :=
    h3Audit_initialSchwartzBochner_allPhysicalScalarIncrements
      F G b hb hG hWeak U₀
  exact ⟨τ, (fun r : ℝ => inner ℝ (G r) U₀), σ,
    hτ, hFrequent, hg, hInc, hσ, hSample⟩

/-- Reuse the exact kinetic ceiling, scalar one-vector limit and
Radon--Riesz theorem to derive the strong physical initial and
kinetic right traces from Schwartz-tested Bochner momentum evolution. -/
theorem h3Audit_initialSchwartzBochner_physicalAndKineticRightTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hData : H3AuditInitialFrequentKineticSchwartzBochnerData
      hH3 hInt0 hMeas0 b) :
    Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ∧
    Tendsto (velocityH3Energy0At u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (velocityH3Energy0At u 0)) := by
  have hOne : H3AuditInitialFrequentKineticOneDirectionIncrementData
      hH3 hInt0 hMeas0 b :=
    h3Audit_initialSchwartzBochner_implies_oneDirectionData
      hH3 hInt0 hMeas0 b hb hData
  exact (h3Audit_initialFrequentKineticOneDirection_physicalAndKineticRightTrace
    hH3 hInt0 hMeas0 b hb hbT hOne).1

end
end Euclidean
end Bridge
end PrimeTensor
