import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopFixedForcingComponent244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Bound.Forcing
import Mathlib.Tactic

/-!
# Necessary order-four velocity-convolution corridor for a fixed third-radial Leray escape

The previous checkpoint freezes an actual order-three Leray forcing coordinate
whose Fourier L² mass is arbitrarily large on every terminal subtail whenever
the physical fourth-radial top mass escapes. The existing quantitative
finite-Leray convolution estimate, with m=3, bounds its L² norm by nine
order-four raw velocity-product convolution norms.

The convolution bound uses input moments at order 2(m+1)=8. We retain this
regularity explicitly as a hypothesis: we do NOT infer order-eight raw moments
from the H³ energy bound alone. The conclusion remains a necessary escape
corridor, not a terminal bound, and the ordered velocity-product pair in the
final theorem may depend on the chosen tail and threshold.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- Explicit high-moment premise needed to apply the already-proved order-four
raw convolution inequality to the actual time-slice velocity state. -/
def h3PathVelocityRawEightMomentsAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) : Prop :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  ∀ k : Fin 3, H3RawFourierMomentIntegrable (8 : ℝ) (U k)

/-- Nine-term, physical order-four velocity-product convolution envelope.
Each term is the genuine `L²` norm of a raw `U_k * U_j` convolution with
four radial Fourier weights. -/
noncomputable def h3RawOrderFourVelocityConvolutionEnvelope244
    (U : H3SpectralFinVectorState)
    (hM : ∀ k : Fin 3, H3RawFourierMomentIntegrable (8 : ℝ) (U k)) : ℝ :=
  ∑ k : Fin 3, 2 *
    (∑ j : Fin 3, (2 * Real.pi) *
      ‖h3RawProductConvolutionRadialFourierL2 4
        (U k) (U j) (hM k) (hM j)‖)

/-- At each actual strict physical time, the third-radial nonlinear Leray
forcing norm is bounded by the nine genuine order-four velocity convolutions.
No abstract forcing envelope has been substituted for the PDE state. -/
theorem h3Path_thirdRadialForcing_le_orderFourConvolutionEnvelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 3)
    (hMom : h3PathVelocityRawEightMomentsAt244 hH3 hClass ht) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
        hH3 hClass i t‖ ≤
      h3RawOrderFourVelocityConvolutionEnvelope244 U
        (show ∀ k : Fin 3, H3RawFourierMomentIntegrable (8 : ℝ) (U k) from hMom) := by
  dsimp only
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  have hM : ∀ k : Fin 3, H3RawFourierMomentIntegrable (8 : ℝ) (U k) := by
    exact hMom
  have hEq :
      h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
        hH3 hClass ht i =
      h3RawFinLerayOuterProductDivergenceRadialFourierL2
        3 U U i hM hM := by
    apply MeasureTheory.Lp.ext
    have hLeft :=
      h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At_ae
        hH3 hClass ht i
    have hRight :=
      h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
        3 U U i hM hM
    filter_upwards [hLeft, hRight] with ξ hL hR
    exact hL.trans hR.symm
  have hBound :=
    norm_h3RawFinLerayOuterProductDivergenceRadialFourierL2_le
      3 U U i hM hM
  rw [← hEq] at hBound
  rw [h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_eq
    hH3 hClass ht i]
  change ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
      hH3 hClass ht i‖ ≤
    h3RawOrderFourVelocityConvolutionEnvelope244 U hM
  exact hBound

/-- A quantitative finite-pair pigeonhole principle with the exact Leray
coefficient `2`, the divergence coefficient `2π`, and nine ordered pairs. -/
theorem h3_scalar_orderFourConvolutionBudget_forces_largePair244
    (f : Fin 3 → Fin 3 → ℝ) (K : ℝ)
    (hLarge : (36 * Real.pi) * K <
      ∑ k : Fin 3, 2 * (∑ j : Fin 3, (2 * Real.pi) * f k j)) :
    ∃ k j : Fin 3, K < f k j := by
  classical
  by_contra hNone
  have hEach (k j : Fin 3) : f k j ≤ K := by
    exact le_of_not_gt (fun h => hNone ⟨k, j, h⟩)
  have hSumLe :
      (∑ k : Fin 3, 2 * (∑ j : Fin 3, (2 * Real.pi) * f k j)) ≤
        ∑ k : Fin 3, 2 * (∑ j : Fin 3, (2 * Real.pi) * K) := by
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hEach k j) (by positivity)
  have hEval :
      (∑ k : Fin 3, 2 * (∑ j : Fin 3, (2 * Real.pi) * K)) =
        (36 * Real.pi) * K := by
    simp
    ring
  rw [hEval] at hSumLe
  exact (not_lt_of_ge hSumLe) hLarge

/-- Time-dependent norm of one actual ordered velocity convolution pair.
It is zero-extended outside the strict physical interval. -/
noncomputable def h3PathOrderFourVelocityConvolutionPairNorm244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (k j : Fin 3) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ioo a T then
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    let hM : ∀ x : Fin 3, H3RawFourierMomentIntegrable (8 : ℝ) (U x) :=
      hMom t ht
    ‖h3RawProductConvolutionRadialFourierL2
      4 (U k) (U j) (hM k) (hM j)‖
  else 0

/-- On strict time slices the zero-extended pair norm is literally the
radial order-four product-convolution norm. -/
theorem h3PathOrderFourVelocityConvolutionPairNorm_eq244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (ht : t ∈ Set.Ioo a T) (k j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    let hM : ∀ x : Fin 3, H3RawFourierMomentIntegrable (8 : ℝ) (U x) :=
      hMom t ht
    h3PathOrderFourVelocityConvolutionPairNorm244
      hH3 hClass hMom k j t =
    ‖h3RawProductConvolutionRadialFourierL2
      4 (U k) (U j) (hM k) (hM j)‖ := by
  dsimp only
  unfold h3PathOrderFourVelocityConvolutionPairNorm244
  simp only [dif_pos ht]

/-- Under the explicitly required order-eight input moments, the escape of
physical top dissipation forces arbitrarily large order-four velocity-product
convolutions on EVERY later terminal subtail. One fixed forcing coordinate
works for all tails; the ordered product pair may vary with the witness. -/
theorem h3Path_unboundedPhysicalTop_forces_orderFourVelocityConvolutionPairs244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht) :
    ∃ i₀ : Fin 3,
      (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
        ∃ r, r ∈ Set.Ioo σ T ∧
          K < (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
            hH3 hClass i₀ r‖ : ℝ) ^ 2) ∧
      (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
        ∃ r, r ∈ Set.Ioo σ T ∧
          ∃ k j : Fin 3,
            K < h3PathOrderFourVelocityConvolutionPairNorm244
              hH3 hClass hMom k j r) := by
  obtain ⟨i₀, hi₀⟩ :=
    h3Path_unboundedPhysicalTop_forces_fixedThirdRadialForcingCofinal244
      hH3 hClass hs hEscape
  refine ⟨i₀, hi₀, ?_⟩
  intro σ hσ K
  let L : ℝ := (36 * Real.pi) * (max K 0 + 1)
  have hC : 0 < 36 * Real.pi := by positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨r, hr, hLarge⟩ := hi₀ σ hσ ((L + 1) ^ 2)
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 (lt_trans hσ.1 hr.1), hr.2⟩
  have hNormLarge : L <
      ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
        hH3 hClass i₀ r‖ := by
    by_contra hn
    have hLe := le_of_not_gt hn
    have hSq :
        (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
          hH3 hClass i₀ r‖ : ℝ) ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hLe 2
    nlinarith only [hLarge, hSq, hL]
  let htAbs : r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hrClass.1, hrClass.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 r htAbs
  have hM : ∀ k : Fin 3, H3RawFourierMomentIntegrable (8 : ℝ) (U k) :=
    hMom r hrClass
  have hEnvelopeBound :=
    h3Path_thirdRadialForcing_le_orderFourConvolutionEnvelope244
      hH3 hClass hrClass i₀ (hMom r hrClass)
  have hLargeBudget :
      (36 * Real.pi) * K <
        ∑ k : Fin 3, 2 *
          (∑ j : Fin 3, (2 * Real.pi) *
            ‖h3RawProductConvolutionRadialFourierL2 4
              (U k) (U j) (hM k) (hM j)‖) := by
    have hK : K < max K 0 + 1 := by
      have hMax : K ≤ max K 0 := le_max_left _ _
      linarith only [hMax]
    have hScaled : (36 * Real.pi) * K < L := by
      dsimp only [L]
      exact mul_lt_mul_of_pos_left hK hC
    have hNormBudget :
        ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
            hH3 hClass i₀ r‖ ≤
          ∑ k : Fin 3, 2 *
            (∑ j : Fin 3, (2 * Real.pi) *
              ‖h3RawProductConvolutionRadialFourierL2 4
                (U k) (U j) (hM k) (hM j)‖) := by
      exact hEnvelopeBound
    exact lt_of_lt_of_le (lt_trans hScaled hNormLarge) hNormBudget
  obtain ⟨k, j, hPair⟩ :=
    h3_scalar_orderFourConvolutionBudget_forces_largePair244
      (fun k j => ‖h3RawProductConvolutionRadialFourierL2
        4 (U k) (U j) (hM k) (hM j)‖) K hLargeBudget
  refine ⟨r, hr, k, j, ?_⟩
  rw [h3PathOrderFourVelocityConvolutionPairNorm_eq244
    hH3 hClass hMom hrClass k j]
  exact hPair

end
end PrimeTensor.FirstMonomialTriad
