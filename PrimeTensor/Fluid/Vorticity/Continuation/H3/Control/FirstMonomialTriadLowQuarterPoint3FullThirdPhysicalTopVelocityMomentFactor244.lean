import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopConvolutionCorridor244
import Mathlib.Tactic

/-!
# From genuine order-four convolution escape to six velocity Fourier factors

The quantitative order-four convolution bound charges only actual Fourier
velocity quantities: the unweighted L² norms, the two L¹ masses, and the
order-eight raw moment masses. An unbounded output convolution forces one
of these six input factors to become arbitrarily large. The input moment
integrability premise is retained rather than derived from H³ alone.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- Exact Young upper budget for one velocity-pair radial-four convolution. -/
noncomputable def h3RawOrderEightVelocityPairMomentBudget244
    (U : H3SpectralFinVectorState) (k j : Fin 3) : ℝ :=
  (‖h3SpectralScalarRawFourierConjL2 (U k)‖ *
    ‖h3SpectralScalarRawFourierL2 (U j)‖) *
    (h3FourierMomentSplitCoefficient (8 : ℝ) *
      (h3SpectralScalarRawFourierMomentMass (8 : ℝ) (U k) *
         h3SpectralScalarRawFourierL1Mass (U j) +
       h3SpectralScalarRawFourierL1Mass (U k) *
         h3SpectralScalarRawFourierMomentMass (8 : ℝ) (U j)))

/-- Time-slice eighth-order Young budget, zero-extended off the strict class. -/
noncomputable def h3PathOrderEightVelocityPairMomentBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k j : Fin 3) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ioo a T then
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    h3RawOrderEightVelocityPairMomentBudget244 U k j
  else 0

/-- The six primitive factors of the genuine velocity convolution budget. -/
noncomputable def h3RawOrderEightVelocityPairPrimitive244
    (U : H3SpectralFinVectorState) (k j : Fin 3) (q : Fin 6) : ℝ :=
  if q = 0 then ‖h3SpectralScalarRawFourierConjL2 (U k)‖
  else if q = 1 then ‖h3SpectralScalarRawFourierL2 (U j)‖
  else if q = 2 then h3SpectralScalarRawFourierMomentMass (8 : ℝ) (U k)
  else if q = 3 then h3SpectralScalarRawFourierL1Mass (U j)
  else if q = 4 then h3SpectralScalarRawFourierL1Mass (U k)
  else h3SpectralScalarRawFourierMomentMass (8 : ℝ) (U j)

/-- Time-slice primitive factor, also zero-extended outside the H³ class. -/
noncomputable def h3PathOrderEightVelocityPairPrimitive244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k j : Fin 3) (q : Fin 6) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ioo a T then
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    h3RawOrderEightVelocityPairPrimitive244 U k j q
  else 0

/-- The physical convolution has the ACTUAL eighth-moment Young budget. -/
theorem h3Path_orderFourConvolutionPair_sq_le_eightMomentBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMom : ∀ r (hr : r ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass hr)
    (ht : t ∈ Set.Ioo a T) (k j : Fin 3) :
    (h3PathOrderFourVelocityConvolutionPairNorm244 hH3 hClass hMom k j t) ^ 2 ≤
      h3PathOrderEightVelocityPairMomentBudget244 hH3 hClass k j t := by
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  have hM : ∀ x : Fin 3, H3RawFourierMomentIntegrable (8 : ℝ) (U x) :=
    hMom t ht
  have hBase := norm_sq_h3RawProductConvolutionRadialFourierL2_le_stateMasses
    4 (U k) (U j) (hM k) (hM j)
  rw [h3PathOrderFourVelocityConvolutionPairNorm_eq244
    hH3 hClass hMom ht k j]
  change ‖h3RawProductConvolutionRadialFourierL2
      4 (U k) (U j) (hM k) (hM j)‖ ^ 2 ≤
    h3PathOrderEightVelocityPairMomentBudget244 hH3 hClass k j t
  unfold h3PathOrderEightVelocityPairMomentBudget244
  simp only [dif_pos ht]
  exact hBase

/-- Universal six-factor fourth-power bound. Its coefficient is precisely
that of the existing Fourier moment splitting inequality. -/
theorem h3_scalar_sixFactorYoungBudget_le_fourthPower244
    (A B X P Q Y C H : ℝ)
    (hH : 0 ≤ H) (hC : 0 ≤ C)
    (_hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hX0 : 0 ≤ X) (hP0 : 0 ≤ P)
    (hQ0 : 0 ≤ Q) (hY0 : 0 ≤ Y)
    (hA : A ≤ H) (hB : B ≤ H)
    (hX : X ≤ H) (hP : P ≤ H)
    (hQ : Q ≤ H) (hY : Y ≤ H) :
    A * B * (C * (X * P + Q * Y)) ≤ (2 * C) * H ^ 4 := by
  have hAB : A * B ≤ H ^ 2 := by
    have h := mul_le_mul hA hB hB0 hH
    nlinarith only [h]
  have hXP : X * P ≤ H ^ 2 := by
    have h := mul_le_mul hX hP hP0 hH
    nlinarith only [h]
  have hQY : Q * Y ≤ H ^ 2 := by
    have h := mul_le_mul hQ hY hY0 hH
    nlinarith only [h]
  have hSum : X * P + Q * Y ≤ 2 * H ^ 2 := by
    linarith only [hXP, hQY]
  have hSum0 : 0 ≤ X * P + Q * Y :=
    add_nonneg (mul_nonneg hX0 hP0) (mul_nonneg hQ0 hY0)
  have hWeighted : C * (X * P + Q * Y) ≤ C * (2 * H ^ 2) :=
    mul_le_mul_of_nonneg_left hSum hC
  have hWeighted0 : 0 ≤ C * (X * P + Q * Y) :=
    mul_nonneg hC hSum0
  have hProd : A * B * (C * (X * P + Q * Y)) ≤
      H ^ 2 * (C * (2 * H ^ 2)) :=
    mul_le_mul hAB hWeighted hWeighted0 (sq_nonneg H)
  calc
    A * B * (C * (X * P + Q * Y)) ≤
        H ^ 2 * (C * (2 * H ^ 2)) := hProd
    _ = (2 * C) * H ^ 4 := by ring

/-- Boundedness of the six genuine velocity factors controls the input-pair
Young budget; this is an exact abstraction of the order-eight estimate. -/
theorem h3_orderEightVelocityPairBudget_le_of_primitiveCeiling244
    (U : H3SpectralFinVectorState) (k j : Fin 3) (H : ℝ)
    (hH : 0 ≤ H)
    (hFactors : ∀ q : Fin 6,
      h3RawOrderEightVelocityPairPrimitive244 U k j q ≤ H) :
    h3RawOrderEightVelocityPairMomentBudget244 U k j ≤
      (2 * h3FourierMomentSplitCoefficient (8 : ℝ)) * H ^ 4 := by
  have ha : ‖h3SpectralScalarRawFourierConjL2 (U k)‖ ≤ H := by
    simpa [h3RawOrderEightVelocityPairPrimitive244] using hFactors (0 : Fin 6)
  have hb : ‖h3SpectralScalarRawFourierL2 (U j)‖ ≤ H := by
    simpa [h3RawOrderEightVelocityPairPrimitive244] using hFactors (1 : Fin 6)
  have hx : h3SpectralScalarRawFourierMomentMass (8 : ℝ) (U k) ≤ H := by
    simpa [h3RawOrderEightVelocityPairPrimitive244] using hFactors (2 : Fin 6)
  have hp : h3SpectralScalarRawFourierL1Mass (U j) ≤ H := by
    simpa [h3RawOrderEightVelocityPairPrimitive244] using hFactors (3 : Fin 6)
  have hq : h3SpectralScalarRawFourierL1Mass (U k) ≤ H := by
    simpa [h3RawOrderEightVelocityPairPrimitive244] using hFactors (4 : Fin 6)
  have hy : h3SpectralScalarRawFourierMomentMass (8 : ℝ) (U j) ≤ H := by
    simpa [h3RawOrderEightVelocityPairPrimitive244] using hFactors (5 : Fin 6)
  unfold h3RawOrderEightVelocityPairMomentBudget244
  exact h3_scalar_sixFactorYoungBudget_le_fourthPower244
    _ _ _ _ _ _ _ H hH
    (h3FourierMomentSplitCoefficient_nonneg (8 : ℝ))
    (norm_nonneg _) (norm_nonneg _)
    (h3SpectralScalarRawFourierMomentMass_nonneg _ _)
    (h3SpectralScalarRawFourierL1Mass_nonneg _)
    (h3SpectralScalarRawFourierL1Mass_nonneg _)
    (h3SpectralScalarRawFourierMomentMass_nonneg _ _)
    ha hb hx hp hq hy

/-- Under top-moment escape, on every terminal subtail some actual velocity
pair has an arbitrarily large order-eight input Young budget. -/
theorem h3Path_unboundedPhysicalTop_forces_eightMomentPairBudgets244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht) :
    ∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ k j : Fin 3,
        K < h3PathOrderEightVelocityPairMomentBudget244
          hH3 hClass k j r := by
  obtain ⟨_i₀, _hi₀, hPairs⟩ :=
    h3Path_unboundedPhysicalTop_forces_orderFourVelocityConvolutionPairs244
      hH3 hClass hs hEscape hMom
  intro σ hσ K
  let L : ℝ := max K 0 + 1
  have hLnonneg : 0 ≤ L := by dsimp [L]; positivity
  have hLone : 1 ≤ L := by
    dsimp [L]
    have hMax : 0 ≤ max K 0 := le_max_right K 0
    linarith only [hMax]
  have hKL : K < L ^ 2 := by
    have hK : K < L := by
      dsimp [L]
      have hMax : K ≤ max K 0 := le_max_left K 0
      linarith only [hMax]
    have hSq : L ≤ L ^ 2 := by
      have hMul : 0 ≤ L * (L - 1) :=
        mul_nonneg hLnonneg (by linarith only [hLone])
      nlinarith only [hMul]
    exact lt_of_lt_of_le hK hSq
  obtain ⟨r, hr, k, j, hPair⟩ := hPairs σ hσ L
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 (lt_trans hσ.1 hr.1), hr.2⟩
  have hSquare : L ^ 2 ≤
      (h3PathOrderFourVelocityConvolutionPairNorm244
        hH3 hClass hMom k j r) ^ 2 :=
    pow_le_pow_left₀ hLnonneg (le_of_lt hPair) 2
  have hBudget := h3Path_orderFourConvolutionPair_sq_le_eightMomentBudget244
    hH3 hClass hMom hrClass k j
  refine ⟨r, hr, k, j, ?_⟩
  exact lt_of_lt_of_le hKL (hSquare.trans hBudget)

/-- One of the SIX genuine input Fourier factors must escape on every terminal
subtail. The pair and factor index may vary with the threshold. -/
theorem h3Path_unboundedPhysicalTop_forces_eightMomentPrimitiveEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht) :
    ∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ k j : Fin 3, ∃ q : Fin 6,
        K < h3PathOrderEightVelocityPairPrimitive244
          hH3 hClass k j q r := by
  intro σ hσ K
  let H : ℝ := max K 0 + 1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let C : ℝ := h3FourierMomentSplitCoefficient (8 : ℝ)
  let B : ℝ := (2 * C) * H ^ 4
  obtain ⟨r, hr, k, j, hLarge⟩ :=
    h3Path_unboundedPhysicalTop_forces_eightMomentPairBudgets244
      hH3 hClass hs hEscape hMom σ hσ B
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 (lt_trans hσ.1 hr.1), hr.2⟩
  let hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hrClass.1, hrClass.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 r hrAbs
  have hSome : ∃ q : Fin 6,
      K < h3RawOrderEightVelocityPairPrimitive244 U k j q := by
    by_contra hNo
    have hFactors : ∀ q : Fin 6,
        h3RawOrderEightVelocityPairPrimitive244 U k j q ≤ H := by
      intro q
      have hNot : ¬ K < h3RawOrderEightVelocityPairPrimitive244 U k j q := by
        intro hHigh
        exact hNo ⟨q, hHigh⟩
      exact (le_of_not_gt hNot).trans (by
        dsimp [H]
        have hMax : K ≤ max K 0 := le_max_left K 0
        linarith only [hMax])
    have hBound := h3_orderEightVelocityPairBudget_le_of_primitiveCeiling244
      U k j H hH hFactors
    have hStrict : B < h3RawOrderEightVelocityPairMomentBudget244 U k j := by
      unfold h3PathOrderEightVelocityPairMomentBudget244 at hLarge
      simp only [dite_eq_left hrClass] at hLarge
      exact hLarge
    have hUpper : h3RawOrderEightVelocityPairMomentBudget244 U k j ≤ B := by
      simpa only [B, C] using hBound
    exact (not_lt_of_ge hUpper) hStrict
  obtain ⟨q, hHigh⟩ := hSome
  refine ⟨r, hr, k, j, q, ?_⟩
  unfold h3PathOrderEightVelocityPairPrimitive244
  simp only [dite_eq_left hrClass]
  exact hHigh


end
end PrimeTensor.FirstMonomialTriad
