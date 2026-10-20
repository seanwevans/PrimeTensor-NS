import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSignedSpatialPairingBridge244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdCanonicalPhysicalBridge244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzWeightedReferenceIndependence244
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic

/-!
# Full 243-slot physical H³ signed interpolation equals the canonical Schwartz limit

The previous two increments identified (1) every physical second derivative
with a canonical L⁴ class and (2) the original Point3 signed interpolation
with the 243 corresponding Euclidean L²×L⁴×L⁴ integrals.

This increment uses the same matched real Schwartz family throughout. Its
third jets converge strongly in L² and its second jets strongly in L⁴. The
standard continuous bilinear Holder maps give continuity of each scalar
three-factor integral, without imposing a nonexistent L⁴ bound on D³u or
assuming that u(t) is Schwartz. The ordered 243-term finite sum can then
pass to the limit, and uniqueness identifies the old physical signed total
with the previously defined, choice-independent weighted canonical total.

No statement about the separate 3–3–1 gradient transport is made here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
-- The local axis Fintype must be in scope BEFORE elaborating the
-- Euclidean-space volume measure. The L⁴ exponent fact must also be present
-- before Lean synthesizes the Lp normed/topological carrier instances.
noncomputable local instance signedLimitAxisFintype244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)
local instance signedLimitFact2244 : Fact (1 ≤ (2 : ENNReal)) :=
  ⟨by norm_num⟩
local instance signedLimitFact4244 : Fact (1 ≤ (4 : ENNReal)) :=
  ⟨by norm_num⟩

-- Annotating : Type coerces mathlib's Lp subgroup to its underlying
-- measurable-function carrier, as in H3FourierRealL2.
private abbrev L2Signed244 : Type := H3FourierRealL2
private abbrev L4Signed244 : Type := MeasureTheory.Lp ℝ 4 (volume : Measure V3)
local instance signedLimitHolder44244 : ENNReal.HolderTriple 4 4 2 := by
  have hReal : Real.HolderTriple 4 4 2 := by
    rw [Real.holderTriple_iff]
    norm_num
  simpa using hReal.ennrealOfReal

/-- A genuinely continuous L²×L⁴×L⁴ scalar pairing. The inner multiplication
is the bounded Holder map L⁴×L⁴→L²; the outer map pairs two L² classes. -/
noncomputable def h3CanonicalSignedLpTriple244
    (A : L2Signed244) (B C : L4Signed244) : ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing
    (volume : Measure V3) (2 : ENNReal) (2 : ENNReal) A
    ((ContinuousLinearMap.mul ℝ ℝ).holderL
      (volume : Measure V3) (4 : ENNReal) (4 : ENNReal) (2 : ENNReal) B C)

/-- The abstract continuous pairing is the actual signed Lebesgue integral,
with the original nesting and no absolute values. -/
theorem h3CanonicalSignedLpTriple_eq_integral244
    (A : L2Signed244) (B C : L4Signed244) :
    h3CanonicalSignedLpTriple244 A B C =
      ∫ x : V3, A x * (B x * C x) := by
  unfold h3CanonicalSignedLpTriple244
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  have hBC :=
    (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := (2 : ENNReal)) B C
  apply integral_congr_ae
  filter_upwards [hBC] with x hx
  change A x *
    ((ContinuousLinearMap.mul ℝ ℝ).holder (2 : ENNReal) B C) x =
      A x * (B x * C x)
  rw [hx]
  rfl

/-- Keep the continuity argument parametrized by two bounded bilinear maps.
The type checker never needs to unfold the enormous `holderL` or `lpPairing`
constructions while applying `ContinuousLinearMap.continuous₂`. -/
private theorem h3SignedBilinearComposition_tendsto244
    (M : L4Signed244 →L[ℝ] L4Signed244 →L[ℝ] L2Signed244)
    (P : L2Signed244 →L[ℝ] L2Signed244 →L[ℝ] ℝ)
    (A : ℕ → L2Signed244) (B C : ℕ → L4Signed244)
    (a : L2Signed244) (b c : L4Signed244)
    (hA : Tendsto A atTop (𝓝 a))
    (hB : Tendsto B atTop (𝓝 b))
    (hC : Tendsto C atTop (𝓝 c)) :
    Tendsto (fun n => P (A n) (M (B n) (C n)))
      atTop (𝓝 (P a (M b c))) := by
  have hBC : Tendsto (fun n : ℕ => (B n, C n))
      atTop (𝓝 (b, c)) := hB.prodMk_nhds hC
  have hM : Continuous (fun z : L4Signed244 × L4Signed244 =>
      M z.1 z.2) := M.continuous₂
  have hProduct : Tendsto (fun n => M (B n) (C n))
      atTop (𝓝 (M b c)) :=
    (hM.tendsto (b, c)).comp hBC
  have hAP : Tendsto (fun n : ℕ => (A n, M (B n) (C n)))
      atTop (𝓝 (a, M b c)) := hA.prodMk_nhds hProduct
  have hP : Continuous (fun z : L2Signed244 × L2Signed244 =>
      P z.1 z.2) := P.continuous₂
  exact (hP.tendsto (a, M b c)).comp hAP

/-- No separate uniform-integrability input is needed: the scalar map is
continuous on L²×L⁴×L⁴, so strong convergence suffices. -/
theorem h3CanonicalSignedLpTriple_tendsto244
    (A : ℕ → L2Signed244) (B C : ℕ → L4Signed244)
    (a : L2Signed244) (b c : L4Signed244)
    (hA : Tendsto A atTop (𝓝 a))
    (hB : Tendsto B atTop (𝓝 b))
    (hC : Tendsto C atTop (𝓝 c)) :
    Tendsto (fun n => h3CanonicalSignedLpTriple244 (A n) (B n) (C n))
      atTop (𝓝 (h3CanonicalSignedLpTriple244 a b c)) := by
  let M : L4Signed244 →L[ℝ] L4Signed244 →L[ℝ] L2Signed244 :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL
      (volume : Measure V3) (4 : ENNReal) (4 : ENNReal) (2 : ENNReal)
  let P : L2Signed244 →L[ℝ] L2Signed244 →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing
      (volume : Measure V3) (2 : ENNReal) (2 : ENNReal)
  have hCore : Tendsto (fun n => P (A n) (M (B n) (C n)))
      atTop (𝓝 (P a (M b c))) :=
    h3SignedBilinearComposition_tendsto244 M P A B C a b c hA hB hC
  -- Separate the easy definitional unfolding from the continuity proof.
  change Tendsto (fun n => P (A n) (M (B n) (C n)))
      atTop (𝓝 (P a (M b c)))
  exact hCore

/-- Every one of the 243 signed Schwartz integrals converges to the genuine
physical three-factor integral expressed using canonical L⁴ second jets. -/
theorem h3MatchedSchwartz_signedSlotIntegral_tendsto_physical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier))
    (j r i k l : A3) :
    Tendsto (fun n => lowNormalRealSchwartz_firstMonomialSlotIntegral
      (F.family.approximants n) i k l r j) atTop
      (𝓝 (h3CanonicalSignedFirstMonomialSlotIntegral244 hFourier j r i k l)) := by
  let μ : Measure V3 := volume
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  let D3 : ℕ → SchwartzMap V3 ℝ := fun n =>
    ∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k}
        (∂_{h3FourierAxisDirection l} (F.family.approximants n j)))
  let D2 : ℕ → SchwartzMap V3 ℝ := fun n =>
    ∂_{h3FourierAxisDirection k}
      (∂_{h3FourierAxisDirection l} (F.family.approximants n r))
  let D2' : ℕ → SchwartzMap V3 ℝ := fun n =>
    ∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection r} (F.family.approximants n j))
  let A : ℕ → L2Signed244 := fun n => (D3 n).toLp 2 μ
  let B : ℕ → L4Signed244 := fun n => (D2 n).toLp 4 μ
  let C : ℕ → L4Signed244 := fun n => (D2' n).toLp 4 μ
  let a : L2Signed244 := h3ActualThirdJetOnFourierCarrier244 hInt hMeas
    (h3ClassicalizationFinOfAxis j) i k l
  let b : L4Signed244 := weightedH3CanonicalSecondJetL4Trace244 U
    (h3ClassicalizationFinOfAxis r) k l
  let c : L4Signed244 := weightedH3CanonicalSecondJetL4Trace244 U
    (h3ClassicalizationFinOfAxis j) i r
  have hThirdState : Tendsto
      (fun n => matchedSpectralThirdFourierJets244 (F.spectral n))
      atTop (𝓝 (matchedSpectralThirdFourierJets244 U)) :=
    continuous_matchedSpectralThirdFourierJets244.continuousAt.tendsto.comp
      F.spectral_tendsto
  have hThirdCoord := (tendsto_pi_nhds.mp hThirdState) (j, (i, (k, l)))
  have hThirdSeq : A = fun n =>
      matchedSpectralThirdFourierJets244 (F.spectral n) (j, (i, (k, l))) := by
    funext n
    change (D3 n).toLp 2 μ = _
    exact F.third_exact n j i k l
  have hThirdTarget :
      matchedSpectralThirdFourierJets244 U (j, (i, (k, l))) = a := by
    change h3ToFourierRealL2
      (h3SpectralVelocityThirdPhysicalJetFamily244 U
        (h3ClassicalizationFinOfAxis j) i k l) =
      h3ToFourierRealL2 (velocityH3L2JetAt u t hInt hMeas
        (h3JetSlot3 (h3ClassicalizationFinOfAxis j)
          (h3ClassicalizationFinOfAxis i) (h3ClassicalizationFinOfAxis k)
          (h3ClassicalizationFinOfAxis l)))
    dsimp only [U]
    rw [h3SpectralVelocityThirdPhysicalJetFamily_actualJet244 hFourier]
  have hA : Tendsto A atTop (𝓝 a) := by
    rw [hThirdSeq, ← hThirdTarget]
    exact hThirdCoord
  have hB : Tendsto B atTop (𝓝 b) := by
    have h := weightedH3CanonicalSecondJetL4Trace_tendsto244 U F
      (h3ClassicalizationFinOfAxis r) k l
    simpa only [h3AxisOfFin3_h3ClassicalizationFinOfAxis] using h
  have hC : Tendsto C atTop (𝓝 c) := by
    have h := weightedH3CanonicalSecondJetL4Trace_tendsto244 U F
      (h3ClassicalizationFinOfAxis j) i r
    simpa only [h3AxisOfFin3_h3ClassicalizationFinOfAxis] using h
  have hIntegral (n : ℕ) :
      h3CanonicalSignedLpTriple244 (A n) (B n) (C n) =
        lowNormalRealSchwartz_firstMonomialSlotIntegral
          (F.family.approximants n) i k l r j := by
    rw [h3CanonicalSignedLpTriple_eq_integral244]
    change (∫ x : V3,
      ((D3 n).toLp 2 μ : V3 → ℝ) x *
        (((D2 n).toLp 4 μ : V3 → ℝ) x *
          ((D2' n).toLp 4 μ : V3 → ℝ) x)) =
      ∫ x : V3, D3 n x * (D2 n x * D2' n x)
    apply integral_congr_ae
    filter_upwards [(D3 n).coeFn_toLp 2 μ,
      (D2 n).coeFn_toLp 4 μ, (D2' n).coeFn_toLp 4 μ]
      with x h3 h2 h2'
    rw [h3, h2, h2']
  have hLimit : h3CanonicalSignedLpTriple244 a b c =
      h3CanonicalSignedFirstMonomialSlotIntegral244 hFourier j r i k l := by
    rw [h3CanonicalSignedLpTriple_eq_integral244]
    rfl
  have h := h3CanonicalSignedLpTriple_tendsto244 A B C a b c hA hB hC
  simp_rw [hIntegral] at h
  rw [hLimit] at h
  exact h

/-- Finite coordinate sums preserve scalar limits without requiring a
uniform convergence hypothesis in the spatial variable. -/
private theorem h3FiniteSignedSum_tendsto244
    {J : Type*} [Fintype J] (f : ℕ → J → ℝ) (g : J → ℝ)
    (h : ∀ j, Tendsto (fun n => f n j) atTop (𝓝 (g j))) :
    Tendsto (fun n => ∑ j : J, f n j) atTop (𝓝 (∑ j : J, g j)) := by
  classical
  have hs (s : Finset J) :
      Tendsto (fun n => Finset.sum s (f n)) atTop
        (𝓝 (Finset.sum s g)) := by
    induction s using Finset.induction_on with
    | empty => simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | @insert j s hj ih =>
        simpa only [Finset.sum_insert hj] using (h j).add ih
  exact hs Finset.univ

/-- All 243 strong Schwartz integral limits are simultaneous, with no
index-dependent subsequence. -/
theorem h3MatchedSchwartz_allSignedSlots_tendsto_physical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier)) :
    Tendsto
      (fun n => 2 * (∑ j : A3, ∑ r : A3, ∑ i : A3,
        ∑ k : A3, ∑ l : A3,
          lowNormalRealSchwartz_firstMonomialSlotIntegral
            (F.family.approximants n) i k l r j))
      atTop (𝓝 (h3CanonicalSignedFirstMonomialAggregate244 hFourier)) := by
  have hSlot (j r i k l : A3) :=
    h3MatchedSchwartz_signedSlotIntegral_tendsto_physical244 hFourier F j r i k l
  have hL (j r i k : A3) := h3FiniteSignedSum_tendsto244
    (fun n l => lowNormalRealSchwartz_firstMonomialSlotIntegral
      (F.family.approximants n) i k l r j)
    (fun l => h3CanonicalSignedFirstMonomialSlotIntegral244 hFourier j r i k l)
    (hSlot j r i k)
  have hK (j r i : A3) := h3FiniteSignedSum_tendsto244
    (fun n k => ∑ l : A3, lowNormalRealSchwartz_firstMonomialSlotIntegral
      (F.family.approximants n) i k l r j)
    (fun k => ∑ l : A3, h3CanonicalSignedFirstMonomialSlotIntegral244 hFourier j r i k l)
    (hL j r i)
  have hI (j r : A3) := h3FiniteSignedSum_tendsto244
    (fun n i => ∑ k : A3, ∑ l : A3, lowNormalRealSchwartz_firstMonomialSlotIntegral
      (F.family.approximants n) i k l r j)
    (fun i => ∑ k : A3, ∑ l : A3, h3CanonicalSignedFirstMonomialSlotIntegral244 hFourier j r i k l)
    (hK j r)
  have hR (j : A3) := h3FiniteSignedSum_tendsto244
    (fun n r => ∑ i : A3, ∑ k : A3, ∑ l : A3,
      lowNormalRealSchwartz_firstMonomialSlotIntegral (F.family.approximants n) i k l r j)
    (fun r => ∑ i : A3, ∑ k : A3, ∑ l : A3,
      h3CanonicalSignedFirstMonomialSlotIntegral244 hFourier j r i k l)
    (hI j)
  have hJ := h3FiniteSignedSum_tendsto244
    (fun n j => ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
      lowNormalRealSchwartz_firstMonomialSlotIntegral (F.family.approximants n) i k l r j)
    (fun j => ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
      h3CanonicalSignedFirstMonomialSlotIntegral244 hFourier j r i k l)
    hR
  have hTwo := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ))
    atTop (𝓝 (2 : ℝ))).mul hJ
  simpa only [h3CanonicalSignedFirstMonomialAggregate244] using hTwo

/-- The original signed H³ interpolation equals the choice-independent
weighted spectral Schwartz limit at every Fourier-compatible physical slice.
The equality uses actual 243-slot 2–4–4 integral convergence. -/
theorem h3PathCanonicalFirstMonomialAggregate_eq_weightedCanonicalSigned244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    h3PathCanonicalFirstMonomialAggregateAt u t =
      weightedH3CanonicalSignedFirstMonomial244
        (velocityH3SpectralStateAt u t hInt hMeas hFourier) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  let F := Classical.choice (exists_h3MatchedSchwartzGradientCompletion244 U)
  have hSchwartz : Tendsto
      (fun n => lowNormalRealSchwartzPoint3Monomial (F.family.approximants n))
      atTop (𝓝 (weightedH3CanonicalSignedFirstMonomial244 U)) := by
    exact weightedH3CanonicalSignedFirstMonomial_tendsto244 U
      (h3MatchedGradientCompletion_toSignedCompletion244 U F)
  have hPhysical := h3MatchedSchwartz_allSignedSlots_tendsto_physical244
    hFourier F
  have hReorder (f : A3 → SchwartzMap V3 ℝ) :
      lowNormalRealSchwartzPoint3Monomial f =
        2 * (∑ j : A3, ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
          lowNormalRealSchwartz_firstMonomialSlotIntegral f i k l r j) := by
    rw [lowNormalRealSchwartz_firstMonomial_eq_twice_slotSum]
    congr 1
    simp only [axis_sum_three]
    ac_rfl
  have hSeq :
      (fun n => 2 * (∑ j : A3, ∑ r : A3, ∑ i : A3, ∑ k : A3,
        ∑ l : A3, lowNormalRealSchwartz_firstMonomialSlotIntegral
          (F.family.approximants n) i k l r j)) =
      (fun n => lowNormalRealSchwartzPoint3Monomial (F.family.approximants n)) := by
    funext n
    exact (hReorder (F.family.approximants n)).symm
  rw [hSeq] at hPhysical
  have hUnique : h3CanonicalSignedFirstMonomialAggregate244 hFourier =
      weightedH3CanonicalSignedFirstMonomial244 U :=
    tendsto_nhds_unique hPhysical hSchwartz
  calc
    h3PathCanonicalFirstMonomialAggregateAt u t =
        h3CanonicalSignedFirstMonomialAggregate244 hFourier :=
      h3PathCanonicalFirstMonomialAggregate_eq_canonicalSecondL4Integral244 hFourier
    _ = weightedH3CanonicalSignedFirstMonomial244 U := hUnique

/-- The signed interpolation gap in the original physical/full-third error
identity is identically zero. Only the 3–3–1 gradient channel remains. -/
theorem h3PathCanonical_signedGap_eq_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    h3PathCanonicalFirstMonomialAggregateAt u t -
        weightedH3CanonicalSignedFirstMonomial244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier) = 0 := by
  rw [h3PathCanonicalFirstMonomialAggregate_eq_weightedCanonicalSigned244 hFourier]
  ring

end
end PrimeTensor.FirstMonomialTriad
