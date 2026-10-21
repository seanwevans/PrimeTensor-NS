import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientIntegrability244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalStrongTrace244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzWeightedReferenceIndependence244
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic

/-!
# Physical 3–3–1 gradient: natural L²–L²–L∞ strong trace

The signed 3–2–2 channel has already been identified with its canonical
Schwartz limit. For the outstanding gradient 3–3–1 channel, the same matched
Schwartz family has two strong third-jet L² limits and a uniform first-jet
error gauge. This file puts these three facts into the correct Banach spaces.

* `h3PhysicalGradientLpTriple244` is the genuine L²×L²×L∞ trilinear
  integral, expressed as two continuous bilinear Hölder maps.
* An a.e. pointwise bound implies the precise L∞-norm bound on an Lp class.
* A vanishing uniform first-jet error therefore gives strong L∞ convergence
  to the actual physical first derivative.
* The matched Schwartz third derivatives converge strongly in the *actual*
  Fourier-carrier L² classes, not to new arbitrary representatives.
* All three limits enter the same trilinear integral, slot by slot.

This module deliberately stops at the Euclidean-carrier Lp slot identity.
Its next consumer must match that Lp target with the original Point3
`spatialEnergyPairing`, split its four gradient orientations, and take
all five finite index sums. No physical gradient equality is postulated here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeGradientLinfTrace244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local instance gradientLinfFact2244 : Fact (1 ≤ (2 : ENNReal)) :=
  ⟨by norm_num⟩
local instance gradientLinfFactTop244 : Fact (1 ≤ (∞ : ENNReal)) :=
  ⟨by simp⟩

private abbrev L2GradientTrace244 : Type := H3FourierRealL2
private abbrev LinfGradientTrace244 : Type :=
  MeasureTheory.Lp ℝ (∞ : ENNReal) (volume : Measure V3)

local instance gradientHolderTopTwoTwo244 : ENNReal.HolderTriple ∞ 2 2 := by
  refine ⟨?_⟩
  simp

/-- Two actual L² factors and a bounded first-jet L∞ factor, with the
physical 3–3–1 factor ordering retained inside the integral. -/
noncomputable def h3PhysicalGradientLpTriple244
    (A B : L2GradientTrace244) (C : LinfGradientTrace244) : ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing
    (volume : Measure V3) (2 : ENNReal) (2 : ENNReal) A
    ((ContinuousLinearMap.mul ℝ ℝ).holderL
      (volume : Measure V3) (∞ : ENNReal) (2 : ENNReal)
      (2 : ENNReal) C B)

/-- The continuous Banach-space pairing is the *literal signed integral*;
it does not take absolute values or change the orientation of the product. -/
theorem h3PhysicalGradientLpTriple_eq_integral244
    (A B : L2GradientTrace244) (C : LinfGradientTrace244) :
    h3PhysicalGradientLpTriple244 A B C =
      ∫ x : V3, A x * (B x * C x) := by
  unfold h3PhysicalGradientLpTriple244
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  have hBC :=
    (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := (2 : ENNReal)) C B
  apply integral_congr_ae
  filter_upwards [hBC] with x hx
  change A x * ((ContinuousLinearMap.mul ℝ ℝ).holder (2 : ENNReal) C B) x =
    A x * (B x * C x)
  rw [hx]
  -- The Holder representative is still expressed through the bounded
  -- bilinear multiplication map; its application must be rewritten, not
  -- changed by definitional equality.
  simp only [ContinuousLinearMap.mul_apply']
  ring

/-- All three exponents converge in their natural normed topologies.
The two bilinear operators are abstract parameters in the expensive
continuity step, preventing `isDefEq` unfolding the Hölder construction. -/
private theorem h3GradientBilinear_tendsto244
    (M : LinfGradientTrace244 →L[ℝ] L2GradientTrace244 →L[ℝ] L2GradientTrace244)
    (P : L2GradientTrace244 →L[ℝ] L2GradientTrace244 →L[ℝ] ℝ)
    (A B : ℕ → L2GradientTrace244)
    (C : ℕ → LinfGradientTrace244)
    (a b : L2GradientTrace244) (c : LinfGradientTrace244)
    (hA : Tendsto A atTop (𝓝 a))
    (hB : Tendsto B atTop (𝓝 b))
    (hC : Tendsto C atTop (𝓝 c)) :
    Tendsto (fun n => P (A n) (M (C n) (B n)))
      atTop (𝓝 (P a (M c b))) := by
  have hCB : Tendsto (fun n : ℕ => (C n, B n))
      atTop (𝓝 (c, b)) := hC.prodMk_nhds hB
  have hM : Continuous (fun z : LinfGradientTrace244 × L2GradientTrace244 =>
      M z.1 z.2) := M.continuous₂
  have hProduct : Tendsto (fun n => M (C n) (B n))
      atTop (𝓝 (M c b)) := (hM.tendsto (c, b)).comp hCB
  have hAP : Tendsto (fun n : ℕ => (A n, M (C n) (B n)))
      atTop (𝓝 (a, M c b)) := hA.prodMk_nhds hProduct
  have hP : Continuous (fun z : L2GradientTrace244 × L2GradientTrace244 =>
      P z.1 z.2) := P.continuous₂
  exact (hP.tendsto (a, M c b)).comp hAP

/-- Strong L² and L∞ convergence imply convergence of the fully signed
three-factor gradient integral, with no dominating L⁴ third jet. -/
theorem h3PhysicalGradientLpTriple_tendsto244
    (A B : ℕ → L2GradientTrace244)
    (C : ℕ → LinfGradientTrace244)
    (a b : L2GradientTrace244) (c : LinfGradientTrace244)
    (hA : Tendsto A atTop (𝓝 a))
    (hB : Tendsto B atTop (𝓝 b))
    (hC : Tendsto C atTop (𝓝 c)) :
    Tendsto (fun n => h3PhysicalGradientLpTriple244 (A n) (B n) (C n))
      atTop (𝓝 (h3PhysicalGradientLpTriple244 a b c)) := by
  let M : LinfGradientTrace244 →L[ℝ] L2GradientTrace244 →L[ℝ]
      L2GradientTrace244 :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL
      (volume : Measure V3) (∞ : ENNReal) (2 : ENNReal) (2 : ENNReal)
  let P : L2GradientTrace244 →L[ℝ] L2GradientTrace244 →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing
      (volume : Measure V3) (2 : ENNReal) (2 : ENNReal)
  have hCore := h3GradientBilinear_tendsto244 M P A B C a b c hA hB hC
  change Tendsto (fun n => P (A n) (M (C n) (B n)))
    atTop (𝓝 (P a (M c b)))
  exact hCore

/-- Uniform a.e. bounds pass with the *same constant* to the normed
L∞ equivalence class; in particular no finite-volume assumption is needed. -/
theorem h3GradientLinf_norm_le_bound244
    {f : V3 → ℝ}
    (hf : MemLp f (∞ : ENNReal) (volume : Measure V3))
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ᵐ x ∂(volume : Measure V3), ‖f x‖ ≤ K) :
    ‖hf.toLp f‖ ≤ K := by
  rw [Lp.norm_toLp]
  rw [eLpNorm_exponent_top]
  calc
    (eLpNormEssSup f (volume : Measure V3)).toReal ≤
        (ENNReal.ofReal K).toReal :=
      ENNReal.toReal_mono (by simp)
        (eLpNormEssSup_le_of_ae_bound hBound)
    _ = K := ENNReal.toReal_ofReal hK

/-- A vanishing *pointwise uniform* gauge upgrades a sequence of L∞
classes to strong L∞ convergence. The proof uses the norm of the
actual difference class, not an illegitimate finite-measure embedding. -/
theorem h3GradientUniformLinf_tendsto244
    (f : ℕ → V3 → ℝ) (g : V3 → ℝ)
    (hf : ∀ n, MemLp (f n) (∞ : ENNReal) (volume : Measure V3))
    (hg : MemLp g (∞ : ENNReal) (volume : Measure V3))
    (δ : ℕ → ℝ)
    (hδNonneg : ∀ n, 0 ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hBound : ∀ n x, |f n x - g x| ≤ δ n) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop
      (𝓝 (hg.toLp g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hNorm (n : ℕ) :
      ‖(hf n).toLp (f n) - hg.toLp g‖ ≤ δ n := by
    have hDiff : MemLp (f n - g) (∞ : ENNReal)
        (volume : Measure V3) := (hf n).sub hg
    have hPoint : ∀ᵐ x ∂(volume : Measure V3),
        ‖(f n - g) x‖ ≤ δ n := by
      filter_upwards with x
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using hBound n x
    have hDiffNorm : ‖hDiff.toLp (f n - g)‖ ≤ δ n :=
      h3GradientLinf_norm_le_bound244 hDiff (δ n) (hδNonneg n) hPoint
    -- The `toLp_sub` theorem has the subtraction on the RIGHT.
    -- Make this equality explicit rather than relying on simp direction.
    have hSub : ((hf n).sub hg).toLp (f n - g) =
        (hf n).toLp (f n) - hg.toLp g :=
      MemLp.toLp_sub (hf n) hg
    calc
      ‖(hf n).toLp (f n) - hg.toLp g‖ =
          ‖((hf n).sub hg).toLp (f n - g)‖ := by rw [hSub]
      _ = ‖hDiff.toLp (f n - g)‖ := rfl
      _ ≤ δ n := hDiffNorm
  have hAbs : Tendsto (fun n =>
      ‖(hf n).toLp (f n) - hg.toLp g‖) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact norm_nonneg _
    · exact hNorm
    · exact hδ
  exact hAbs

/-- The actual physical gradient pulled back to Fourier space has a
canonical L∞ class at every Fourier-compatible interior Navier–Stokes slice. -/
noncomputable def h3ActualPhysicalFirstJetLinf244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (q : Fin 3) (r : A3) : LinfGradientTrace244 := by
  have hOld : MemLp
      (spatial3.d r (loggedVelocityComponent u t (h3AxisOfFin3 q)))
      (∞ : ENNReal) (volume : Measure Point3) := by
    exact h3ActualPhysicalGradientFirstJet_memLp_top244 hNS ht hFourier
      (h3AxisOfFin3 q) r
  have hPull := hOld.comp_measurePreserving
    (PiLp.volume_preserving_ofLp A3)
  exact hPull.toLp
    (fun x : V3 => spatial3.d r
      (loggedVelocityComponent u t (h3AxisOfFin3 q)) (WithLp.ofLp x))

/-- The *literal* third derivatives of a matched real Schwartz completion
converge strongly in L² to the old physical third-order jet. -/
theorem h3MatchedSchwartz_physicalThirdL2_tendsto244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier))
    (q : Fin 3) (a b c : A3) :
    Tendsto (fun n =>
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c}
            (F.family.approximants n (h3AxisOfFin3 q))))).toLp
              2 (volume : Measure V3)) atTop
      (𝓝 (h3ActualThirdJetOnFourierCarrier244 hInt hMeas q a b c)) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  have hThirdState : Tendsto
      (fun n => matchedSpectralThirdFourierJets244 (F.spectral n))
      atTop (𝓝 (matchedSpectralThirdFourierJets244 U)) :=
    continuous_matchedSpectralThirdFourierJets244.continuousAt.tendsto.comp
      F.spectral_tendsto
  -- `matchedSpectralThirdFourierJets244` is indexed by physical axes,
  -- whereas the actual third-jet wrapper uses `Fin 3` components.
  have hCoord := (tendsto_pi_nhds.mp hThirdState)
    (h3AxisOfFin3 q, (a, (b, c)))
  have hSeq : (fun n =>
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c}
            (F.family.approximants n (h3AxisOfFin3 q))))).toLp
              2 (volume : Measure V3)) =
      (fun n => matchedSpectralThirdFourierJets244 (F.spectral n)
        (h3AxisOfFin3 q, (a, (b, c)))) := by
    funext n
    exact F.third_exact n (h3AxisOfFin3 q) a b c
  have hTarget : matchedSpectralThirdFourierJets244 U
      (h3AxisOfFin3 q, (a, (b, c))) =
      h3ActualThirdJetOnFourierCarrier244 hInt hMeas q a b c := by
    change h3ToFourierRealL2
      (h3SpectralVelocityThirdPhysicalJetFamily244 U
        (h3ClassicalizationFinOfAxis (h3AxisOfFin3 q)) a b c) =
      h3ToFourierRealL2
        (velocityH3L2JetAt u t hInt hMeas
          (h3JetSlot3 q (h3ClassicalizationFinOfAxis a)
            (h3ClassicalizationFinOfAxis b)
            (h3ClassicalizationFinOfAxis c)))
    simp only [h3ClassicalizationFinOfAxis_h3AxisOfFin3]
    dsimp only [U]
    rw [h3SpectralVelocityThirdPhysicalJetFamily_actualJet244 hFourier]
  rw [hSeq, ← hTarget]
  exact hCoord

/-- The old physical first derivative is the strong L∞ limit of the
FIRST derivatives of the *same* matched Schwartz sequence, using only the
previously proved spatially uniform spectral H³ error gauge. -/
theorem h3MatchedSchwartz_physicalFirstLinf_tendsto244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier))
    (q : Fin 3) (r : A3) :
    Tendsto (fun n =>
      (∂_{h3FourierAxisDirection r}
        (F.family.approximants n (h3AxisOfFin3 q))).toLp
          (∞ : ENNReal) (volume : Measure V3)) atTop
      (𝓝 (h3ActualPhysicalFirstJetLinf244 hNS ht hFourier q r)) := by
  let D : ℕ → SchwartzMap V3 ℝ := fun n =>
    ∂_{h3FourierAxisDirection r}
      (F.family.approximants n (h3AxisOfFin3 q))
  let g : V3 → ℝ := fun x =>
    spatial3.d r (loggedVelocityComponent u t (h3AxisOfFin3 q))
      (WithLp.ofLp x)
  have hD (n : ℕ) : MemLp (D n : V3 → ℝ)
      (∞ : ENNReal) (volume : Measure V3) := (D n).memLp_top _
  have hOld : MemLp
      (spatial3.d r (loggedVelocityComponent u t (h3AxisOfFin3 q)))
      (∞ : ENNReal) (volume : Measure Point3) :=
    h3ActualPhysicalGradientFirstJet_memLp_top244 hNS ht hFourier
      (h3AxisOfFin3 q) r
  have hg : MemLp g (∞ : ENNReal) (volume : Measure V3) :=
    hOld.comp_measurePreserving (PiLp.volume_preserving_ofLp A3)
  obtain ⟨hδ, hGauge⟩ :=
    h3MatchedSchwartz_physicalFirstJetGauge244 hNS ht hFourier F
  let δ : ℕ → ℝ := fun n =>
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      ‖F.spectral n q -
        velocityH3SpectralScalarAt u t hInt hMeas hFourier q‖
  have hδNonneg (n : ℕ) : 0 ≤ δ n :=
    mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (norm_nonneg _)
  have hδLimit : Tendsto δ atTop (𝓝 0) := hδ q
  have hBound (n : ℕ) (x : V3) :
      |(D n : V3 → ℝ) x - g x| ≤ δ n := by
    exact hGauge n q r x
  have hLim := h3GradientUniformLinf_tendsto244
    (fun n => (D n : V3 → ℝ)) g hD hg δ hδNonneg hδLimit hBound
  change Tendsto (fun n => (hD n).toLp (D n : V3 → ℝ))
    atTop (𝓝 (hg.toLp g)) at hLim
  -- Both L∞ targets use the same physical function; the proof that it is
  -- MemLp is proof-irrelevant, and the `toLp` construction is canonical.
  exact hLim

/-- Every ordered 3–3–1 Schwartz triple converges to the trilinear
functional of the actual old physical two third jets and first jet.
This is the analytic core needed for the four gradients per 243 slots. -/
theorem h3MatchedSchwartz_physicalGradientLpTriple_tendsto244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier))
    (j p q : Fin 3) (a b c d e f r : A3) :
    Tendsto (fun n => h3PhysicalGradientLpTriple244
      ((∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c}
            (F.family.approximants n (h3AxisOfFin3 j))))).toLp
              2 (volume : Measure V3))
      ((∂_{h3FourierAxisDirection d}
        (∂_{h3FourierAxisDirection e}
          (∂_{h3FourierAxisDirection f}
            (F.family.approximants n (h3AxisOfFin3 p))))).toLp
              2 (volume : Measure V3))
      ((∂_{h3FourierAxisDirection r}
        (F.family.approximants n (h3AxisOfFin3 q))).toLp
              (∞ : ENNReal) (volume : Measure V3))) atTop
      (𝓝 (h3PhysicalGradientLpTriple244
        (h3ActualThirdJetOnFourierCarrier244 hInt hMeas j a b c)
        (h3ActualThirdJetOnFourierCarrier244 hInt hMeas p d e f)
        (h3ActualPhysicalFirstJetLinf244 hNS ht hFourier q r))) := by
  exact h3PhysicalGradientLpTriple_tendsto244 _ _ _ _ _ _
    (h3MatchedSchwartz_physicalThirdL2_tendsto244 hFourier F j a b c)
    (h3MatchedSchwartz_physicalThirdL2_tendsto244 hFourier F p d e f)
    (h3MatchedSchwartz_physicalFirstLinf_tendsto244 hNS ht hFourier F q r)

end
end PrimeTensor.FirstMonomialTriad
