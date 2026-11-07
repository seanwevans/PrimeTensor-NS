import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticOffshellGapExcess
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalCompactTimeRadialTightness
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalGlobalHighMaxTail
import Mathlib.Tactic

/-!
# Compact-gap sixth-power flux: one low-maximum cutoff before the adverse time

The signed top third-order physical transport is represented by the genuine
real-solenoidal Schwartz sixth-power flux. Unlike fixed-time off-shell
persistence, one radius is chosen *uniformly over a complete strict-time
physical gap* before choosing the adverse physical snapshot. The Schwartz
recovery is still selected separately at each time; no time-measurable
selection or terminal-uniform cutoff is assumed.

The common radius comes from compactness of the actual continuous weighted
H3 spectral trajectory and the high-maximum trilinear bound
  |integral_high F6| <= 1944 C1 K |P_R V|^2.
Once that high-maximum integral is uniformly small, an adverse physical
third-order rate must persist in the complementary low-maximum signed flux.
The conclusion is quantitative at a prescribed positive margin and uses the
same gaps between the original kinetic natural-annulus windows.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology FourierTransform
open scoped BigOperators Interval ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private abbrev FluxAxisCompact244 := PrimeTensor.Axis Depth.three
private abbrev FluxPointCompact244 := H3FourierPoint3
private abbrev FluxPairCompact244 := FluxPointCompact244 × FluxPointCompact244

noncomputable local instance axisFintypeKineticCompactGap244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The *same* low-maximum cutoff works for all potentially adverse times
inside one physical time gap. Only the real-solenoidal Schwartz recovery
sequence varies with the snapshot. -/
def thirdFullKineticGapUniformLowMaxCarrier244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (η x y : ℝ) : Prop :=
  ∃ R : ℕ, ∀ s : ℝ, s ∈ Set.Icc x y →
    η < -velocityH3TransportDerivative3At u s →
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap FluxPointCompact244 ℝ,
      (∀ n : ℕ, ∀ z : FluxPointCompact244,
        ∑ j : FluxAxisCompact244,
          fderiv ℝ (h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))) z
            (h3FourierAxisDirection j) = 0) ∧
      Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : FluxPairCompact244,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j : FluxAxisCompact244 => h3SchwartzComplexify
              (Ψ n (h3ClassicalizationFinOfAxis j))) z
          ∂volume.prod volume).im)
        atTop (𝓝 (velocityH3TransportDerivative3At u s)) ∧
      (∀ᶠ n : ℕ in atTop,
        η / 2 < -(((2 * Real.pi) ^ 7 / 3) *
          (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j : FluxAxisCompact244 => h3SchwartzComplexify
                (Ψ n (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume).im))

/-- Strong compact-time spectral tightness plus solenoidal Fourier recovery
eliminates the need to postulate a jointly chosen time-Schwartz family.
One natural high-maximum cutoff works on the entire preterminal slab,
although the recovery convergence index can depend on the physical time. -/
theorem thirdFullPhysical_strictSlab_independentRecovery_highMaxUniform244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y : ℝ) (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x ≤ y) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ t : ℝ, t ∈ Set.Icc x y →
      ∃ Ψ : ℕ → Fin 3 → SchwartzMap FluxPointCompact244 ℝ,
        (∀ n : ℕ, ∀ z : FluxPointCompact244,
          ∑ j : FluxAxisCompact244,
            fderiv ℝ (h3SchwartzComplexify
              (Ψ n (h3ClassicalizationFinOfAxis j))) z
              (h3FourierAxisDirection j) = 0) ∧
        Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
          (∫ z : FluxPairCompact244,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j : FluxAxisCompact244 => h3SchwartzComplexify
                (Ψ n (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume).im)
          atTop (𝓝 (velocityH3TransportDerivative3At u t)) ∧
        (∀ᶠ n : ℕ in atTop,
          ‖∫ z in thirdFullHighMaxSet244 R,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j : FluxAxisCompact244 => h3SchwartzComplexify
                (Ψ n (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume‖ < ε) := by
  have hx0 : 0 < x := lt_trans hClass.terminal_start.1 hx.1
  have hSub : Set.Icc x y ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le hx0 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  have hCont : ContinuousOn
      (h3AuditActualSpectralVelocityTotal hH3) (Set.Icc x y) :=
    (h3Audit_initialActualSpectralVelocity_continuousOn hH3).mono hSub
  obtain ⟨K₀, hK₀⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc x y)).exists_bound_of_continuousOn hCont
  let K : ℝ := max K₀ 0 + 1
  have hK : 0 ≤ K := by
    dsimp only [K]
    linarith only [le_max_right K₀ 0]
  let B : ℝ := 1944 * h3SobolevFirstMomentDeweightingConstant * K
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity [h3SobolevFirstMomentDeweightingConstant_nonneg]
  let δ : ℝ := min 1 (ε / (1 + B))
  have hOneB : 0 < 1 + B := by linarith only [hB]
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min_iff.mpr ⟨by norm_num, div_pos hε hOneB⟩
  have hδone : δ ≤ 1 := min_le_left 1 (ε / (1 + B))
  have hδepsilon : B * δ < ε := by
    have hδle : δ ≤ ε / (1 + B) := min_le_right 1 (ε / (1 + B))
    calc
      B * δ ≤ B * (ε / (1 + B)) :=
        mul_le_mul_of_nonneg_left hδle hB
      _ < (1 + B) * (ε / (1 + B)) :=
        mul_lt_mul_of_pos_right (by linarith only [hB]) (div_pos hε hOneB)
      _ = ε := by
        rw [mul_comm (1 + B)]
        exact div_mul_cancel₀ ε hOneB.ne'
  obtain ⟨R, hR⟩ :=
    thirdFullPhysicalStrictSlab_uniformHighRadial244 hH3
      x y hx0 hxy hy.2 (δ / 2) (by positivity)
  refine ⟨R, ?_⟩
  intro t ht
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  have htNS : t ∈ Set.Ioo (0 : ℝ) T := hSub ht
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htNS
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS hInt
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  have hUEq : h3AuditActualSpectralVelocityTotal hH3 t = U := by
    rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t htNS]
    rfl
  have hUBound : ‖U‖ ≤ max K₀ 0 := by
    rw [← hUEq]
    exact (hK₀ t ht).trans (le_max_left K₀ 0)
  have hUTail :
      ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ < δ / 2 := by
    rw [← hUEq]
    exact hR t ht
  obtain ⟨V, Ψ, hV, hAE, hDiv, _hDefect, _hE₂, _hE₃, hFlux⟩ :=
    exists_thirdFullPhysicalSnapshot_solenoidalPureSixthPowerFlux244
      hH3.navier_stokes htNS hH3 hClass htClass hFourier
  have hDiff : Tendsto (fun n : ℕ => ‖V n - U‖)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hV
  have hNearNorm : ∀ᶠ n : ℕ in atTop, ‖V n - U‖ < 1 / 2 :=
    hDiff.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hNearTail : ∀ᶠ n : ℕ in atTop, ‖V n - U‖ < δ / 2 :=
    hDiff.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < δ / 2))
  refine ⟨Ψ, hDiv, hFlux, ?_⟩
  filter_upwards [hNearNorm, hNearTail] with n hnNorm hnTail
  have hVNorm : ‖V n‖ ≤ K := by
    have hTriangle : ‖V n‖ ≤ ‖V n - U‖ + ‖U‖ := by
      calc
        ‖V n‖ = ‖(V n - U) + U‖ := by rw [sub_add_cancel]
        _ ≤ ‖V n - U‖ + ‖U‖ := norm_add_le _ _
    dsimp only [K]
    linarith only [hTriangle, hnNorm, hUBound]
  have hVTail :
      ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ < δ := by
    calc
      ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ =
          ‖thirdFullSpectralVelocityHighRadialApply244 R ((V n - U) + U)‖ := by
            rw [sub_add_cancel]
      _ = ‖thirdFullSpectralVelocityHighRadialApply244 R (V n - U) +
          thirdFullSpectralVelocityHighRadialApply244 R U‖ := by
            rw [thirdFullSpectralVelocityHighRadialApply_add244]
      _ ≤ ‖thirdFullSpectralVelocityHighRadialApply244 R (V n - U)‖ +
          ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ := norm_add_le _ _
      _ ≤ ‖V n - U‖ +
          ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ := by
            exact add_le_add
              (thirdFullSpectralVelocityHighRadialApply_norm_le244 R (V n - U)) le_rfl
      _ < δ := by linarith only [hnTail, hUTail]
  have hOne :
      ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ ≤ 1 :=
    (le_of_lt hVTail).trans hδone
  have hSquare :
      ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ ^ 2 ≤ δ := by
    have hNonneg := norm_nonneg (thirdFullSpectralVelocityHighRadialApply244 R (V n))
    have hMul := mul_le_mul_of_nonneg_left hOne hNonneg
    have hAux :
        ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ ^ 2 ≤
          ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ := by
      nlinarith only [hMul]
    exact hAux.trans hVTail.le
  let v : FluxAxisCompact244 → SchwartzMap FluxPointCompact244 ℂ :=
    fun j => h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
  have hRep : ∀ j : FluxAxisCompact244,
      (V n (h3ClassicalizationFinOfAxis j) : FluxPointCompact244 → ℂ) =ᵐ[volume]
        (fun ξ : FluxPointCompact244 =>
          (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ) := by
    intro j
    exact hAE n (h3ClassicalizationFinOfAxis j)
  have hGlobal := thirdFullWeightedSchwartz_highMaxIntegral_le244
    v (hDiv n) (V n) hRep K hK hVNorm R
  change ‖∫ z in thirdFullHighMaxSet244 R,
      thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ < ε
  calc
    ‖∫ z in thirdFullHighMaxSet244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z
          ∂volume.prod volume‖ ≤
        B * ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ ^ 2 :=
      hGlobal
    _ ≤ B * δ := mul_le_mul_of_nonneg_left hSquare hB
    _ < ε := hδepsilon

/-- If the actual signed third-order H³ transport is adverse at ANY point
of a chosen strict-time gap, its real-solenoidal Schwartz recovery must
retain more than half that margin in the LOW-MAXIMUM complementary integral.
The cutoff R depends on the compact gap and η, but is chosen before s. -/
theorem thirdFullPhysical_strictGap_adverseThird_uniformLowMax244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y : ℝ) (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x < y) (η : ℝ) (hη : 0 < η) :
    thirdFullKineticGapUniformLowMaxCarrier244 u η x y := by
  let A : ℝ := (2 * Real.pi) ^ 7 / 3
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let ε : ℝ := η / (8 * (A + 1))
  have hDen : 0 < 8 * (A + 1) := by positivity
  have hε : 0 < ε := div_pos hη hDen
  have hAEps : A * ε ≤ η / 8 := by
    have hMul : (8 * (A + 1)) * ε = η := by
      dsimp only [ε]
      exact mul_div_cancel₀ η hDen.ne'
    have hAux : (A + 1) * ε = η / 8 := by
      nlinarith only [hMul]
    calc
      A * ε ≤ (A + 1) * ε :=
        mul_le_mul_of_nonneg_right (by linarith : A ≤ A + 1) hε.le
      _ = η / 8 := hAux
  obtain ⟨R, hR⟩ :=
    thirdFullPhysical_strictSlab_independentRecovery_highMaxUniform244
      hH3 hClass x y hx hy hxy.le ε hε
  unfold thirdFullKineticGapUniformLowMaxCarrier244
  refine ⟨R, ?_⟩
  intro s hs hAdverse
  obtain ⟨Ψ, hDiv, hFull, hHigh⟩ := hR s hs
  refine ⟨Ψ, hDiv, hFull, ?_⟩
  have hThreshold : velocityH3TransportDerivative3At u s < -(3 * η / 4) := by
    linarith only [hAdverse, hη]
  have hFullLate : ∀ᶠ n : ℕ in atTop,
      A * (∫ z : FluxPairCompact244,
        thirdFullSchwartzComplexSixthPowerFlux244
          (fun j : FluxAxisCompact244 => h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))) z
        ∂volume.prod volume).im < -(3 * η / 4) := by
    have hLate := hFull.eventually (Iio_mem_nhds hThreshold)
    simpa only [A] using hLate
  filter_upwards [hFullLate, hHigh] with n hnFull hnHigh
  let v : FluxAxisCompact244 → SchwartzMap FluxPointCompact244 ℂ :=
    fun j => h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
  let HI : ℂ := ∫ z in thirdFullHighMaxSet244 R,
    thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume
  let LO : ℂ := ∫ z in (thirdFullHighMaxSet244 R)ᶜ,
    thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume
  have hSplit := thirdFullSchwartzSixthPowerFlux_setSplit244
    v (hDiv n) (thirdFullHighMaxSet244 R)
      (thirdFullHighMaxSet_measurable244 R)
  have hImEq :
      A * (∫ z : FluxPairCompact244,
        thirdFullSchwartzComplexSixthPowerFlux244 v z
          ∂volume.prod volume).im = A * HI.im + A * LO.im := by
    rw [hSplit, Complex.add_im]
    dsimp only [HI, LO]
    ring
  have hImag : |HI.im| ≤ ‖HI‖ := Complex.abs_im_le_norm _
  have hHighSmall : ‖HI‖ < ε := by
    simpa only [HI, v] using hnHigh
  have hHighAbs : |A * HI.im| ≤ η / 8 := by
    calc
      |A * HI.im| = A * |HI.im| := by
        rw [abs_mul, abs_of_nonneg hA]
      _ ≤ A * ‖HI‖ := mul_le_mul_of_nonneg_left hImag hA
      _ ≤ A * ε := mul_le_mul_of_nonneg_left hHighSmall.le hA
      _ ≤ η / 8 := hAEps
  have hHighLower : -(η / 8) ≤ A * HI.im := by
    have hNeg : -|A * HI.im| ≤ A * HI.im := neg_abs_le _
    linarith only [hNeg, hHighAbs]
  change η / 2 < -(A * LO.im)
  change A * (∫ z : FluxPairCompact244,
    thirdFullSchwartzComplexSixthPowerFlux244 v z
      ∂volume.prod volume).im < -(3 * η / 4) at hnFull
  linarith only [hImEq, hnFull, hHighLower, hη]

/-- The kinetic cumulative three-way obstruction now carries an independently
selected LOW-MAXIMUM Fourier radius on the offending original gap, *before*
selecting its adverse time. The remaining two branches are unchanged. -/
theorem thirdFullPhysical_kineticCumulativeMarginOrGapLowMax244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hSeparated : ∀ k l : ℕ, k < l →
      τ (v k) + δ (v k) < τ (v l))
    (hWindows : ∀ k : ℕ,
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)))
    (η : ℝ) (hη : 0 < η) :
    ∀ m : ℕ,
      (∃ k : ℕ, k ≤ m ∧
        ∃ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) ∧
          M (v k) / 4 < h3PathSqrtEnergyRiccatiCoefficient *
            Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
      ((∑ k ∈ Finset.range (m + 1), δ (v k) * (M (v k) / 4)) + 1 ≤
        velocityH3EnergyAt u (τ (v 0)) +
        ∑ k ∈ Finset.range m,
          thirdFullKineticGapLowOrderMargin244 u η
            (τ (v k) + δ (v k)) (τ (v (k + 1)))) ∨
      (∃ k : ℕ, k < m ∧
        thirdFullKineticGapUniformLowMaxCarrier244 u η
          (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
        ∃ s : ℝ, s ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
          η < -velocityH3TransportDerivative3At u s ∧
          η < ((2 * Real.pi) ^ 7 / 3) *
            (1944 * h3SobolevFirstMomentDeweightingConstant *
              (velocityH3EnergyAt u s + 1) ^ 3)) := by
  have hPrevious := thirdFullPhysical_kineticCumulativeMarginOrAdverseThird244
    hH3 hClass b hb M τ N δ v hSeparated hWindows η hη
  intro m
  rcases hPrevious m with hRiccati | hRest
  · exact Or.inl hRiccati
  rcases hRest with hLower | ⟨k, hk, s, hs, hAdverse, hAmplitude⟩
  · exact Or.inr (Or.inl hLower)
  have hStart : τ (v k) + δ (v k) ∈ Set.Ioo a T := by
    obtain ⟨ht, hw⟩ := hWindows k
    rcases hw with ⟨_, hδ, _, hEnd, _, _⟩
    exact ⟨by linarith only [hb.1, ht.1, hδ], hEnd⟩
  have hFinish : τ (v (k + 1)) ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hWindows (k + 1)).1.1,
      (hWindows (k + 1)).1.2⟩
  have hCarrier := thirdFullPhysical_strictGap_adverseThird_uniformLowMax244
    hH3 hClass _ _ hStart hFinish
      (hSeparated k (k + 1) (Nat.lt_succ_self k)) η hη
  exact Or.inr (Or.inr ⟨k, hk, hCarrier, s, hs, hAdverse, hAmplitude⟩)

/-- No strong terminal H³ trace: on the SAME kinetic-selected cofinal windows,
each original inter-window gap has its OWN low-maximum Fourier carrier radius
uniform over the entire compact gap. This upgrades fixed-time off-shell
persistence without asserting an unjustified terminal-uniform radius. -/
theorem thirdFullPhysical_noH3Trace_kineticCompactGapLowMaxCarriers244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ, k ≤ v k ∧ τ (v k) ∈ Set.Ioo b T ∧
        ThirdFullKineticNaturalAnnularLocalWitness244
          hH3 b (τ (v k)) (v k) (N (v k))
          (M (v k)) (δ (v k))) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k) / 4) *
            ENNReal.ofReal (δ (v k))) ≤
        ∫⁻ r in Set.Ioo a T,
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in τ (v k)..(τ (v k) + δ (v k)),
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          h3PathActualBandRawKineticMass244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) < ε) ∧
      (∀ η : ℝ, 0 < η → ∀ k : ℕ,
        thirdFullKineticGapUniformLowMaxCarrier244 u η
          (τ (v k) + δ (v k)) (τ (v (k + 1)))) := by
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform, _hAlternatives⟩ :=
    thirdFullPhysical_noH3Trace_kineticOffshellGapObstruction244
      hH3 hClass b hb hNoTrace hDInt M hM
  refine ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform, ?_⟩
  intro η hη k
  have hStart : τ (v k) + δ (v k) ∈ Set.Ioo a T := by
    have ht : τ (v k) ∈ Set.Ioo b T := (hTimes k).2.1
    have hw := (hTimes k).2.2
    rcases hw with ⟨_, hδ, _, hEnd, _, _⟩
    exact ⟨by linarith only [hb.1, ht.1, hδ], hEnd⟩
  have hFinish : τ (v (k + 1)) ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hTimes (k + 1)).2.1.1,
      (hTimes (k + 1)).2.1.2⟩
  exact thirdFullPhysical_strictGap_adverseThird_uniformLowMax244
    hH3 hClass _ _ hStart hFinish
    (hSeparated k (k + 1) (Nat.lt_succ_self k)) η hη

end
end PrimeTensor.FirstMonomialTriad
