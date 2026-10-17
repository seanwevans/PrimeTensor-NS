import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzMatchedSecondDerivative244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzActualThirdJetIdentification244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.Cubic.Velocity.Physical.L2.Continuity

/-!
# Full 27+81 physical H³ Schwartz approximation jet family

The previous compact weighted-frequency theorem constructs matched actual real
Schwartz functions whose 27 quadratic and 81 cubic derivative L² classes are
exactly the spectral multiplier reconstructions. This module proves the missing
quantitative quadratic weighted-to-Fourier bound, its subtraction and continuity
properties, and identifies the quadratic reconstruction with the 27 original
physical second derivative H³ jet states at a compatible time slice.

It then selects ONE three-component compact-weighted approximation sequence and
ONE family of matched real Schwartz functions with simultaneous convergence of
all 27 real second-derivative L² classes, all 81 third-derivative L² classes,
and the zeroth order physical velocity. All derivative targets are literal old
physical H³ jets, not newly postulated representatives.

The next step is to use finite-sum norm continuity to prove actual E₂/E₃
Cauchy energies. Approximate solenoidality and the physical transport
identification remain separate.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology FourierTransform
open scoped BigOperators ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeMatchedSecondFamily244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact quadratic physical Fourier multiplier has operator norm at
most `(2π)²` from the native weighted H³ scalar state. -/
theorem norm_h3SpectralScalarRawSecondCoordinateFourierL2_le244
    (a b : A3) (G : H3SpectralScalarState) :
    ‖h3SpectralScalarRawSecondCoordinateFourierL2_244 a b G‖ ≤
      (2 * Real.pi) ^ 2 * ‖G‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [h3SpectralScalarRawSecondCoordinateFourierL2_ae244 a b G]
    with ξ hξ
  rw [hξ]
  have hInv0 : 0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact inv_nonneg.mpr (h3SobolevFrequencyWeight_pos ξ).le
  have ha := norm_h3FourierDerivativeSymbol_le_gradientMagnitude
    (h3ClassicalizationFinOfAxis a) ξ
  have hb := norm_h3FourierDerivativeSymbol_le_gradientMagnitude
    (h3ClassicalizationFinOfAxis b) ξ
  have hRadial :=
    h3FourierNorm_sq_mul_h3SobolevFrequencyWeightInv_le_one ξ
  unfold h3SpectralScalarRawFourier h3SobolevFrequencyWeightInvComplex
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hInv0]
  calc
    ‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis a) ξ‖ *
        (‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis b) ξ‖ *
          (h3SobolevFrequencyWeightInv ξ * ‖G ξ‖)) ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3SobolevFrequencyWeightInv ξ * ‖G ξ‖)) := by
        gcongr
        unfold h3FourierGradientMagnitude
        positivity
    _ = (2 * Real.pi) ^ 2 *
        ((‖ξ‖ ^ 2 * h3SobolevFrequencyWeightInv ξ) * ‖G ξ‖) := by
          unfold h3FourierGradientMagnitude
          ring
    _ ≤ (2 * Real.pi) ^ 2 * (1 * ‖G ξ‖) := by
          gcongr
    _ = (2 * Real.pi) ^ 2 * ‖G ξ‖ := by ring

/-- The bundled quadratic Fourier multiplier is additive under subtraction. -/
theorem h3SpectralScalarRawSecondCoordinateFourierL2_sub244
    (a b : A3) (G H : H3SpectralScalarState) :
    h3SpectralScalarRawSecondCoordinateFourierL2_244 a b (G - H) =
      h3SpectralScalarRawSecondCoordinateFourierL2_244 a b G -
      h3SpectralScalarRawSecondCoordinateFourierL2_244 a b H := by
  apply MeasureTheory.Lp.ext
  have hGH := h3SpectralScalarRawSecondCoordinateFourierL2_ae244 a b (G - H)
  have hG := h3SpectralScalarRawSecondCoordinateFourierL2_ae244 a b G
  have hH := h3SpectralScalarRawSecondCoordinateFourierL2_ae244 a b H
  have hRaw := h3SpectralScalarRawFourier_sub_ae G H
  have hOut := MeasureTheory.Lp.coeFn_sub
    (h3SpectralScalarRawSecondCoordinateFourierL2_244 a b G)
    (h3SpectralScalarRawSecondCoordinateFourierL2_244 a b H)
  filter_upwards [hGH, hG, hH, hRaw, hOut] with
    ξ hGHξ hGξ hHξ hRawξ hOutξ
  rw [hGHξ, hOutξ]
  simp only [Pi.sub_apply]
  rw [hGξ, hHξ, hRawξ]
  ring

/-- Lipschitz control of quadratic multiplier differences. -/
theorem norm_h3SpectralScalarRawSecondCoordinateFourierL2_sub_le244
    (a b : A3) (G H : H3SpectralScalarState) :
    ‖h3SpectralScalarRawSecondCoordinateFourierL2_244 a b G -
      h3SpectralScalarRawSecondCoordinateFourierL2_244 a b H‖ ≤
      (2 * Real.pi) ^ 2 * ‖G - H‖ := by
  rw [← h3SpectralScalarRawSecondCoordinateFourierL2_sub244]
  exact norm_h3SpectralScalarRawSecondCoordinateFourierL2_le244
    a b (G - H)

/-- Strong continuity of the full quadratic spectral coordinate map. -/
theorem continuous_h3SpectralScalarRawSecondCoordinateFourierL2_244
    (a b : A3) :
    Continuous (h3SpectralScalarRawSecondCoordinateFourierL2_244 a b) := by
  rw [continuous_iff_continuousAt]
  intro G
  unfold ContinuousAt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero
  · intro H
    exact norm_nonneg _
  · intro H
    exact norm_h3SpectralScalarRawSecondCoordinateFourierL2_sub_le244 a b H G
  · have hBound :
        ContinuousAt
          (fun H : H3SpectralScalarState =>
            (2 * Real.pi) ^ 2 * ‖H - G‖) G := by
        fun_prop
    simpa using hBound.tendsto

/-- Plancherel and real-part projection transport quadratic continuity to
real physical L² on the native `Point3` carrier. -/
theorem continuous_h3SpectralScalarRawSecondCoordinatePhysicalL2_244
    (a b : A3) :
    Continuous (h3SpectralScalarRawSecondCoordinatePhysicalL2_244 a b) := by
  unfold h3SpectralScalarRawSecondCoordinatePhysicalL2_244
  exact continuous_h3FromFourierRealL2.comp
    (continuous_h3RealPartFourierL2.comp
      ((MeasureTheory.Lp.fourierTransformₗᵢ V3 ℂ).symm.continuous.comp
        (continuous_h3SpectralScalarRawSecondCoordinateFourierL2_244 a b)))

/-- All 27 ordered second-jet physical L² coordinates in one finite product. -/
noncomputable def h3SpectralVelocitySecondPhysicalJetFamily244
    (U : H3SpectralVelocityState) :
    Fin 3 → A3 → A3 → H3ScalarL2 :=
  fun j a b => h3SpectralScalarRawSecondCoordinatePhysicalL2_244 a b (U j)

/-- The full quadratic physical jet family varies continuously with the
weighted spectral H³ velocity, not merely along a particular mild path. -/
theorem continuous_h3SpectralVelocitySecondPhysicalJetFamily244 :
    Continuous h3SpectralVelocitySecondPhysicalJetFamily244 := by
  unfold h3SpectralVelocitySecondPhysicalJetFamily244
  apply continuous_pi
  intro j
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  exact (continuous_h3SpectralScalarRawSecondCoordinatePhysicalL2_244 a b).comp
    (continuous_apply j)

/-- Strong weighted H³ convergence transports simultaneously to all 27
quadratic physical L² jet states. -/
theorem h3SpectralVelocitySecondPhysicalJetFamily_tendsto_of_weighted244
    {F : ℕ → H3SpectralVelocityState} {U : H3SpectralVelocityState}
    (hF : Tendsto F atTop (𝓝 U)) :
    Tendsto (fun n => h3SpectralVelocitySecondPhysicalJetFamily244 (F n))
      atTop (𝓝 (h3SpectralVelocitySecondPhysicalJetFamily244 U)) := by
  exact continuous_h3SpectralVelocitySecondPhysicalJetFamily244.continuousAt.tendsto.comp hF

/-- At a genuine Fourier-compatible physical H³ snapshot, the quadratic
spectral Fourier multiplier is exactly the original second derivative slot. -/
theorem h3SpectralScalarRawSecondCoordinateFourierL2_actualJet244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) (a b : A3) :
    h3SpectralScalarRawSecondCoordinateFourierL2_244 a b
      (velocityH3SpectralScalarAt u t hInt hMeas hFourier j) =
    velocityH3FourierJetAt u t hInt hMeas
      (h3JetSlot2 j (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)) := by
  let G : H3SpectralScalarState :=
    velocityH3SpectralScalarAt u t hInt hMeas hFourier j
  have hRaw :
      h3SpectralScalarRawFourier G =ᵐ[volume]
        (velocityH3BaseFourierAt u t hInt hMeas j : V3 → ℂ) := by
    have h := h3SpectralScalarRawFourierL2_ae G
    change (h3SpectralScalarRawFourierL2
      (velocityH3SpectralScalarAt u t hInt hMeas hFourier j) :
        V3 → ℂ) =ᵐ[volume] h3SpectralScalarRawFourier G at h
    rw [h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
      hFourier j] at h
    exact h.symm
  have hQuadratic :=
    h3SpectralScalarRawSecondCoordinateFourierL2_ae244 a b G
  have hActual :=
    velocityH3FourierCompatibleAt_orderTwo hFourier j
      (h3ClassicalizationFinOfAxis a)
      (h3ClassicalizationFinOfAxis b)
  change h3SpectralScalarRawSecondCoordinateFourierL2_244 a b G = _
  apply MeasureTheory.Lp.ext
  filter_upwards [hQuadratic, hRaw, hActual] with
    ξ hQuadraticξ hRawξ hActualξ
  rw [hQuadraticξ, hActualξ, hRawξ]
  simp only [h3FourierDerivativeSymbol2]
  ring

/-- The quadratic physical reconstruction is the EXACT second-order real
physical velocity L² jet already used in the original H³ energy. -/
theorem h3SpectralScalarRawSecondCoordinatePhysicalL2_actualJet244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) (a b : A3) :
    h3SpectralScalarRawSecondCoordinatePhysicalL2_244 a b
      (velocityH3SpectralScalarAt u t hInt hMeas hFourier j) =
    velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot2 j (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)) := by
  unfold h3SpectralScalarRawSecondCoordinatePhysicalL2_244
  rw [h3SpectralScalarRawSecondCoordinateFourierL2_actualJet244
    hFourier j a b]
  rw [velocityH3FourierJetAt_apply]
  unfold h3ScalarFourierL2
  rw [(MeasureTheory.Lp.fourierTransformₗᵢ V3 ℂ).symm_apply_apply]
  rw [h3RealPartFourierL2_complexify_eq]
  exact h3FromFourierRealL2_h3ToFourierRealL2 _

/-- Entire 27-coordinate quadratic reconstruction equals the actual old
second-order physical H³ jet family. -/
theorem h3SpectralVelocitySecondPhysicalJetFamily_actualJet244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    h3SpectralVelocitySecondPhysicalJetFamily244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier) =
    (fun j : Fin 3 => fun a b : A3 =>
      velocityH3L2JetAt u t hInt hMeas
        (h3JetSlot2 j (h3ClassicalizationFinOfAxis a)
          (h3ClassicalizationFinOfAxis b))) := by
  funext j a b
  exact h3SpectralScalarRawSecondCoordinatePhysicalL2_actualJet244
    hFourier j a b

/-- ONE sequence of real physical Schwartz fields whose zeroth L² and
literal second and third derivative L² fields agree exactly with the matching
weighted spectral reconstructions; all 27+81 derivative families converge. -/
theorem exists_h3SmoothCompactWeighted_realSchwartzAllSecondThirdSequence244
    (U : H3SpectralVelocityState) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      Tendsto V atTop (𝓝 U) ∧
      (∀ n j,
        h3SpectralVelocityDecodeRealL2 (V n) j =
          (Ψ n j).toLp 2 (volume : Measure V3)) ∧
      (∀ n j a b,
        h3SpectralVelocitySecondPhysicalJetFamily244 (V n) j a b =
          h3FromFourierRealL2
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection b} (Ψ n j))).toLp
                2 (volume : Measure V3))) ∧
      (∀ n j a b c,
        h3SpectralVelocityThirdPhysicalJetFamily244 (V n) j a b c =
          h3FromFourierRealL2
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection b}
                (∂_{h3FourierAxisDirection c} (Ψ n j)))).toLp
                  2 (volume : Measure V3))) ∧
      Tendsto (fun n => h3SpectralVelocitySecondPhysicalJetFamily244 (V n))
        atTop (𝓝 (h3SpectralVelocitySecondPhysicalJetFamily244 U)) ∧
      Tendsto (fun n => h3SpectralVelocityThirdPhysicalJetFamily244 (V n))
        atTop (𝓝 (h3SpectralVelocityThirdPhysicalJetFamily244 U)) := by
  classical
  have hRadiusPos (n : ℕ) : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  have hApprox (n : ℕ) (j : Fin 3) :
      ∃ F : H3SpectralScalarState,
      ∃ ψ : SchwartzMap V3 ℝ,
        ‖U j - F‖ < (1 : ℝ) / ((n : ℝ) + 1) ∧
        h3SpectralScalarDecodeRealL2 F =
          ψ.toLp 2 (volume : Measure V3) ∧
        (∀ a b : A3,
          h3SpectralScalarRawSecondCoordinatePhysicalL2_244 a b F =
            h3FromFourierRealL2
              ((∂_{h3FourierAxisDirection a}
                (∂_{h3FourierAxisDirection b} ψ)).toLp
                  2 (volume : Measure V3))) ∧
        (∀ a b c : A3,
          h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c F =
            h3FromFourierRealL2
              ((∂_{h3FourierAxisDirection a}
                (∂_{h3FourierAxisDirection b}
                  (∂_{h3FourierAxisDirection c} ψ))).toLp
                    2 (volume : Measure V3))) :=
    exists_h3SmoothCompactWeighted_realSchwartzExactSecondThird244
      (U j) (hRadiusPos n)
  choose F Ψ hF hZero hSecond hThird using hApprox
  let V : ℕ → H3SpectralVelocityState := fun n j => F n j
  have hRadiusTendsto :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hWeighted : Tendsto V atTop (𝓝 U) := by
    rw [tendsto_pi_nhds]
    intro j
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hRadiusTendsto) ε hε
    refine ⟨N, ?_⟩
    intro n hn
    have hSmall : (1 : ℝ) / ((n : ℝ) + 1) < ε := by
      have h := hN n hn
      simpa only [Real.dist_eq, sub_zero,
        abs_of_pos (hRadiusPos n)] using h
    calc
      dist (V n j) (U j) = dist (U j) (V n j) := dist_comm _ _
      _ = ‖U j - F n j‖ := by simp only [V, dist_eq_norm]
      _ < (1 : ℝ) / ((n : ℝ) + 1) := hF n j
      _ < ε := hSmall
  have hExactZero (n : ℕ) (j : Fin 3) :
      h3SpectralVelocityDecodeRealL2 (V n) j =
        (Ψ n j).toLp 2 (volume : Measure V3) := by
    change h3SpectralScalarDecodeRealL2 (F n j) = _
    exact hZero n j
  have hExactSecond (n : ℕ) (j : Fin 3) (a b : A3) :
      h3SpectralVelocitySecondPhysicalJetFamily244 (V n) j a b =
        h3FromFourierRealL2
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b} (Ψ n j))).toLp
              2 (volume : Measure V3)) := by
    change h3SpectralScalarRawSecondCoordinatePhysicalL2_244 a b (F n j) = _
    exact hSecond n j a b
  have hExactThird (n : ℕ) (j : Fin 3) (a b c : A3) :
      h3SpectralVelocityThirdPhysicalJetFamily244 (V n) j a b c =
        h3FromFourierRealL2
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b}
              (∂_{h3FourierAxisDirection c} (Ψ n j)))).toLp
                2 (volume : Measure V3)) := by
    change h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c (F n j) = _
    exact hThird n j a b c
  exact ⟨V, Ψ, hWeighted, hExactZero, hExactSecond, hExactThird,
    h3SpectralVelocitySecondPhysicalJetFamily_tendsto_of_weighted244 hWeighted,
    h3SpectralVelocityThirdPhysicalJetFamily_tendsto_of_weighted244 hWeighted⟩

/-- The synchronized Schwartz sequence converges in every second and third
literal derivative to the corresponding ACTUAL H³ physical velocity jet. -/
theorem exists_h3SmoothCompactWeighted_actualSecondThirdJetSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      Tendsto V atTop (𝓝 (velocityH3SpectralStateAt u t hInt hMeas hFourier)) ∧
      (∀ n j a b,
        h3SpectralVelocitySecondPhysicalJetFamily244 (V n) j a b =
          h3FromFourierRealL2
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection b} (Ψ n j))).toLp
                2 (volume : Measure V3))) ∧
      (∀ n j a b c,
        h3SpectralVelocityThirdPhysicalJetFamily244 (V n) j a b c =
          h3FromFourierRealL2
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection b}
                (∂_{h3FourierAxisDirection c} (Ψ n j)))).toLp
                  2 (volume : Measure V3))) ∧
      Tendsto (fun n => h3SpectralVelocitySecondPhysicalJetFamily244 (V n))
        atTop (𝓝 (fun j : Fin 3 => fun a b : A3 =>
          velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot2 j (h3ClassicalizationFinOfAxis a)
              (h3ClassicalizationFinOfAxis b)))) ∧
      Tendsto (fun n => h3SpectralVelocityThirdPhysicalJetFamily244 (V n))
        atTop (𝓝 (fun j : Fin 3 => fun a b c : A3 =>
          velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot3 j (h3ClassicalizationFinOfAxis a)
              (h3ClassicalizationFinOfAxis b)
              (h3ClassicalizationFinOfAxis c)))) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  obtain ⟨V, Ψ, hWeighted, _, hSecondExact, hThirdExact,
    hSecond, hThird⟩ :=
    exists_h3SmoothCompactWeighted_realSchwartzAllSecondThirdSequence244 U
  have hSecondEq := h3SpectralVelocitySecondPhysicalJetFamily_actualJet244 hFourier
  have hThirdEq := h3SpectralVelocityThirdPhysicalJetFamily_actualJet244 hFourier
  refine ⟨V, Ψ, hWeighted, hSecondExact, hThirdExact, ?_, ?_⟩
  · rw [← hSecondEq]
    exact hSecond
  · rw [← hThirdEq]
    exact hThird

/-- All 27+81 literal real Schwartz derivative L² families in the matched
sequence are Cauchy, since both finite-product reconstructions converge.
This is the complete Hilbert-jet Cauchy statement; translation into the
integrated E₂/E₃ differences is the next finite-energy equivalence step. -/
theorem exists_h3SmoothCompactWeighted_realSchwartzSecondThirdL2Cauchy244
    (U : H3SpectralVelocityState) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      (∀ n j a b,
        h3SpectralVelocitySecondPhysicalJetFamily244 (V n) j a b =
          h3FromFourierRealL2
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection b} (Ψ n j))).toLp
                2 (volume : Measure V3))) ∧
      (∀ n j a b c,
        h3SpectralVelocityThirdPhysicalJetFamily244 (V n) j a b c =
          h3FromFourierRealL2
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection b}
                (∂_{h3FourierAxisDirection c} (Ψ n j)))).toLp
                  2 (volume : Measure V3))) ∧
      CauchySeq (fun n => h3SpectralVelocitySecondPhysicalJetFamily244 (V n)) ∧
      CauchySeq (fun n => h3SpectralVelocityThirdPhysicalJetFamily244 (V n)) := by
  obtain ⟨V, Ψ, _, _, hSecondExact, hThirdExact,
    hSecond, hThird⟩ :=
    exists_h3SmoothCompactWeighted_realSchwartzAllSecondThirdSequence244 U
  exact ⟨V, Ψ, hSecondExact, hThirdExact,
    hSecond.cauchySeq, hThird.cauchySeq⟩

end
end PrimeTensor.FirstMonomialTriad
