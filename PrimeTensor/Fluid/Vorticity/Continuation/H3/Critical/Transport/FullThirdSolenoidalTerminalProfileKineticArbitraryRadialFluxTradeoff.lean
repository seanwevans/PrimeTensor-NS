import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticCompactGapLowMaxFlux
import Mathlib.Tactic

/-!
# Arbitrary-radius signed sixth-power flux / weighted H3 tail tradeoff

On a physical kinetic gap, a common low-maximum cutoff exists, but its
radius is not controlled as the gaps approach the terminal time. Here the
cutoff is *arbitrary*. At any genuinely adverse top-order physical snapshot,
the exact solenoidal sixth-power Fourier integral forces either an adverse
signed flux BELOW the chosen radius or a quantitative weighted-H3 spectral
tail ABOVE that radius.

The scalar tradeoff uses the genuine high-max trilinear bound

  ‖∫_{HighMax(R)} F6‖ ≤ 1944 C1 K ‖P_R V‖²

on the existing exactly solenoidal strong-H3 Schwartz recovery. Its error is
an arbitrary positive γ, not an assumed physical H3 endpoint limit. The
result remains valid for each original kinetic PDE gap and retains the same
annular times and cofinal subsequence. No terminal-uniform cutoff, terminal
H3 bound, or a sign for the complex Fourier integrand is assumed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology FourierTransform
open scoped BigOperators Interval ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private abbrev RadialAxis244 := PrimeTensor.Axis Depth.three
private abbrev RadialPoint244 := H3FourierPoint3
private abbrev RadialPair244 := RadialPoint244 × RadialPoint244

noncomputable local instance axisFintypeKineticArbitraryRadius244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At every adverse physical snapshot, the signed low-maximum Fourier flux
plus an EXPLICIT quadratic weighted-H3 high-radial tail pays the adverse
margin. The cutoff R is arbitrary and is selected before the recovery.
The small approximation tolerance γ may be chosen independently of R. -/
theorem thirdFullPhysical_adverseThird_arbitraryRadiusFluxTailBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R : ℕ) (η γ : ℝ) (hγ : 0 < γ)
    (hAdverse : η < -velocityH3TransportDerivative3At u t) :
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap RadialPoint244 ℝ,
      (∀ (n : ℕ) (ξ : RadialPoint244),
        ∑ j : RadialAxis244,
          fderiv ℝ (h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))) ξ
            (h3FourierAxisDirection j) = 0) ∧
      Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : RadialPair244,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j : RadialAxis244 => h3SchwartzComplexify
              (Ψ n (h3ClassicalizationFinOfAxis j))) z
          ∂volume.prod volume).im)
        atTop (𝓝 (velocityH3TransportDerivative3At u t)) ∧
      (∀ᶠ n : ℕ in atTop,
        η < -(((2 * Real.pi) ^ 7 / 3) *
          (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j : RadialAxis244 => h3SchwartzComplexify
                (Ψ n (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume).im) +
          ((2 * Real.pi) ^ 7 / 3) *
            (1944 * h3SobolevFirstMomentDeweightingConstant *
              (velocityH3EnergyAt u t + 1) *
              (‖thirdFullSpectralVelocityHighRadialApply244 R
                  (h3AuditActualSpectralVelocityTotal hH3 t)‖ + γ) ^ 2)) := by
  have htNS : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htNS
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS hInt
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hUeq : U = velocityH3SpectralStateAt u t hInt hMeas hFourier := by
    dsimp only [U]
    rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t htNS]
    rfl
  obtain ⟨V, Ψ, hVraw, hAE, hDiv, _hDefect, _hE₂, _hE₃, hFlux⟩ :=
    exists_thirdFullPhysicalSnapshot_solenoidalPureSixthPowerFlux244
      hH3.navier_stokes htNS hH3 hClass ht hFourier
  have hV : Tendsto V atTop (𝓝 U) := by
    rw [hUeq]
    exact hVraw
  let E : ℝ := velocityH3EnergyAt u t
  let K : ℝ := E + 1
  let A : ℝ := (2 * Real.pi) ^ 7 / 3
  let B : ℝ := 1944 * h3SobolevFirstMomentDeweightingConstant * K
  have hEnergy : 1 ≤ E := one_le_velocityH3EnergyAt u t
  have hK : 0 ≤ K := by dsimp only [K]; linarith only [hEnergy]
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity [h3SobolevFirstMomentDeweightingConstant_nonneg]
  have hU : ‖U‖ ≤ E := by
    rw [hUeq]
    exact norm_velocityH3SpectralStateAt_le_energyCeiling
      hFourier hEnergy le_rfl
  have hDiff : Tendsto (fun n : ℕ => ‖V n - U‖)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hV
  have hNearNorm : ∀ᶠ n : ℕ in atTop, ‖V n - U‖ < 1 :=
    hDiff.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hNearTail : ∀ᶠ n : ℕ in atTop, ‖V n - U‖ < γ :=
    hDiff.eventually (eventually_lt_nhds hγ)
  have hThreshold : velocityH3TransportDerivative3At u t < -η := by
    linarith only [hAdverse]
  have hFullLate : ∀ᶠ n : ℕ in atTop,
      A * (∫ z : RadialPair244,
        thirdFullSchwartzComplexSixthPowerFlux244
          (fun j : RadialAxis244 => h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))) z
        ∂volume.prod volume).im < -η := by
    have hEvent := hFlux.eventually (Iio_mem_nhds hThreshold)
    simpa only [A] using hEvent
  refine ⟨Ψ, hDiv, hFlux, ?_⟩
  filter_upwards [hNearNorm, hNearTail, hFullLate]
    with n hnNorm hnTail hnFull
  have hVNorm : ‖V n‖ ≤ K := by
    have hTriangle : ‖V n‖ ≤ ‖V n - U‖ + ‖U‖ := by
      calc
        ‖V n‖ = ‖(V n - U) + U‖ := by rw [sub_add_cancel]
        _ ≤ ‖V n - U‖ + ‖U‖ := norm_add_le _ _
    dsimp only [K]
    linarith only [hTriangle, hnNorm, hU]
  have hTailBound :
      ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ ≤
        ‖V n - U‖ + ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ := by
    calc
      ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ =
          ‖thirdFullSpectralVelocityHighRadialApply244 R ((V n - U) + U)‖ := by
            rw [sub_add_cancel]
      _ = ‖thirdFullSpectralVelocityHighRadialApply244 R (V n - U) +
          thirdFullSpectralVelocityHighRadialApply244 R U‖ := by
            rw [thirdFullSpectralVelocityHighRadialApply_add244]
      _ ≤ ‖thirdFullSpectralVelocityHighRadialApply244 R (V n - U)‖ +
          ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ := norm_add_le _ _
      _ ≤ ‖V n - U‖ + ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ :=
        add_le_add
          (thirdFullSpectralVelocityHighRadialApply_norm_le244 R (V n - U))
          le_rfl
  have hTailLt :
      ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ <
        ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ + γ := by
    linarith only [hTailBound, hnTail]
  have hTailSq :
      ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ ^ 2 ≤
        (‖thirdFullSpectralVelocityHighRadialApply244 R U‖ + γ) ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg (thirdFullSpectralVelocityHighRadialApply244 R (V n)))
      hTailLt.le 2
  let w : RadialAxis244 → SchwartzMap RadialPoint244 ℂ :=
    fun j => h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
  let G : RadialAxis244 → H3SpectralScalarState :=
    fun j => V n (h3ClassicalizationFinOfAxis j)
  have hRep : ∀ j : RadialAxis244,
      (G j : RadialPoint244 → ℂ) =ᵐ[volume]
        (fun ξ : RadialPoint244 =>
          (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ) := by
    intro j
    exact hAE n (h3ClassicalizationFinOfAxis j)
  have hGlobal := thirdFullWeightedSchwartz_highMaxIntegral_le244
    w (hDiv n) (V n) hRep K hK hVNorm R
  let HI : ℂ := ∫ z in thirdFullHighMaxSet244 R,
    thirdFullSchwartzComplexSixthPowerFlux244 w z ∂volume.prod volume
  let LO : ℂ := ∫ z in (thirdFullHighMaxSet244 R)ᶜ,
    thirdFullSchwartzComplexSixthPowerFlux244 w z ∂volume.prod volume
  have hHigh :
      ‖HI‖ ≤ B *
        (‖thirdFullSpectralVelocityHighRadialApply244 R U‖ + γ) ^ 2 := by
    have hFirst : ‖HI‖ ≤ B *
        ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ ^ 2 :=
      hGlobal
    exact hFirst.trans (mul_le_mul_of_nonneg_left hTailSq hB)
  have hImLow : -‖HI‖ ≤ HI.im := by
    have hAbs := Complex.abs_im_le_norm HI
    have hNeg := neg_abs_le HI.im
    linarith only [hAbs, hNeg]
  have hImLowA : -(A * ‖HI‖) ≤ A * HI.im := by
    have h := mul_le_mul_of_nonneg_left hImLow hA
    linarith only [h]
  have hHighA : A * ‖HI‖ ≤
      A * (B * (‖thirdFullSpectralVelocityHighRadialApply244 R U‖ + γ) ^ 2) :=
    mul_le_mul_of_nonneg_left hHigh hA
  have hSplit := thirdFullSchwartzSixthPowerFlux_setSplit244
    w (hDiv n) (thirdFullHighMaxSet244 R)
      (thirdFullHighMaxSet_measurable244 R)
  have hImEq :
      A * (∫ z : RadialPair244,
        thirdFullSchwartzComplexSixthPowerFlux244 w z
          ∂volume.prod volume).im = A * HI.im + A * LO.im := by
    rw [hSplit, Complex.add_im]
    dsimp only [HI, LO]
    ring
  change η < -(A * LO.im) +
    A * (B * (‖thirdFullSpectralVelocityHighRadialApply244 R U‖ + γ) ^ 2)
  change A * (∫ z : RadialPair244,
    thirdFullSchwartzComplexSixthPowerFlux244 w z
      ∂volume.prod volume).im < -η at hnFull
  linarith only [hnFull, hImEq, hImLowA, hHighA]

/-- Explicit arbitrary-radius alternative at an adverse physical snapshot:
if the *genuine weighted-H3* tail cost at R cannot pay half the adverse
margin, the complementary low-maximum signed sixth flux must pay it on the
same real-solenoidal recovery. This is a necessary dichotomy, not a cutoff
uniform in the terminal time. -/
theorem thirdFullPhysical_adverseThird_arbitraryRadiusTailOrLowMax244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R : ℕ) (η γ : ℝ) (hγ : 0 < γ)
    (hAdverse : η < -velocityH3TransportDerivative3At u t) :
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap RadialPoint244 ℝ,
      (∀ (n : ℕ) (ξ : RadialPoint244),
        ∑ j : RadialAxis244,
          fderiv ℝ (h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))) ξ
            (h3FourierAxisDirection j) = 0) ∧
      Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : RadialPair244,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j : RadialAxis244 => h3SchwartzComplexify
              (Ψ n (h3ClassicalizationFinOfAxis j))) z
          ∂volume.prod volume).im)
        atTop (𝓝 (velocityH3TransportDerivative3At u t)) ∧
      ((η / 2 < ((2 * Real.pi) ^ 7 / 3) *
          (1944 * h3SobolevFirstMomentDeweightingConstant *
            (velocityH3EnergyAt u t + 1) *
            (‖thirdFullSpectralVelocityHighRadialApply244 R
                (h3AuditActualSpectralVelocityTotal hH3 t)‖ + γ) ^ 2)) ∨
       (∀ᶠ n : ℕ in atTop,
         η / 2 < -(((2 * Real.pi) ^ 7 / 3) *
           (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
             thirdFullSchwartzComplexSixthPowerFlux244
               (fun j : RadialAxis244 => h3SchwartzComplexify
                 (Ψ n (h3ClassicalizationFinOfAxis j))) z
             ∂volume.prod volume).im))) := by
  obtain ⟨Ψ, hDiv, hFlux, hCost⟩ :=
    thirdFullPhysical_adverseThird_arbitraryRadiusFluxTailBudget244
      hH3 hClass ht R η γ hγ hAdverse
  let C : ℝ := ((2 * Real.pi) ^ 7 / 3) *
    (1944 * h3SobolevFirstMomentDeweightingConstant *
      (velocityH3EnergyAt u t + 1) *
      (‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ + γ) ^ 2)
  refine ⟨Ψ, hDiv, hFlux, ?_⟩
  by_cases hLarge : η / 2 < C
  · exact Or.inl hLarge
  · right
    have hSmall : C ≤ η / 2 := le_of_not_gt hLarge
    filter_upwards [hCost] with n hn
    change η < -(((2 * Real.pi) ^ 7 / 3) *
      (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        thirdFullSchwartzComplexSixthPowerFlux244
          (fun j : RadialAxis244 => h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))) z
        ∂volume.prod volume).im) + C at hn
    linarith only [hn, hSmall]

/-- This is a universal-in-R quantitative physical gap obstruction. A gap
cannot hide an adverse top-third Fourier rate at ALL low-maximum radii
without paying the explicit actual weighted-H3 tail cost. The recovered
Schwartz sequence can depend on t and R; nothing is assumed jointly
measurable in time. -/
def ThirdFullKineticGapArbitraryRadialTradeoff244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x y : ℝ) : Prop :=
  ∀ (R : ℕ) (η γ : ℝ), 0 < γ →
    ∀ t : ℝ, t ∈ Set.Icc x y →
      η < -velocityH3TransportDerivative3At u t →
      ∃ Ψ : ℕ → Fin 3 → SchwartzMap RadialPoint244 ℝ,
        (∀ (n : ℕ) (ξ : RadialPoint244),
          ∑ j : RadialAxis244,
            fderiv ℝ (h3SchwartzComplexify
              (Ψ n (h3ClassicalizationFinOfAxis j))) ξ
              (h3FourierAxisDirection j) = 0) ∧
        Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
          (∫ z : RadialPair244,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j : RadialAxis244 => h3SchwartzComplexify
                (Ψ n (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume).im)
          atTop (𝓝 (velocityH3TransportDerivative3At u t)) ∧
        ((η / 2 < ((2 * Real.pi) ^ 7 / 3) *
            (1944 * h3SobolevFirstMomentDeweightingConstant *
              (velocityH3EnergyAt u t + 1) *
              (‖thirdFullSpectralVelocityHighRadialApply244 R
                  (h3AuditActualSpectralVelocityTotal hH3 t)‖ + γ) ^ 2)) ∨
         (∀ᶠ n : ℕ in atTop,
           η / 2 < -(((2 * Real.pi) ^ 7 / 3) *
             (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
               thirdFullSchwartzComplexSixthPowerFlux244
                 (fun j : RadialAxis244 => h3SchwartzComplexify
                   (Ψ n (h3ClassicalizationFinOfAxis j))) z
               ∂volume.prod volume).im)))

/-- Every strict compact gap satisfies the arbitrary-radius dichotomy.
Unlike an existence-of-R statement, this holds for EVERY R and γ>0. -/
theorem thirdFullPhysical_strictGap_allRadialFluxTradeoffs244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y : ℝ) (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x < y) :
    ThirdFullKineticGapArbitraryRadialTradeoff244 u T hH3 x y := by
  intro R η γ hγ t ht hAdverse
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  exact thirdFullPhysical_adverseThird_arbitraryRadiusTailOrLowMax244
    hH3 hClass htClass R η γ hγ hAdverse

/-- Preserve precisely the original disjoint kinetic annular witnesses.
Every inter-window physical gap has the universal arbitrary-radius signed
flux / weighted-H3 tail alternative; no new gap, window, width or
frequency cutoff is selected in the cofinal construction. -/
theorem thirdFullPhysical_noH3Trace_kineticArbitraryRadialGapTradeoff244
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
      (∀ k : ℕ, ThirdFullKineticGapArbitraryRadialTradeoff244
        u T hH3 (τ (v k) + δ (v k)) (τ (v (k + 1)))) := by
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform, _hCarrier⟩ :=
    thirdFullPhysical_noH3Trace_kineticCompactGapLowMaxCarriers244
      hH3 hClass b hb hNoTrace hDInt M hM
  refine ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform, ?_⟩
  intro k
  have hStart : τ (v k) + δ (v k) ∈ Set.Ioo a T := by
    have ht : τ (v k) ∈ Set.Ioo b T := (hTimes k).2.1
    have hw := (hTimes k).2.2
    rcases hw with ⟨_, hδ, _, hEnd, _, _⟩
    exact ⟨by linarith only [hb.1, ht.1, hδ], hEnd⟩
  have hFinish : τ (v (k + 1)) ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hTimes (k + 1)).2.1.1,
      (hTimes (k + 1)).2.1.2⟩
  exact thirdFullPhysical_strictGap_allRadialFluxTradeoffs244
    hH3 hClass _ _ hStart hFinish
    (hSeparated k (k + 1) (Nat.lt_succ_self k))

end
end PrimeTensor.FirstMonomialTriad
