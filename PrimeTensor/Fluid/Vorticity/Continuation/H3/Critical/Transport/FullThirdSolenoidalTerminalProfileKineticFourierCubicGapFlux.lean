import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticCumulativeSignedGapTransport
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalMinimumFrequencyPartition
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedTopTransport
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Encoded.Canonical.Energy.Restart.Closure
import Mathlib.Tactic

/-!
# Native solenoidal sixth-power Fourier flux on the genuine kinetic H3 gaps

The real-solenoidal Schwartz approximation of an actual preterminal physical
snapshot has a pure, uncorrected sixth-power Fourier transfer. Its exactly
partitioned six-dimensional triad integral obeys the genuine moment estimate

  ‖integral F6‖ <= 1944 C1 K^3.

Unlike an existential cutoff-independent bound, the first theorem chooses
K = E3(t)+1 explicitly, by the actual weighted physical Fourier state and
its strong solenoidal Schwartz recovery. Passing to the physical flux limit
yields a pointwise physical top-order signed H3 transport bound, without
postulating a globally bounded H3 state or discarding the complex phases.

The second theorem combines it with the accepted exact lower-order physical
energy balance. The resulting nonnegative majorant of the true signed H3
replenishment is integrated over the ORIGINAL gaps between the kinetic PDE
persistence windows. The cumulative budget thus has a real Fourier origin,
not an independent transport cap or a presumed favorable flux sign.

This does not exclude fast H3 energy growth or regularity breakdown: its
energy-cubic gap majorant is not proved integrable on the terminal tail.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology FourierTransform
open scoped BigOperators Interval ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeKineticFourierGap244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

private abbrev FluxAxis244 := PrimeTensor.Axis Depth.three
private abbrev FluxV244 := H3FourierPoint3
private abbrev FluxPair244 := FluxV244 × FluxV244

/-- A physical signed third-order transport snapshot has an EXPLICIT native
cubic bound from the six-orbit solenoidal Fourier flux. The choice of the
Schwartz recovery cutoff never enters the final physical right side. -/
theorem thirdFullPhysical_topThird_sixthFlux_le_energyCubic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    |velocityH3TransportDerivative3At u t| ≤
      ((2 * Real.pi) ^ 7 / 3) *
        (1944 * h3SobolevFirstMomentDeweightingConstant *
          (velocityH3EnergyAt u t + 1) ^ 3) := by
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
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  obtain ⟨V, Ψ, hV, hAE, hDiv, _hDefect, _hE2, _hE3, hFlux⟩ :=
    exists_thirdFullPhysicalSnapshot_solenoidalPureSixthPowerFlux244
      hH3.navier_stokes htNS hH3 hClass ht hFourier
  let E : ℝ := velocityH3EnergyAt u t
  let K : ℝ := E + 1
  have hEnergy : 1 ≤ E := one_le_velocityH3EnergyAt u t
  have hK : 0 ≤ K := by dsimp only [K]; linarith only [hEnergy]
  have hU : ‖U‖ ≤ E :=
    norm_velocityH3SpectralStateAt_le_energyCeiling
      hFourier hEnergy le_rfl
  have hNear : ∀ᶠ n : ℕ in atTop, ‖V n - U‖ < 1 := by
    have hDiff : Tendsto (fun n : ℕ => ‖V n - U‖)
        atTop (𝓝 (0 : ℝ)) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hV
    exact hDiff.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hNorm : ∀ᶠ n : ℕ in atTop, ‖V n‖ ≤ K := by
    filter_upwards [hNear] with n hn
    have hTriangle : ‖V n‖ ≤ ‖V n - U‖ + ‖U‖ := by
      calc
        ‖V n‖ = ‖(V n - U) + U‖ := by rw [sub_add_cancel]
        _ ≤ ‖V n - U‖ + ‖U‖ := norm_add_le _ _
    dsimp only [K]
    linarith only [hTriangle, hn, hU]
  let A : ℝ := (2 * Real.pi) ^ 7 / 3
  let B : ℝ := 1944 * h3SobolevFirstMomentDeweightingConstant * K ^ 3
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let F : ℕ → ℝ := fun n =>
    A * (∫ z : FluxPair244,
      thirdFullSchwartzComplexSixthPowerFlux244
        (fun j : FluxAxis244 => h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) z
      ∂volume.prod volume).im
  have hAt (n : ℕ) (hn : ‖V n‖ ≤ K) : |F n| ≤ A * B := by
    let v : FluxAxis244 → SchwartzMap FluxV244 ℂ :=
      fun j => h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
    let G : FluxAxis244 → H3SpectralScalarState :=
      fun j => V n (h3ClassicalizationFinOfAxis j)
    have hRep : ∀ j : FluxAxis244, (G j : FluxV244 → ℂ) =ᵐ[volume]
        (fun ξ : FluxV244 =>
          (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ) := by
      intro j
      exact hAE n (h3ClassicalizationFinOfAxis j)
    have hCoord (j : FluxAxis244) : ‖G j‖ ≤ K :=
      (h3SpectralFinVector_coordinate_norm_le
        (V n) (h3ClassicalizationFinOfAxis j)).trans hn
    have hGlobal := thirdFullWeightedSchwartz_globalMinSectorIntegral_le244
      v (hDiv n) G hRep K hK hCoord
    have hImag :
        |(∫ z : FluxPair244,
          thirdFullSchwartzComplexSixthPowerFlux244 v z
            ∂volume.prod volume).im| ≤
        ‖∫ z : FluxPair244,
          thirdFullSchwartzComplexSixthPowerFlux244 v z
            ∂volume.prod volume‖ :=
      Complex.abs_im_le_norm _
    change |A * (∫ z : FluxPair244,
          thirdFullSchwartzComplexSixthPowerFlux244 v z
            ∂volume.prod volume).im| ≤ A * B
    calc
      |A * (∫ z : FluxPair244,
          thirdFullSchwartzComplexSixthPowerFlux244 v z
            ∂volume.prod volume).im| =
          A * |(∫ z : FluxPair244,
            thirdFullSchwartzComplexSixthPowerFlux244 v z
              ∂volume.prod volume).im| := by
              rw [abs_mul, abs_of_nonneg hA]
      _ ≤ A * ‖∫ z : FluxPair244,
          thirdFullSchwartzComplexSixthPowerFlux244 v z
            ∂volume.prod volume‖ :=
          mul_le_mul_of_nonneg_left hImag hA
      _ ≤ A * B :=
          mul_le_mul_of_nonneg_left hGlobal hA
  have hFlux' : Tendsto F atTop
      (𝓝 (velocityH3TransportDerivative3At u t)) := by
    simpa only [F, A] using hFlux
  have hEvent : ∀ᶠ n : ℕ in atTop, |F n| ≤ A * B := by
    filter_upwards [hNorm] with n hn
    exact hAt n hn
  have hTend : Tendsto (fun n : ℕ => |F n|) atTop
      (𝓝 |velocityH3TransportDerivative3At u t|) := hFlux'.abs
  have hLimit : |velocityH3TransportDerivative3At u t| ≤ A * B :=
    le_of_tendsto hTend hEvent
  simpa only [A, B, K, E] using hLimit

/-- The actual positive signed H3 growth surplus is bounded by a LOW-order
physical multiplier plus the genuine six-orbit solenoidal Fourier cubic.
The sign of the sixth-order flux is not dropped until the proven absolute
bound has been applied. -/
theorem thirdFullPhysical_positiveSignedSurplus_le_sixthFluxCubic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    max 0 (-velocityH3TransportDerivativeAt u t -
        2 * velocityH3DissipationAt u t) ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        velocityH3EnergyAt u t +
      ((2 * Real.pi) ^ 7 / 3) *
        (1944 * h3SobolevFirstMomentDeweightingConstant *
          (velocityH3EnergyAt u t + 1) ^ 3) := by
  let E : ℝ := velocityH3EnergyAt u t
  let D : ℝ := velocityH3DissipationAt u t
  let T3 : ℝ := velocityH3TransportDerivative3At u t
  let L : ℝ := 24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
    Real.sqrt E) * E
  let C : ℝ := ((2 * Real.pi) ^ 7 / 3) *
    (1944 * h3SobolevFirstMomentDeweightingConstant * (E + 1) ^ 3)
  have hEnergy : 0 ≤ E :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_velocityH3EnergyAt u t)
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity [h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg]
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity [h3SobolevFirstMomentDeweightingConstant_nonneg]
  have hTop : |T3| ≤ C :=
    thirdFullPhysical_topThird_sixthFlux_le_energyCubic244 hH3 hClass ht
  have hBase := h3PathCanonical_deriv_add_dissipation_le_signedTopTransport
    hH3 hClass ht
  have hFull := deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
    hH3 hClass ht
  have hNeg : -T3 ≤ |T3| := neg_le_abs T3
  have hD : 0 ≤ D := velocityH3DissipationAt_nonneg u t
  have hUpper : -velocityH3TransportDerivativeAt u t - 2 * D ≤ L + C := by
    dsimp only [L, C, T3, D, E] at hBase hFull hTop hNeg hD ⊢
    linarith only [hBase, hFull, hTop, hNeg, hD]
  change max 0 (-velocityH3TransportDerivativeAt u t - 2 * D) ≤ L + C
  exact max_le (add_nonneg hL hC) hUpper

/-- The physical signed replenishment on each genuine compact gap is paid
by a time-integrable majorant from the native solenoidal sixth-order Fourier
flux and the verified low-order physical commutator. The gap endpoints are
not shifted and neither term is asserted terminal-L1 integrable. -/
theorem thirdFullPhysical_gap_positiveSurplusIntegral_le_sixthFluxCubic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y : ℝ) (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x < y) :
    (∫ s in x..y,
      max 0 (-velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s)) ≤
      ∫ s in x..y,
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u s)) *
            velocityH3EnergyAt u s +
          ((2 * Real.pi) ^ 7 / 3) *
            (1944 * h3SobolevFirstMomentDeweightingConstant *
              (velocityH3EnergyAt u s + 1) ^ 3)) := by
  let E : ℝ → ℝ := velocityH3EnergyAt u
  let A : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  let B : ℝ := ((2 * Real.pi) ^ 7 / 3)
  let C : ℝ := 1944 * h3SobolevFirstMomentDeweightingConstant
  let F : ℝ → ℝ := fun s => 24 * (A * Real.sqrt (E s)) * E s +
    B * (C * (E s + 1) ^ 3)
  have hSubset : Set.Icc x y ⊆ Set.Ioo a T := by
    intro s hs
    exact ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hy.2⟩
  have hE : ContinuousOn E (Set.Icc x y) :=
    (continuousOn_velocityH3EnergyAt_on_energyClassTail
      hH3 hClass).mono hSubset
  have hSqrt : ContinuousOn (fun s => Real.sqrt (E s)) (Set.Icc x y) :=
    Real.continuous_sqrt.comp_continuousOn hE
  have hFirst : ContinuousOn
      (fun s => 24 * (A * Real.sqrt (E s)) * E s)
      (Set.Icc x y) :=
    ((continuousOn_const.mul (continuousOn_const.mul hSqrt)).mul hE)
  have hSecond : ContinuousOn
      (fun s => B * (C * (E s + 1) ^ 3)) (Set.Icc x y) :=
    continuousOn_const.mul
      (continuousOn_const.mul ((hE.add continuousOn_const).pow 3))
  have hFInt : IntervalIntegrable F volume x y :=
    ((hFirst.add hSecond)).intervalIntegrable_of_Icc hxy.le
  have hGInt :=
    (h3Critical_physicalGap_signedPositiveTransport_intervalIntegrable_automatic
      hH3 hClass x y hx hy hxy).2
  have hPoint (s : ℝ) (hs : s ∈ Set.Icc x y) :
      max 0 (-velocityH3TransportDerivativeAt u s -
          2 * velocityH3DissipationAt u s) ≤ F s := by
    have h := thirdFullPhysical_positiveSignedSurplus_le_sixthFluxCubic244
      hH3 hClass (hSubset hs)
    simpa only [F, A, B, C, E] using h
  have hIntegral := intervalIntegral.integral_mono_on
    hxy.le hGInt hFInt hPoint
  simpa only [F, E, A, B, C] using hIntegral

/-- The original kinetic windows now have an explicit FOURIER-origin
majorant for the positive signed transport that replenishes their gaps.
It combines the actual physical sixth-order solenoidal flux with the lower
physical commutator, and preserves every original window and cutoff. -/
theorem thirdFullPhysical_kineticDisjoint_cumulativeSixthFluxGapBudget244
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
        (M (v k)) (δ (v k))) :
    ∀ m : ℕ,
      (∃ k : ℕ, k ≤ m ∧
        ∃ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) ∧
          M (v k) / 4 < h3PathSqrtEnergyRiccatiCoefficient *
            Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
      (∑ k ∈ Finset.range (m + 1), δ (v k) * (M (v k) / 4)) + 1 ≤
        velocityH3EnergyAt u (τ (v 0)) +
        ∑ k ∈ Finset.range m,
          ∫ s in (τ (v k) + δ (v k))..τ (v (k + 1)),
            (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
                Real.sqrt (velocityH3EnergyAt u s)) *
                velocityH3EnergyAt u s +
              ((2 * Real.pi) ^ 7 / 3) *
                (1944 * h3SobolevFirstMomentDeweightingConstant *
                  (velocityH3EnergyAt u s + 1) ^ 3)) := by
  have hBase := thirdFullPhysical_kineticDisjoint_cumulativeSignedGapBudget244
    hH3 hClass b hb M τ N δ v hSeparated hWindows
  have hGapStart (k : ℕ) :
      τ (v k) + δ (v k) ∈ Set.Ioo a T := by
    obtain ⟨ht, hw⟩ := hWindows k
    rcases hw with ⟨_, hδ, _, hEnd, _, _⟩
    exact ⟨by linarith only [hb.1, ht.1, hδ], hEnd⟩
  have hGapFinish (k : ℕ) :
      τ (v (k + 1)) ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hWindows (k + 1)).1.1,
      (hWindows (k + 1)).1.2⟩
  have hGap (k : ℕ) :
      (∫ s in (τ (v k) + δ (v k))..τ (v (k + 1)),
        max 0 (-velocityH3TransportDerivativeAt u s -
          2 * velocityH3DissipationAt u s)) ≤
      ∫ s in (τ (v k) + δ (v k))..τ (v (k + 1)),
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u s)) *
            velocityH3EnergyAt u s +
          ((2 * Real.pi) ^ 7 / 3) *
            (1944 * h3SobolevFirstMomentDeweightingConstant *
              (velocityH3EnergyAt u s + 1) ^ 3)) :=
    thirdFullPhysical_gap_positiveSurplusIntegral_le_sixthFluxCubic244
      hH3 hClass _ _ (hGapStart k) (hGapFinish k)
      (hSeparated k (k + 1) (Nat.lt_succ_self k))
  intro m
  rcases hBase m with hRiccati | hBudget
  · exact Or.inl hRiccati
  · right
    have hSum :
        (∑ k ∈ Finset.range m,
          ∫ s in (τ (v k) + δ (v k))..τ (v (k + 1)),
            max 0 (-velocityH3TransportDerivativeAt u s -
              2 * velocityH3DissipationAt u s)) ≤
        ∑ k ∈ Finset.range m,
          ∫ s in (τ (v k) + δ (v k))..τ (v (k + 1)),
            (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
                Real.sqrt (velocityH3EnergyAt u s)) *
                velocityH3EnergyAt u s +
              ((2 * Real.pi) ^ 7 / 3) *
                (1944 * h3SobolevFirstMomentDeweightingConstant *
                  (velocityH3EnergyAt u s + 1) ^ 3)) :=
      Finset.sum_le_sum (fun k _ => hGap k)
    linarith only [hBudget, hSum]


/-- Same-witness physical no-H3-trace consequence. The finite cumulative
kinetic charges are paid by an actual Riccati-scale H3 time, or by the initial
physical energy and an explicitly Fourier-derived cubic gap integral. The
original uniformly vanishing raw kinetic carriers and exact dissipative
windows remain visible in this statement. -/
theorem thirdFullPhysical_noH3Trace_kineticSixthFluxGapObstruction244
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
      (∀ m : ℕ,
        (∃ k : ℕ, k ≤ m ∧
          ∃ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) ∧
            M (v k) / 4 < h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
        (∑ k ∈ Finset.range (m + 1), δ (v k) * (M (v k) / 4)) + 1 ≤
          velocityH3EnergyAt u (τ (v 0)) +
          ∑ k ∈ Finset.range m,
            ∫ s in (τ (v k) + δ (v k))..τ (v (k + 1)),
              (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
                  Real.sqrt (velocityH3EnergyAt u s)) *
                  velocityH3EnergyAt u s +
                ((2 * Real.pi) ^ 7 / 3) *
                  (1944 * h3SobolevFirstMomentDeweightingConstant *
                    (velocityH3EnergyAt u s + 1) ^ 3))) := by
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform, _hAccount⟩ :=
    thirdFullPhysical_noH3Trace_kineticCumulativeSignedGapObstruction244
      hH3 hClass b hb hNoTrace hDInt M hM
  have hWindows (k : ℕ) :
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)) :=
    ⟨(hTimes k).2.1, (hTimes k).2.2⟩
  have hFourier := thirdFullPhysical_kineticDisjoint_cumulativeSixthFluxGapBudget244
    hH3 hClass b hb M τ N δ v hSeparated hWindows
  exact ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform, hFourier⟩

end
end PrimeTensor.FirstMonomialTriad
