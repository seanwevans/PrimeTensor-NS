import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularSelectedAspectEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularYoungWidthTemporalContinuity
import Mathlib.Tactic

/-!
# Wide-annulus kinetic evacuation forced by the actual Young-width term

The preceding selected-annulus theorem forces the ratio of outer to inner
radii to escape any fixed constant when finite H3 dissipation supplies the
physical L2 terminal trace. Here we examine the independent, genuinely
nonlinear annular-width obstruction at a *single* selected physical time.

The exact physical deficit retains the real sharp highpass kinetic mass, the
kinetic-only lowpass source, the full Young residual, and the physical zero-
viscosity outer budget. Nonnegativity of the discarded costs is *proved*,
not postulated. For a positive selected kinetic excess and a nonnegative
actual deficit, with sigma² >= 2 rho² and rho > 0, we obtain

  2 sigma^6 * (true annular raw Fourier kinetic mass)
    <= 9 rho^6 * (true physical sharp highpass kinetic mass).

Thus a wide-aperture positive-deficit witness must evacuate almost all its
highpass kinetic mass from the interior of the selected annulus. The theorem
is a necessary spectral concentration condition, not a claim that selected
positive deficits arise from Navier--Stokes, nor a continuation theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The exact unweighted raw kinetic L2 mass on one physical Fourier annulus,
expressed by the *difference* of two already registered sharp Fourier CLMs.
The norm squares are computed on the actual H3 velocity Fourier decoder. -/
noncomputable def thirdFullPhysicalActualSharpAnnularRawMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t rho sigma : ℝ) : ℝ :=
  ∑ j : Fin 3,
    ‖h3CriticalFourierSharpLowCutoffCLM sigma
        (h3SpectralScalarRawFourierL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) j)) -
      h3CriticalFourierSharpLowCutoffCLM rho
        (h3SpectralScalarRawFourierL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) j))‖ ^ 2

/-- The original annular width coefficient pays the exact raw band mass.
No nonlinear Young-residual term is replaced by an abstract surrogate. -/
theorem thirdFullPhysical_actualAnnularYoungWidth_controls_rawBand244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t rho sigma : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma) :
    (2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2) *
        thirdFullPhysicalActualSharpAnnularRawMass244 hH3 t rho sigma ≤
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma := by
  let U : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 t
  have hGap : 0 ≤ (∑ j : Fin 3,
      ‖thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma
        (hRho.trans hOrder)
        (thirdFullPhysicalAnnularYoungResidualBandFourierL2244 rho sigma U j)‖ ^ 2) :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  calc
    (2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2) *
        thirdFullPhysicalActualSharpAnnularRawMass244 hH3 t rho sigma ≤
      thirdFullPhysicalAnnularYoungWidthHilbertCost244
        rho sigma (hRho.trans hOrder) U := by
          dsimp only [thirdFullPhysicalAnnularYoungWidthHilbertCost244,
            thirdFullPhysicalActualSharpAnnularRawMass244]
          linarith only [hGap]
    _ = thirdFullPhysicalActualAnnularYoungWidthCost244
          hH3 t rho sigma :=
      (thirdFullPhysical_actualYoungWidthCost_eq_hilbert244
        hH3 t rho sigma hOrder (hRho.trans hOrder)).symm

/-- The exact deficit polynomial forces a width-cost budget even after
nonnegative Young and physical zero-viscosity source terms are discarded.
The positive kinetic excess is required: squaring an arbitrary signed
mismatch and then discarding the source would otherwise be incorrect. -/
theorem thirdFullKinetic_positiveDeficit_forcesWidthBudget244
    (a w B P Y M N C epsilon : ℝ)
    (ha : 0 ≤ a) (hw : 0 ≤ w) (hB : 0 ≤ B)
    (hP : 0 ≤ P) (hM : 0 ≤ M)
    (hExcess : B ≤ a * M)
    (hYoung : C * N ≤ Y)
    (hDeficit : epsilon ≤
      w * (a * M - B) ^ 2 - M * (Y + w * P)) :
    epsilon + M * (C * N) ≤ w * (a * M) ^ 2 := by
  have hAM : 0 ≤ a * M := mul_nonneg ha hM
  have hGap : 0 ≤ a * M - B := sub_nonneg.mpr hExcess
  have hGapLe : a * M - B ≤ a * M := sub_le_self _ hB
  have hSq : (a * M - B) ^ 2 ≤ (a * M) ^ 2 :=
    pow_le_pow_left₀ hGap hGapLe 2
  have hSqW : w * (a * M - B) ^ 2 ≤ w * (a * M) ^ 2 :=
    mul_le_mul_of_nonneg_left hSq hw
  have hCost : C * N ≤ Y + w * P :=
    hYoung.trans (le_add_of_nonneg_right (mul_nonneg hw hP))
  have hMcost : M * (C * N) ≤ M * (Y + w * P) :=
    mul_le_mul_of_nonneg_left hCost hM
  linarith only [hDeficit, hSqW, hMcost]

/-- A purely scalar wide-aperture estimate: if the outer frequency square
is at least twice the inner frequency square, the ratio of mean-frequency
square to aperture square is at most nine. The positive aperture cancels
without relying on an unavailable strict-multiplication typeclass. -/
theorem thirdFullKinetic_wideAperture_bandWidth_scalar244
    (r s M N : ℝ)
    (hr : 0 < r) (hWide : 2 * r ≤ s) (hM : 0 ≤ M)
    (hWidth :
      (2 * s ^ 3 * ((s - r) / 2) ^ 2) * N ≤
        r ^ 3 * (((r + s) / 2) ^ 2 * M)) :
    2 * s ^ 3 * N ≤ 9 * r ^ 3 * M := by
  let d : ℝ := (s - r) / 2
  let a : ℝ := (r + s) / 2
  have hd : 0 < d := by
    dsimp only [d]
    linarith only [hr, hWide]
  have ha : 0 ≤ a := by
    dsimp only [a]
    linarith only [hr, hWide]
  have hAperture : a ≤ 3 * d := by
    dsimp only [a, d]
    linarith only [hWide]
  have hSquare : a ^ 2 ≤ (3 * d) ^ 2 :=
    pow_le_pow_left₀ ha hAperture 2
  have hScale : 0 ≤ r ^ 3 * M :=
    mul_nonneg (pow_nonneg hr.le 3) hM
  have hUpper : r ^ 3 * (a ^ 2 * M) ≤
      (9 * r ^ 3 * M) * d ^ 2 := by
    calc
      r ^ 3 * (a ^ 2 * M) = (r ^ 3 * M) * a ^ 2 := by ring
      _ ≤ (r ^ 3 * M) * (3 * d) ^ 2 :=
        mul_le_mul_of_nonneg_left hSquare hScale
      _ = (9 * r ^ 3 * M) * d ^ 2 := by ring
  have hScaled : (2 * s ^ 3 * N) * d ^ 2 ≤
      (9 * r ^ 3 * M) * d ^ 2 := by
    calc
      (2 * s ^ 3 * N) * d ^ 2 =
          (2 * s ^ 3 * ((s - r) / 2) ^ 2) * N := by
            dsimp only [d]
            ring
      _ ≤ r ^ 3 * (((r + s) / 2) ^ 2 * M) := hWidth
      _ ≤ (9 * r ^ 3 * M) * d ^ 2 := by
        change r ^ 3 * (a ^ 2 * M) ≤ (9 * r ^ 3 * M) * d ^ 2
        exact hUpper
  exact (mul_le_mul_iff_of_pos_right (pow_pos hd 2)).mp hScaled

/-- HARD PHYSICAL CONSEQUENCE. A genuinely nonnegative actual annular
kinetic deficit with strict kinetic excess cannot carry substantial raw
Fourier kinetic mass in the increasingly wide annulus. This is the precise
σ⁶-versus-ρ⁶ kinetic evacuation forced by the full Young-width cost. -/
theorem thirdFullPhysical_wideAnnularPositiveDeficit_forces_rawBandEvacuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b t rho sigma : ℝ)
    (hRho : 0 < rho) (hOrder : rho ≤ sigma)
    (hWide : 2 * rho ^ 2 ≤ sigma ^ 2)
    (margin : ℝ) (hMargin : 0 < margin)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (hDeficit : 0 ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma) :
    2 * (sigma ^ 2) ^ 3 *
        thirdFullPhysicalActualSharpAnnularRawMass244 hH3 t rho sigma ≤
      9 * (rho ^ 2) ^ 3 *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho := by
  let M : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho
  let N : ℝ := thirdFullPhysicalActualSharpAnnularRawMass244 hH3 t rho sigma
  let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let w : ℝ := (rho ^ 2) ^ 3
  let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      rho (velocityH3Energy0At u b))
  let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
  let Y : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma
  let C : ℝ := 2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; exact sq_nonneg _
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244 _ _))
  have hP : 0 ≤ P := by
    dsimp only [P, thirdFullPhysicalOuterViscousCapBase244]
    have hEnergy : 0 ≤ velocityH3Energy0At u b :=
      velocityH3Energy0At_nonneg u b
    positivity
  have hY : C * N ≤ Y := by
    dsimp only [C, N, Y]
    exact thirdFullPhysical_actualAnnularYoungWidth_controls_rawBand244
      hH3 t rho sigma hRho.le hOrder
  have hEx : B ≤ a * M := by
    change B + margin ≤ a * M at hExcess
    linarith only [hExcess, hMargin]
  have hFloor : 0 ≤ w * (a * M - B) ^ 2 - M * (Y + w * P) := by
    exact hDeficit
  have hBudget := thirdFullKinetic_positiveDeficit_forcesWidthBudget244
    a w B P Y M N C 0 ha hw hB hP hM hEx hY hFloor
  have hMpos : 0 < M := by
    have hPositive : 0 < a * M := by
      change B + margin ≤ a * M at hExcess
      linarith only [hExcess, hMargin, hB]
    by_contra hNot
    have hZero : M = 0 := le_antisymm (le_of_not_gt hNot) hM
    rw [hZero, mul_zero] at hPositive
    exact (not_lt_of_ge (le_refl (0 : ℝ))) hPositive
  have hReduced : C * N ≤ (w * a ^ 2) * M := by
    apply (mul_le_mul_iff_of_pos_left hMpos).mp
    calc
      M * (C * N) ≤ 0 + M * (C * N) := by simp
      _ ≤ w * (a * M) ^ 2 := hBudget
      _ = M * ((w * a ^ 2) * M) := by ring
  have hWidthReal :
      (2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2) * N ≤
        (rho ^ 2) ^ 3 * (((rho ^ 2 + sigma ^ 2) / 2) ^ 2 * M) := by
    dsimp only [C, w, a] at hReduced
    simpa only [mul_assoc] using hReduced
  have hWideResult := thirdFullKinetic_wideAperture_bandWidth_scalar244
    (rho ^ 2) (sigma ^ 2) M N (pow_pos hRho 2) hWide hM hWidthReal
  simpa only [M, N] using hWideResult


/-- A concrete aspect-ratio K turns sixth-order width coercivity into a
normalized *fractional* kinetic-mass estimate. No limit theorem is needed
for this cancellation: the strictly positive inner radius pays the factor. -/
theorem thirdFullKinetic_wideAnnularBand_normalizedAspect244
    (rho sigma K M N : ℝ)
    (hRho : 0 < rho) (hK : 2 ≤ K)
    (hAspect : K * rho ≤ sigma) (hN : 0 ≤ N)
    (hBand : 2 * (sigma ^ 2) ^ 3 * N ≤
      9 * (rho ^ 2) ^ 3 * M) :
    2 * K ^ 6 * N ≤ 9 * M := by
  have hKpos : 0 < K := by linarith only [hK]
  have hKrho : 0 ≤ K * rho := (mul_pos hKpos hRho).le
  have hPower : (K * rho) ^ 6 ≤ sigma ^ 6 :=
    pow_le_pow_left₀ hKrho hAspect 6
  have hRatio : K ^ 6 * (rho ^ 2) ^ 3 ≤ (sigma ^ 2) ^ 3 := by
    calc
      K ^ 6 * (rho ^ 2) ^ 3 = (K * rho) ^ 6 := by ring
      _ ≤ sigma ^ 6 := hPower
      _ = (sigma ^ 2) ^ 3 := by ring
  have hScaled : (2 * K ^ 6 * N) * (rho ^ 2) ^ 3 ≤
      (9 * M) * (rho ^ 2) ^ 3 := by
    calc
      (2 * K ^ 6 * N) * (rho ^ 2) ^ 3 =
          (2 * N) * (K ^ 6 * (rho ^ 2) ^ 3) := by ring
      _ ≤ (2 * N) * (sigma ^ 2) ^ 3 :=
        mul_le_mul_of_nonneg_left hRatio (by positivity)
      _ = 2 * (sigma ^ 2) ^ 3 * N := by ring
      _ ≤ 9 * (rho ^ 2) ^ 3 * M := hBand
      _ = (9 * M) * (rho ^ 2) ^ 3 := by ring
  exact (mul_le_mul_iff_of_pos_right
    (pow_pos (pow_pos hRho 2) 3)).mp hScaled

/-- Cofinal selected-annulus kinetic evacuation under finite physical H3
viscosity: *every* fixed ratio K >= 2 eventually yields a K^{-6} upper
fraction of actual highpass kinetic mass inside the selected band. This
combines the previous physical L2-trace aspect escape with the exact
positive-deficit Young-width coercivity; it does not assume highpass
tightness or a uniform aspect bound as an independent premise. -/
theorem thirdFullPhysical_cofinalSelectedWideAnnularDeficit_bandEvacuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x sigma margin : ℕ → ℝ) (n : ℕ → ℕ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hn : Tendsto n atTop atTop)
    (hOrder : ∀ k : ℕ, (n k : ℝ) + 1 ≤ sigma k)
    (hMargin : ∀ k : ℕ, 0 < margin k)
    (hExcess : ∀ k : ℕ,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          ((n k : ℝ) + 1) (velocityH3Energy0At u b)) + margin k ≤
        ((((n k : ℝ) + 1) ^ 2 + sigma k ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k)
            ((n k : ℝ) + 1))
    (hDeficit : ∀ k : ℕ,
      0 ≤ thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b (x k) ((n k : ℝ) + 1) (sigma k)) :
    ∀ K : ℝ, 2 ≤ K → ∀ᶠ k : ℕ in atTop,
      2 * K ^ 6 *
        thirdFullPhysicalActualSharpAnnularRawMass244
          hH3 (x k) ((n k : ℝ) + 1) (sigma k) ≤
      9 * thirdFullPhysicalActualSharpKineticHighMass244
        hH3 (x k) ((n k : ℝ) + 1) := by
  intro K hK
  have hAspect :=
    thirdFullPhysical_finiteDissipation_selectedNaturalExcess_aspectEscape244
      hH3 hClass hDInt b hb x sigma margin n
      hx hCofinal hn hOrder hMargin hExcess K (by linarith only [hK])
  filter_upwards [hAspect] with k hk
  let rho : ℝ := (n k : ℝ) + 1
  have hRho : 0 < rho := by dsimp only [rho]; positivity
  have hWide : 2 * rho ^ 2 ≤ sigma k ^ 2 := by
    have hK2 : 2 * rho ≤ K * rho :=
      mul_le_mul_of_nonneg_right hK hRho.le
    have hTwo : 2 * rho ≤ sigma k := hK2.trans hk.le
    have hSquare : (2 * rho) ^ 2 ≤ (sigma k) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hTwo 2
    nlinarith only [hSquare, sq_nonneg rho]
  have hBand :=
    thirdFullPhysical_wideAnnularPositiveDeficit_forces_rawBandEvacuation244
      hH3 b (x k) rho (sigma k) hRho
      (hOrder k) hWide
      (margin k) (hMargin k) (hExcess k) (hDeficit k)
  have hN : 0 ≤ thirdFullPhysicalActualSharpAnnularRawMass244
      hH3 (x k) rho (sigma k) := by
    unfold thirdFullPhysicalActualSharpAnnularRawMass244
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  exact thirdFullKinetic_wideAnnularBand_normalizedAspect244
    rho (sigma k) K
    (thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) rho)
    (thirdFullPhysicalActualSharpAnnularRawMass244 hH3 (x k) rho (sigma k))
    hRho hK hk.le hN hBand

end
end PrimeTensor.FirstMonomialTriad
