import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalPhysicalMomentBridge
import Mathlib.Tactic

/-!
# The physical H³ transport survives removal of moving thin radial shells

The signed, real physical third-order transport is already the limit of the
*same* genuine solenoidal Schwartz sixth-power flux as the weighted H³ recovery.
The previous physical moment bridge bounds its exact unsigned three-contraction
budget uniformly in the recovery index. The quantitative radial shell estimate
therefore kills any moving common-squared-radius annulus with bounded radii and
vanishing width, even though the Fourier velocity changes at every index.

Subtract the shell from the full complex Fourier integral using the existing
exact measure-theoretic partition.  The off-shell *signed imaginary part* then
converges to the ORIGINAL physical H³ transport.  This is a localization of a
necessary surviving channel, NOT a coercivity or favorable-sign argument.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology FourierTransform
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev PairV := V3 × V3

noncomputable local instance axisFintypePhysicalOffshellPersistence244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- General complex-integral transfer: a near-shell piece whose *norm* tends
 to zero cannot alter the limiting signed imaginary part of the full flux.
The exact solenoidal integrability theorem supplies the integral partition. -/
theorem thirdFullSchwartzSixthPowerFlux_offshell_tendsto_of_shellZero244
    (v : ℕ → A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ n : ℕ, ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v n j) x (h3FourierAxisDirection j) = 0)
    (s : ℕ → Set PairV) (hs : ∀ n, MeasurableSet (s n))
    (hNear : Tendsto (fun n : ℕ =>
      ‖∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume‖) atTop (𝓝 (0 : ℝ)))
    (L : ℝ)
    (hFull : Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
      (∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume).im) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
      (∫ z in (s n)ᶜ, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume).im) atTop (𝓝 L) := by
  have hNearImBound (n : ℕ) :
      ‖(∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume).im‖ ≤
      ‖∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume‖ := by
    simpa only [Real.norm_eq_abs] using
      (Complex.abs_im_le_norm
        (∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
          ∂volume.prod volume))
  have hNearImNorm : Tendsto (fun n : ℕ =>
      ‖(∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume).im‖) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun n => norm_nonneg _) hNearImBound hNear
  have hNearIm : Tendsto (fun n : ℕ =>
      (∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume).im) atTop (𝓝 (0 : ℝ)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hNearImNorm
  have hNearScaled : Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
      (∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume).im) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (hNearIm.const_mul ((2 * Real.pi) ^ 7 / 3))
  have hDiff : Tendsto (fun n : ℕ =>
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
          ∂volume.prod volume).im -
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
          ∂volume.prod volume).im) atTop (𝓝 L) := by
    simpa only [sub_zero] using hFull.sub hNearScaled
  have hOffEq (n : ℕ) :
      (∫ z in (s n)ᶜ, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume) =
      (∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume) -
      (∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume) := by
    rw [thirdFullSchwartzSixthPowerFlux_setSplit244
      (v n) (hDiv n) (s n) (hs n)]
    abel
  have hOffFn : (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
      (∫ z in (s n)ᶜ, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume).im) =
      (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
          ∂volume.prod volume).im -
        ((2 * Real.pi) ^ 7 / 3) *
        (∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
          ∂volume.prod volume).im) := by
    funext n
    rw [hOffEq n, Complex.sub_im]
    ring
  rw [hOffFn]
  exact hDiff

/-- Bounded physical Fourier mass and first moment convert moving-annulus
suppression into convergence of the *off-shell signed transport itself*. -/
theorem thirdFullSchwartzSixthPowerFlux_offshell_tendsto_of_moments244
    (v : ℕ → A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ n : ℕ, ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v n j) x (h3FourierAxisDirection j) = 0)
    (lo hi : ℕ → ℝ) (H M E : ℝ)
    (hlo : ∀ n, 0 ≤ lo n) (hlohi : ∀ n, lo n ≤ hi n)
    (hhi : ∀ n, hi n ≤ H)
    (s : ℕ → Set PairV) (hs : ∀ n, MeasurableSet (s n))
    (hShell : ∀ n z, z ∈ s n →
      thirdFullTriadWithinSquareAnnulus244 (lo n) (hi n) z)
    (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hMass : ∀ n, thirdFullBudgetFourierMass244 (v n) ≤ E)
    (hFirst : ∀ n, thirdFullBudgetFirstMoment244 (v n) ≤ M)
    (hWidth : Tendsto (fun n => hi n - lo n) atTop (𝓝 (0 : ℝ)))
    (L : ℝ)
    (hFull : Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
      (∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume).im) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
      (∫ z in (s n)ᶜ, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume).im) atTop (𝓝 L) := by
  have hNear := thirdFullSchwartzSixthPowerFlux_movingAnnulus_vanishes_of_moments244
    v hDiv lo hi H M E hlo hlohi hhi s hs hShell hM hE hMass hFirst hWidth
  exact thirdFullSchwartzSixthPowerFlux_offshell_tendsto_of_shellZero244
    v hDiv s hs hNear L hFull

/-- At every Fourier-compatible interior Navier--Stokes snapshot, use the
ALREADY CONSTRUCTED real solenoidal, H³-strongly converging recovery family.
No new raw-moment premise is needed: the physical weighted representation
controls both raw moments on that very same family.  An arbitrary moving
bounded thin common-radius annulus contributes asymptotically zero flux;
its complement carries the full OLD physical signed third-order transport. -/
theorem exists_thirdFullPhysicalSnapshot_offshellTransportPersistence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (htNS : t ∈ Set.Ioo (0 : ℝ) T)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (lo hi : ℕ → ℝ) (H : ℝ)
    (hlo : ∀ n, 0 ≤ lo n) (hlohi : ∀ n, lo n ≤ hi n)
    (hhi : ∀ n, hi n ≤ H)
    (s : ℕ → Set PairV) (hs : ∀ n, MeasurableSet (s n))
    (hShell : ∀ n z, z ∈ s n →
      thirdFullTriadWithinSquareAnnulus244 (lo n) (hi n) z)
    (hWidth : Tendsto (fun n => hi n - lo n) atTop (𝓝 (0 : ℝ))) :
    ∃ (V : ℕ → H3SpectralVelocityState)
      (Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ) (K : ℝ),
      0 ≤ K ∧
      Tendsto V atTop
        (𝓝 (velocityH3SpectralStateAt u t hInt hMeas hFourier)) ∧
      (∀ (n : ℕ) (x : V3), ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) x
            (h3FourierAxisDirection j) = 0) ∧
      (∀ n : ℕ,
        let v : A3 → SchwartzMap V3 ℂ :=
          fun j => h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
        thirdFullBudgetFourierMass244 v ≤ 3 * K ^ 2 ∧
        thirdFullBudgetFirstMoment244 v ≤
          3 * h3SobolevFirstMomentDeweightingConstant * K ∧
        thirdFullSchwartzSixthFluxTotalBudget244 v ≤
          27 * h3SobolevFirstMomentDeweightingConstant * K ^ 3) ∧
      Tendsto (fun n : ℕ =>
        ‖∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244
          (fun j : A3 => h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))) z
          ∂volume.prod volume‖) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
        (∫ z in (s n)ᶜ, thirdFullSchwartzComplexSixthPowerFlux244
          (fun j : A3 => h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))) z
          ∂volume.prod volume).im)
        atTop (𝓝 (velocityH3TransportDerivative3At u t)) := by
  obtain ⟨V, Ψ, K, hK, hV, hDiv, hMoment, hFull⟩ :=
    exists_thirdFullPhysicalSnapshot_solenoidalUniformMomentBudget244
      hNS htNS hH3 hClass ht hFourier
  let v : ℕ → A3 → SchwartzMap V3 ℂ :=
    fun n j => h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
  have hDivV : ∀ n : ℕ, ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v n j) x (h3FourierAxisDirection j) = 0 := by
    intro n x
    exact hDiv n x
  have hMass : ∀ n, thirdFullBudgetFourierMass244 (v n) ≤ 3 * K ^ 2 := by
    intro n
    exact (hMoment n).1
  have hFirst : ∀ n, thirdFullBudgetFirstMoment244 (v n) ≤
      3 * h3SobolevFirstMomentDeweightingConstant * K := by
    intro n
    exact (hMoment n).2.1
  have hM : 0 ≤ 3 * h3SobolevFirstMomentDeweightingConstant * K :=
    mul_nonneg
      (mul_nonneg (by norm_num)
        h3SobolevFirstMomentDeweightingConstant_nonneg) hK
  have hE : 0 ≤ 3 * K ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg K)
  have hNear := thirdFullSchwartzSixthPowerFlux_movingAnnulus_vanishes_of_moments244
    v hDivV lo hi H
      (3 * h3SobolevFirstMomentDeweightingConstant * K) (3 * K ^ 2)
    hlo hlohi hhi s hs hShell hM hE hMass hFirst hWidth
  have hOff := thirdFullSchwartzSixthPowerFlux_offshell_tendsto_of_shellZero244
    v hDivV s hs hNear (velocityH3TransportDerivative3At u t) hFull
  refine ⟨V, Ψ, K, hK, hV, hDiv, hMoment, ?_, ?_⟩
  · simpa only [v] using hNear
  · simpa only [v] using hOff

end
end PrimeTensor.FirstMonomialTriad
