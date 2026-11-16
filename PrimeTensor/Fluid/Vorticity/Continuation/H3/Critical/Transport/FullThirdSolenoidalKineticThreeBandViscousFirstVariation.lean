import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandLerayTransferProbe
import Mathlib.Tactic

/-!
# Viscous first variation of the exact three-band Navier--Stokes symbol

This is the next algebraic test following the verified six-mode example.
All classical real operations appear only in the established real Fourier
bridge. No native PrimeMultiset/PrimeRatio addition, subtraction or zero is
introduced, and positive-rank tensor coordinates remain the old Axis fold.

For spatial frequency k times the original three-mode geometry, and a common
Fourier amplitude A, the exact high-mode nonlinear kinetic work is 2*k*A^3.
The Laplacian loss at that same high mode is 10*nu*k^2*A^2. Therefore

  highNet(nu,k,A) = 2*k*A^2*(A - 5*nu*k).

Here highNet is per positive Fourier mode, with the usual (1/2)|u_hat|^2
kinetic normalization; the real Hermitian pair has twice this variation.
For positive viscosity and frequency the high mode gains kinetic energy
initially iff A > 5*nu*k (assuming A > 0). Both nonlinear outward cutoff
fluxes remain positive for every A,k > 0.

This is a first-variation symbol calculation, NOT a proof of a time-uniform
flux inequality, Schwartz localization, or global regularity. The genuine
unforced PDE interpretation uses the standard Fourier NS ODE at initial time;
its derivation from project-local solution data is a separate bridge task.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

/-- Squared radius of the actual high Fourier wavevector (3,1,0). -/
theorem thirdFullThreeBand_highWaveSquare_eq244 :
    thirdFullThreeBandDot244
      thirdFullThreeBandWaveHigh244 thirdFullThreeBandWaveHigh244 = 10 := by
  norm_num [thirdFullThreeBandDot244,
    thirdFullThreeBandWaveHigh244, thirdFullThreeBandAdd244,
    thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
    PrimeTensor.Bridge.Euclidean.axis_fold_three]

/-- Squared high-mode solenoidal polarization magnitude. -/
theorem thirdFullThreeBand_highPolarSquare_eq244 :
    thirdFullThreeBandDot244
      thirdFullThreeBandPolarHigh244 thirdFullThreeBandPolarHigh244 = 1 := by
  norm_num [thirdFullThreeBandDot244, thirdFullThreeBandPolarHigh244,
    PrimeTensor.Bridge.Euclidean.axis_fold_three]

/-- Scaled true nonlinear work at each of the three positive Fourier modes. -/
def thirdFullThreeBand_scaledLowWork244 (k A : ℝ) : ℝ :=
  k * A ^ 3 * thirdFullThreeBandProjectedLow244

def thirdFullThreeBand_scaledMidWork244 (k A : ℝ) : ℝ :=
  k * A ^ 3 * thirdFullThreeBandProjectedMid244

def thirdFullThreeBand_scaledHighWork244 (k A : ℝ) : ℝ :=
  k * A ^ 3 * thirdFullThreeBandProjectedHigh244

/-- Genuine cubic scaling of the full signed (Hermitian) triad symbol. -/
theorem thirdFullThreeBand_scaledWork_triple244 (k A : ℝ) :
    thirdFullThreeBand_scaledLowWork244 k A = -(k * A ^ 3) ∧
    thirdFullThreeBand_scaledMidWork244 k A = -(k * A ^ 3) ∧
    thirdFullThreeBand_scaledHighWork244 k A = 2 * k * A ^ 3 := by
  obtain ⟨hL, hM, hH⟩ := thirdFullThreeBand_exampleProjectedWork244
  constructor
  · unfold thirdFullThreeBand_scaledLowWork244
    rw [hL]
    ring
  constructor
  · unfold thirdFullThreeBand_scaledMidWork244
    rw [hM]
    ring
  · unfold thirdFullThreeBand_scaledHighWork244
    rw [hH]
    ring

/-- Both outer cutoff fluxes remain positive at any positive scale/amplitude.
The right cutoff is the gain above 3*k; the left is the drain below 3*k/2. -/
theorem thirdFullThreeBand_scaledBothOutward_pos244
    (k A : ℝ) (hk : 0 < k) (hA : 0 < A) :
    0 < -thirdFullThreeBand_scaledLowWork244 k A ∧
    0 < thirdFullThreeBand_scaledHighWork244 k A := by
  obtain ⟨hL, _, hH⟩ := thirdFullThreeBand_scaledWork_triple244 k A
  rw [hL, hH]
  have hProd : 0 < k * A ^ 3 := mul_pos hk (pow_pos hA 3)
  constructor
  · simpa only [neg_neg] using hProd
  · positivity

/-- Exact high-mode viscous energy loss at frequency k*(3,1,0).
The factor |k*c|^2 is multiplied by the actual high polarization norm. -/
def thirdFullThreeBand_scaledHighViscousLoss244
    (nu k A : ℝ) : ℝ :=
  nu * k ^ 2 * A ^ 2 *
    (thirdFullThreeBandDot244
      thirdFullThreeBandWaveHigh244 thirdFullThreeBandWaveHigh244) *
    (thirdFullThreeBandDot244
      thirdFullThreeBandPolarHigh244 thirdFullThreeBandPolarHigh244)

/-- Unforced high-mode kinetic first variation, before the Hermitian factor 2. -/
def thirdFullThreeBand_scaledHighNet244
    (nu k A : ℝ) : ℝ :=
  thirdFullThreeBand_scaledHighWork244 k A -
    thirdFullThreeBand_scaledHighViscousLoss244 nu k A

/-- Exact physical viscous competition. No high-Sobolev or terminal hypothesis. -/
theorem thirdFullThreeBand_scaledHighNet_formula244
    (nu k A : ℝ) :
    thirdFullThreeBand_scaledHighNet244 nu k A =
      2 * k * A ^ 2 * (A - 5 * nu * k) := by
  unfold thirdFullThreeBand_scaledHighNet244
    thirdFullThreeBand_scaledHighWork244
    thirdFullThreeBand_scaledHighViscousLoss244
  rw [thirdFullThreeBand_exampleProjectedWork244.2.2,
    thirdFullThreeBand_highWaveSquare_eq244,
    thirdFullThreeBand_highPolarSquare_eq244]
  ring

/-- The exact amplitude threshold for a high-mode gain, when k,A are positive. -/
theorem thirdFullThreeBand_scaledHighNet_positive_iff244
    (nu k A : ℝ) (hk : 0 < k) (hA : 0 < A) :
    0 < thirdFullThreeBand_scaledHighNet244 nu k A ↔
      5 * nu * k < A := by
  rw [thirdFullThreeBand_scaledHighNet_formula244]
  have hp : 0 < 2 * k * A ^ 2 := by positivity
  constructor
  · intro h
    by_contra hNot
    have hLe : A ≤ 5 * nu * k := le_of_not_gt hNot
    have hg : A - 5 * nu * k ≤ 0 := sub_nonpos.mpr hLe
    have hc : (2 * k * A ^ 2) * (A - 5 * nu * k) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hp.le hg
    linarith
  · intro h
    exact mul_pos hp (sub_pos.mpr h)

/-- At the exactly balanced amplitude viscosity cancels nonlinear growth. -/
theorem thirdFullThreeBand_scaledHighNet_threshold_zero244
    (nu k : ℝ) :
    thirdFullThreeBand_scaledHighNet244 nu k (5 * nu * k) = 0 := by
  rw [thirdFullThreeBand_scaledHighNet_formula244]
  ring

/-- Every positive viscosity and frequency admits a strictly positive
initial high-mode kinetic gain, e.g. the amplitude 6*nu*k. -/
theorem thirdFullThreeBand_scaledHighNet_supercritical244
    (nu k : ℝ) (hnu : 0 < nu) (hk : 0 < k) :
    0 < thirdFullThreeBand_scaledHighNet244 nu k (6 * nu * k) := by
  have hA : 0 < 6 * nu * k := by positivity
  apply (thirdFullThreeBand_scaledHighNet_positive_iff244
    nu k (6 * nu * k) hk hA).2
  have hnk : 0 < nu * k := mul_pos hnu hk
  nlinarith

/-- The physical Hermitian partners double, but do not change, the threshold. -/
def thirdFullThreeBand_scaledHighPairNet244 (nu k A : ℝ) : ℝ :=
  2 * thirdFullThreeBand_scaledHighNet244 nu k A

theorem thirdFullThreeBand_scaledHighPairNet_formula244
    (nu k A : ℝ) :
    thirdFullThreeBand_scaledHighPairNet244 nu k A =
      4 * k * A ^ 2 * (A - 5 * nu * k) := by
  rw [thirdFullThreeBand_scaledHighPairNet244,
    thirdFullThreeBand_scaledHighNet_formula244]
  ring

end
end PrimeTensor.FirstMonomialTriad
