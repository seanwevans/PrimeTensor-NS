import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientPathBridge244
import Mathlib.Tactic

/-!
# Automatic gradient-axis integrability for every Schwartz-realized H3 slice

The full-third gradient bridge established exact identity for every one of the
four physical 3+3+1 gradient products, including the physical factor two,
and lifted the equality to the complete third-order transport using an explicit
`H3RealSchwartzGradientAxesIntegrable244` contract.

This module derives that contract from the existing real Schwartz realization.
The physical density is a sum of four genuine products of derivatives of
Schwartz functions. Such a sum is integrable on the Euclidean Fourier carrier;
`PiLp.volume_preserving_toLp` transports its integrability back to Point3.

This is a spatial regularity theorem. It does not assert that a particular
static Schwarz profile occurs at a time of an unforced Navier--Stokes solution.
The lower transport orders and the dynamic extension question remain separate.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdGradientIntegrability244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

private abbrev firstSchwartzJetInt244 (f : A3 → SchwartzMap V3 ℝ)
    (j r : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection r} (f j)

private abbrev thirdSchwartzJetInt244 (f : A3 → SchwartzMap V3 ℝ)
    (j i k l : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection k}
      (∂_{h3FourierAxisDirection l} (f j)))

/-- Each actual physical `D³u`/gradient-block density is integrable: its
four Schwartz triple products have integrable pullbacks under the *actual*
Point3-to-Euclidean volume preserving map. No PDE hypotheses are required. -/
theorem thirdFullRealSchwartz_gradientAxisDensity_integrable244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (j i k l r : A3) :
    Integrable (fun x : Point3 =>
      (spatial3.d i (spatial3.d k (spatial3.d l
        (loggedVelocityComponent u t j)))) x *
      (thirdTransportCommutatorAxisGradientBlock
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r) x) := by
  let F : SchwartzMap V3 ℝ := thirdSchwartzJetInt244 f j i k l
  let G₁ : SchwartzMap V3 ℝ := thirdSchwartzJetInt244 f r i k l
  let H₁ : SchwartzMap V3 ℝ := firstSchwartzJetInt244 f j r
  let G₂ : SchwartzMap V3 ℝ := thirdSchwartzJetInt244 f j i k r
  let H₂ : SchwartzMap V3 ℝ := firstSchwartzJetInt244 f r l
  let G₃ : SchwartzMap V3 ℝ := thirdSchwartzJetInt244 f j i r l
  let H₃ : SchwartzMap V3 ℝ := firstSchwartzJetInt244 f r k
  let G₄ : SchwartzMap V3 ℝ := thirdSchwartzJetInt244 f j r k l
  let H₄ : SchwartzMap V3 ℝ := firstSchwartzJetInt244 f r i
  have hComponent : ∀ q : A3,
      (fun x : Point3 =>
        (PrimeTensor.Bridge.logSpaceTimeVectorField u t x).component q) =
        loggedVelocityComponent u t q := by
    intro q
    rfl
  have hTop :
      spatial3.d i (spatial3.d k (spatial3.d l
        (loggedVelocityComponent u t j))) = h3SchwartzPoint3Scalar F := by
    rw [hRealization j]
    simp only [h3SchwartzPoint3Scalar_spatial_d]
    rfl
  have hBlock :
      thirdTransportCommutatorAxisGradientBlock
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r =
      (fun x : Point3 =>
        let y := h3Point3ToFourierCLM x
        G₁ y * H₁ y + (G₂ y * H₂ y + (G₃ y * H₃ y + G₄ y * H₄ y))) := by
    funext x
    simp only [thirdTransportCommutatorAxisGradientBlock]
    rw [hComponent j, hComponent r]
    simp only [hRealization j, hRealization r,
      h3SchwartzPoint3Scalar_spatial_d]
    simp only [h3SchwartzPoint3Scalar]
    dsimp only [G₁, H₁, G₂, H₂, G₃, H₃, G₄, H₄,
      thirdSchwartzJetInt244, firstSchwartzJetInt244]
    ring
  have hDensity :
      (fun x : Point3 =>
        (spatial3.d i (spatial3.d k (spatial3.d l
          (loggedVelocityComponent u t j)))) x *
        (thirdTransportCommutatorAxisGradientBlock
          (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r) x) =
      (fun x : Point3 =>
        F (h3Point3ToFourierCLM x) *
          (G₁ (h3Point3ToFourierCLM x) * H₁ (h3Point3ToFourierCLM x) +
           (G₂ (h3Point3ToFourierCLM x) * H₂ (h3Point3ToFourierCLM x) +
            (G₃ (h3Point3ToFourierCLM x) * H₃ (h3Point3ToFourierCLM x) +
             G₄ (h3Point3ToFourierCLM x) * H₄ (h3Point3ToFourierCLM x))))) := by
    funext x
    rw [hTop, hBlock]
    rfl
  have h₁ : Integrable (fun y : V3 => F y * (G₁ y * H₁ y)) :=
    thirdFullRealSchwartz_threeProduct_integrable244 F G₁ H₁
  have h₂ : Integrable (fun y : V3 => F y * (G₂ y * H₂ y)) :=
    thirdFullRealSchwartz_threeProduct_integrable244 F G₂ H₂
  have h₃ : Integrable (fun y : V3 => F y * (G₃ y * H₃ y)) :=
    thirdFullRealSchwartz_threeProduct_integrable244 F G₃ H₃
  have h₄ : Integrable (fun y : V3 => F y * (G₄ y * H₄ y)) :=
    thirdFullRealSchwartz_threeProduct_integrable244 F G₄ H₄
  have hCarrier : Integrable (fun y : V3 => F y *
      (G₁ y * H₁ y + (G₂ y * H₂ y +
        (G₃ y * H₃ y + G₄ y * H₄ y)))) := by
    have hSum :
        (fun y : V3 => F y *
          (G₁ y * H₁ y + (G₂ y * H₂ y +
            (G₃ y * H₃ y + G₄ y * H₄ y)))) =
        (fun y : V3 => F y * (G₁ y * H₁ y) +
          (F y * (G₂ y * H₂ y) +
            (F y * (G₃ y * H₃ y) + F y * (G₄ y * H₄ y)))) := by
      funext y
      ring
    rw [hSum]
    exact h₁.add (h₂.add (h₃.add h₄))
  change Integrable (fun x : Point3 =>
    (spatial3.d i (spatial3.d k (spatial3.d l
      (loggedVelocityComponent u t j)))) x *
    (thirdTransportCommutatorAxisGradientBlock
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r) x)
    (volume : Measure Point3)
  rw [hDensity]
  change Integrable
    ((fun y : V3 => F y *
      (G₁ y * H₁ y + (G₂ y * H₂ y +
        (G₃ y * H₃ y + G₄ y * H₄ y)))) ∘
      (WithLp.toLp 2 : Point3 → V3))
    (volume : Measure Point3)
  exact (PiLp.volume_preserving_toLp A3).integrable_comp_of_integrable hCarrier

/-- The explicit gradient-axis integrability contract is automatically
satisfied on every realized real Schwartz time slice. -/
theorem thirdFullRealSchwartz_gradientAxesIntegrable_of_realization244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    H3RealSchwartzGradientAxesIntegrable244 u t := by
  intro j i k l r
  exact thirdFullRealSchwartz_gradientAxisDensity_integrable244
    u t f hRealization j i k l r

/-- The entire physical third-order gradient agrees with the actual real
Schwartz gradient, with no separate axis-integrability hypothesis. -/
theorem thirdFullRealSchwartz_pathGradientTotal_eq_of_realization244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    thirdOrderGradientTransportSum u t = fullSchwartzGradientTransport244 f := by
  exact thirdFullRealSchwartz_pathGradientTotal_eq244 u t f hRealization
    (thirdFullRealSchwartz_gradientAxesIntegrable_of_realization244
      u t f hRealization)

/-- The *complete* top-order physical NS commutator is the full actual
Schwartz `G3 + 3M`. Only the existing H3 energy-class and actual slice
realization hypotheses remain: gradient-axis integrability is a theorem. -/
theorem h3Path_fullThirdTransport_eq_realSchwartz_of_realization244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    velocityH3TransportDerivative3At u t = fullSchwartzThirdCommutator244 f := by
  exact h3Path_fullThirdTransport_eq_realSchwartz244
    hH3 hClass ht f hRealization
    (thirdFullRealSchwartz_gradientAxesIntegrable_of_realization244
      u t f hRealization)

end
end PrimeTensor.FirstMonomialTriad
