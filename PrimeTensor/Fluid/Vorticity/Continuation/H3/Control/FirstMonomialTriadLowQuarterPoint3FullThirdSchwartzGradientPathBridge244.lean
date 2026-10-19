import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdUnforcedSignFrontier244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzPhysicalPathCriticalHalf244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadPhysicalTransport
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Closure
import Mathlib.Tactic

/-!
# Actual physical path / real Schwartz gradient bridge at third order

For a real Schwartz realization of an actual Navier--Stokes time slice,
identify the original physical four-slot `3+3+1` gradient block, including
its energy-pairing factor TWO, with the four literal Schwartz triple
integrals. The complete axis and multi-index sum then coincides with
`fullSchwartzGradientTransport244`.

The only extra integration contract is the integrability of each individual
split gradient-axis pairing, not a new PDE or numerical bound. It is stated
separately because integrability of a sum does not imply integrability of its
summands. The preexisting energy class and realization hypotheses stay visible.

Finally we combine the existing exact interpolation identity to identify the
TOP-ORDER `velocityH3TransportDerivative3At` with the entire signed Schwartz
`G3+3M` functional. Lower orders and actual-solution realization are not
claimed without hypotheses.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdSchwartzGradientPath244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

private abbrev firstGradientJet244 (f : A3 → SchwartzMap V3 ℝ)
    (j r : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection r} (f j)

private abbrev thirdGradientJet244 (f : A3 → SchwartzMap V3 ℝ)
    (j i k l : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection k}
      (∂_{h3FourierAxisDirection l} (f j)))

/-- All three factors are actual Schwartz functions, so a product of their
values has an ordinary Lebesgue integral. This is independent of the PDE. -/
theorem thirdFullRealSchwartz_threeProduct_integrable244
    (F G H : SchwartzMap V3 ℝ) :
    Integrable (fun y : V3 => F y * (G y * H y)) := by
  exact (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) F
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) G H)).integrable

/-- Real-linear distribution of the complete four-slot axis integral;
all integrability hypotheses are discharged by Schwartz products. -/
theorem thirdFullRealSchwartz_fourGradientIntegral244
    (F G₁ H₁ G₂ H₂ G₃ H₃ G₄ H₄ : SchwartzMap V3 ℝ) :
    2 * (∫ y : V3, F y *
      (G₁ y * H₁ y + (G₂ y * H₂ y +
        (G₃ y * H₃ y + G₄ y * H₄ y)))) =
      fullGradientTriple244 F G₁ H₁ +
        fullGradientTriple244 F G₂ H₂ +
        fullGradientTriple244 F G₃ H₃ +
        fullGradientTriple244 F G₄ H₄ := by
  let Q₁ : V3 → ℝ := fun y => F y * (G₁ y * H₁ y)
  let Q₂ : V3 → ℝ := fun y => F y * (G₂ y * H₂ y)
  let Q₃ : V3 → ℝ := fun y => F y * (G₃ y * H₃ y)
  let Q₄ : V3 → ℝ := fun y => F y * (G₄ y * H₄ y)
  have h₁ : Integrable Q₁ := thirdFullRealSchwartz_threeProduct_integrable244 F G₁ H₁
  have h₂ : Integrable Q₂ := thirdFullRealSchwartz_threeProduct_integrable244 F G₂ H₂
  have h₃ : Integrable Q₃ := thirdFullRealSchwartz_threeProduct_integrable244 F G₃ H₃
  have h₄ : Integrable Q₄ := thirdFullRealSchwartz_threeProduct_integrable244 F G₄ H₄
  calc
    _ = 2 * (∫ y : V3, Q₁ y + (Q₂ y + (Q₃ y + Q₄ y))) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      dsimp [Q₁, Q₂, Q₃, Q₄]
      ring
    _ = 2 * ((∫ y : V3, Q₁ y) +
        ((∫ y : V3, Q₂ y) + ((∫ y : V3, Q₃ y) +
          (∫ y : V3, Q₄ y)))) := by
      -- `integral_add` is expressed using pointwise function addition.
      -- Normalize its statement to the actual binder-shaped integrands
      -- before rewriting; `rw [integral_add ...]` does not match the raw
      -- nested lambda syntax in this version of Mathlib.
      have h12 := integral_add h₁ (h₂.add (h₃.add h₄))
      have h23 := integral_add h₂ (h₃.add h₄)
      have h34 := integral_add h₃ h₄
      simp only [Pi.add_apply] at h12 h23 h34
      congr 1
      calc
        (∫ y : V3, Q₁ y + (Q₂ y + (Q₃ y + Q₄ y))) =
            (∫ y : V3, Q₁ y) +
              (∫ y : V3, Q₂ y + (Q₃ y + Q₄ y)) := h12
        _ = (∫ y : V3, Q₁ y) +
              ((∫ y : V3, Q₂ y) +
                (∫ y : V3, Q₃ y + Q₄ y)) := by rw [h23]
        _ = _ := by rw [h34]
    _ = _ := by
      dsimp [Q₁, Q₂, Q₃, Q₄, fullGradientTriple244]
      ring

/-- At a realized physical Schwartz slice, the *actual* four-term
`D³u · Du` axis pairing is the identical four-term, seven-derivative
Schwartz coefficient. No Navier--Stokes equation is used in this identity. -/
theorem thirdFullRealSchwartz_pathGradientAxis_eq244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (j i k l r : A3) :
    spatialEnergyPairing
      (spatial3.d i (spatial3.d k (spatial3.d l
        (loggedVelocityComponent u t j))))
      (thirdTransportCommutatorAxisGradientBlock
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r) =
      fullSchwartzGradientAxis244 f j i k l r := by
  let F : SchwartzMap V3 ℝ := thirdGradientJet244 f j i k l
  let G₁ : SchwartzMap V3 ℝ := thirdGradientJet244 f r i k l
  let H₁ : SchwartzMap V3 ℝ := firstGradientJet244 f j r
  let G₂ : SchwartzMap V3 ℝ := thirdGradientJet244 f j i k r
  let H₂ : SchwartzMap V3 ℝ := firstGradientJet244 f r l
  let G₃ : SchwartzMap V3 ℝ := thirdGradientJet244 f j i r l
  let H₃ : SchwartzMap V3 ℝ := firstGradientJet244 f r k
  let G₄ : SchwartzMap V3 ℝ := thirdGradientJet244 f j r k l
  let H₄ : SchwartzMap V3 ℝ := firstGradientJet244 f r i
  have hComponent : ∀ q : A3,
      (fun x : Point3 => (PrimeTensor.Bridge.logSpaceTimeVectorField u t x).component q) =
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
    -- The original gradient block orders the factors as H₂*G₂,
    -- H₃*G₃, H₄*G₄, whereas the named Schwartz block writes G₂*H₂,
    -- G₃*H₃, G₄*H₄.  Expand the physical pullback and the local jet
    -- abbreviations on BOTH sides, then let commutative algebra reorder.
    simp only [h3SchwartzPoint3Scalar]
    dsimp only [G₁, H₁, G₂, H₂, G₃, H₃, G₄, H₄,
      thirdGradientJet244, firstGradientJet244]
    ring
  calc
    _ = 2 * (∫ y : V3, F y *
        (G₁ y * H₁ y + (G₂ y * H₂ y +
          (G₃ y * H₃ y + G₄ y * H₄ y)))) := by
      rw [hTop, hBlock]
      change 2 * (∫ x : Point3,
        (fun y : V3 => F y *
          (G₁ y * H₁ y + (G₂ y * H₂ y +
            (G₃ y * H₃ y + G₄ y * H₄ y)))) (h3Point3ToFourierCLM x)) = _
      exact congrArg (fun v : ℝ => 2 * v)
        (h3Point3ToFourier_integral (fun y : V3 =>
          F y * (G₁ y * H₁ y + (G₂ y * H₂ y +
            (G₃ y * H₃ y + G₄ y * H₄ y)))))
    _ = fullGradientTriple244 F G₁ H₁ +
          fullGradientTriple244 F G₂ H₂ +
          fullGradientTriple244 F G₃ H₃ +
          fullGradientTriple244 F G₄ H₄ :=
      thirdFullRealSchwartz_fourGradientIntegral244 F G₁ H₁ G₂ H₂ G₃ H₃ G₄ H₄
    _ = fullSchwartzGradientAxis244 f j i k l r := by
      rfl

/-- Precisely the extra measure-theoretic contract needed to split each
sum of three gradient-axis pairings in an actual time slice. The preceding
axis formula identifies each term with Schwartz data; the contract does not
assume the desired equality or transport sign. -/
def H3RealSchwartzGradientAxesIntegrable244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : Prop :=
  ∀ j i k l r : A3,
    Integrable (fun x : Point3 =>
      (spatial3.d i (spatial3.d k (spatial3.d l
        (loggedVelocityComponent u t j)))) x *
      (thirdTransportCommutatorAxisGradientBlock
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r) x)

/-- The complete actual third-order physical gradient transport equals
its 243-slot Schwartz analogue on a real Schwartz slice, assuming only the
split axis pairing integrability needed for finite-sum integration. -/
theorem thirdFullRealSchwartz_pathGradientTotal_eq244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hAxes : H3RealSchwartzGradientAxesIntegrable244 u t) :
    thirdOrderGradientTransportSum u t = fullSchwartzGradientTransport244 f := by
  have hAxis (j i k l : A3) :
      spatialEnergyPairing
        (spatial3.d i (spatial3.d k (spatial3.d l
          (loggedVelocityComponent u t j))))
        (thirdTransportCommutatorGradientBlock
          (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j) =
      ∑ r : A3, fullSchwartzGradientAxis244 f j i k l r := by
    let Q : Point3 → ℝ := spatial3.d i (spatial3.d k (spatial3.d l
      (loggedVelocityComponent u t j)))
    let B : A3 → Point3 → ℝ := fun r =>
      thirdTransportCommutatorAxisGradientBlock
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r
    have hI (r : A3) : Integrable (fun x : Point3 => Q x * B r x) :=
      hAxes j i k l r
    have hSplit :
        spatialEnergyPairing Q (fun x => B xAxis x + (B yAxis x + B zAxis x)) =
        spatialEnergyPairing Q (B xAxis) +
          (spatialEnergyPairing Q (B yAxis) + spatialEnergyPairing Q (B zAxis)) := by
      unfold spatialEnergyPairing
      calc
        _ = 2 * (∫ x : Point3,
          Q x * B xAxis x + (Q x * B yAxis x + Q x * B zAxis x)) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          ring
        _ = 2 * ((∫ x : Point3, Q x * B xAxis x) +
          ((∫ x : Point3, Q x * B yAxis x) +
            (∫ x : Point3, Q x * B zAxis x))) := by
          have hXY := integral_add (hI xAxis) ((hI yAxis).add (hI zAxis))
          have hYZ := integral_add (hI yAxis) (hI zAxis)
          simp only [Pi.add_apply] at hXY hYZ
          congr 1
          calc
            (∫ x : Point3,
              Q x * B xAxis x + (Q x * B yAxis x + Q x * B zAxis x)) =
                (∫ x : Point3, Q x * B xAxis x) +
                  (∫ x : Point3, Q x * B yAxis x + Q x * B zAxis x) := hXY
            _ = _ := by rw [hYZ]
        _ = _ := by ring
    change spatialEnergyPairing Q
        (fun x => B xAxis x + (B yAxis x + B zAxis x)) = _
    rw [hSplit]
    simp only [axis_sum_three]
    rw [thirdFullRealSchwartz_pathGradientAxis_eq244 u t f hRealization j i k l xAxis,
      thirdFullRealSchwartz_pathGradientAxis_eq244 u t f hRealization j i k l yAxis,
      thirdFullRealSchwartz_pathGradientAxis_eq244 u t f hRealization j i k l zAxis]
  unfold thirdOrderGradientTransportSum fullSchwartzGradientTransport244
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  exact hAxis j i k l

/-- The full TOP-ORDER physical unforced NS transport of a Schwartz-realized
admissible time slice is precisely `G3(f)+3M(f)`. The PDE is used only for
the canonical exact commutator split, not to fabricate a solution. -/
theorem h3Path_fullThirdTransport_eq_realSchwartz244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hAxes : H3RealSchwartzGradientAxesIntegrable244 u t) :
    velocityH3TransportDerivative3At u t = fullSchwartzThirdCommutator244 f := by
  have hSplit := h3PathCanonical_thirdTransport_eq_gradient_add_interpolation
    hH3 hClass ht
  rw [hSplit, thirdFullRealSchwartz_pathGradientTotal_eq244
    u t f hRealization hAxes,
    lowNormalRealSchwartz_pathInterpolation_eq_three_schwartz244
      hH3 hClass ht f hRealization]
  rfl

end
end PrimeTensor.FirstMonomialTriad
