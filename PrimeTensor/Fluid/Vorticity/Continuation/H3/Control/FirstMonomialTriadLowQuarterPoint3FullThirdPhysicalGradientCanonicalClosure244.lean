import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientPoint3TripleBridge244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientIntegrability244
import Mathlib.Tactic

/-!
# Actual physical H³ gradient = canonical 972-term Schwartz gradient completion

The previous checkpoint proved each genuine three-factor 3–3–1 Schwartz
integral tends to the corresponding OLD physical Point3 Lebesgue integral.
This closes the remaining nonlinear limit problem:

* Four oriented 3–3–1 triple integrals reconstruct the original old
  `spatialEnergyPairing` of one physical gradient-axis block, with factor 2.
* The three contraction axes and four derivative/component axes are summed
  with their original ordering and without any infinite-sum interchange.
* Every matched real Schwartz gradient tends to the old physical gradient
  scalar; uniqueness identifies that scalar with the canonical weighted
  spectral-H³ gradient completion.
* The already-closed signed 243-slot channel then supplies the full-third
  physical/canonical identity under the original PDE decomposition.

Only the existing Fourier-compatible genuine NS slice, old H³ data and
physical H³ energy path assumptions appear. No physical Schwartz realization,
third-derivative L⁴ assumption, or new nonlinear limit hypothesis is added.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeGradientCanonicalClosure244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceGradientCanonicalClosure244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exactly four physically oriented third-third-first gradient densities
at the ordered (j,i,k,l,r) gradient commutator slot. -/
noncomputable def h3PhysicalGradientFourTripleSum244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (j i k l r : A3) : ℝ :=
  let jj := h3ClassicalizationFinOfAxis j
  let rr := h3ClassicalizationFinOfAxis r
  2 * (∫ x : Point3,
    h3OldPhysicalGradientTripleDensity244 u t jj rr jj i k l i k l r x) +
  2 * (∫ x : Point3,
    h3OldPhysicalGradientTripleDensity244 u t jj jj rr i k l i k r l x) +
  2 * (∫ x : Point3,
    h3OldPhysicalGradientTripleDensity244 u t jj jj rr i k l i r l k x) +
  2 * (∫ x : Point3,
    h3OldPhysicalGradientTripleDensity244 u t jj jj rr i k l r k l i x)

/-- One ORIGINAL physical gradient-axis energy pairing equals the four
physical 3–3–1 integrals. The actual triple-integrability theorem,
not integrability of their sum, justifies every application of integral_add. -/
theorem h3PhysicalGradientAxis_eq_fourTriples244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j i k l r : A3) :
    spatialEnergyPairing
      (spatial3.d i (spatial3.d k (spatial3.d l
        (loggedVelocityComponent u t j))))
      (thirdTransportCommutatorAxisGradientBlock
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r) =
    h3PhysicalGradientFourTripleSum244 u t j i k l r := by
  let jj : Fin 3 := h3ClassicalizationFinOfAxis j
  let rr : Fin 3 := h3ClassicalizationFinOfAxis r
  let Q₁ : Point3 → ℝ :=
    h3OldPhysicalGradientTripleDensity244 u t jj rr jj i k l i k l r
  let Q₂ : Point3 → ℝ :=
    h3OldPhysicalGradientTripleDensity244 u t jj jj rr i k l i k r l
  let Q₃ : Point3 → ℝ :=
    h3OldPhysicalGradientTripleDensity244 u t jj jj rr i k l i r l k
  let Q₄ : Point3 → ℝ :=
    h3OldPhysicalGradientTripleDensity244 u t jj jj rr i k l r k l i
  -- The physical integrability theorem uses private jet abbreviations from
  -- an imported module. `simp only` cannot unfold those private names;
  -- make their *actual* derivative meaning explicit first.
  have hPhysicalTriple
      (j₀ p₀ q₀ a b c d e f r₀ : A3) :
      Integrable (h3OldPhysicalGradientTripleDensity244 u t
        (h3ClassicalizationFinOfAxis j₀)
        (h3ClassicalizationFinOfAxis p₀)
        (h3ClassicalizationFinOfAxis q₀) a b c d e f r₀)
        (volume : Measure Point3) := by
    have h := h3ActualPhysicalGradientTriple_integrable244 hNS ht hFourier
      j₀ p₀ q₀ a b c d e f r₀
    change Integrable (fun x : Point3 =>
      (spatial3.d a (spatial3.d b (spatial3.d c
        (loggedVelocityComponent u t j₀)))) x *
        ((spatial3.d d (spatial3.d e (spatial3.d f
          (loggedVelocityComponent u t p₀)))) x *
         (spatial3.d r₀ (loggedVelocityComponent u t q₀)) x))
        (volume : Measure Point3) at h
    -- First identify the old physical density as an actual function.
    -- Rewriting the function equality avoids asking `simpa` to normalize
    -- the opaque density while elaborating `Integrable`.
    have hDensity :
        h3OldPhysicalGradientTripleDensity244 u t
          (h3ClassicalizationFinOfAxis j₀)
          (h3ClassicalizationFinOfAxis p₀)
          (h3ClassicalizationFinOfAxis q₀) a b c d e f r₀ =
        (fun x : Point3 =>
          (spatial3.d a (spatial3.d b (spatial3.d c
            (loggedVelocityComponent u t j₀)))) x *
            ((spatial3.d d (spatial3.d e (spatial3.d f
              (loggedVelocityComponent u t p₀)))) x *
             (spatial3.d r₀ (loggedVelocityComponent u t q₀)) x)) := by
      funext x
      dsimp only [h3OldPhysicalGradientTripleDensity244]
      simp only [h3AxisOfFin3_h3ClassicalizationFinOfAxis]
    rw [hDensity]
    exact h
  have h₁ : Integrable Q₁ :=
    hPhysicalTriple j r j i k l i k l r
  have h₂ : Integrable Q₂ :=
    hPhysicalTriple j j r i k l i k r l
  have h₃ : Integrable Q₃ :=
    hPhysicalTriple j j r i k l i r l k
  have h₄ : Integrable Q₄ :=
    hPhysicalTriple j j r i k l r k l i
  have hComponent (q : A3) :
      (fun x : Point3 =>
        (PrimeTensor.Bridge.logSpaceTimeVectorField u t x).component q) =
      loggedVelocityComponent u t q := rfl
  have hDensity :
      (fun x : Point3 =>
        (spatial3.d i (spatial3.d k (spatial3.d l
          (loggedVelocityComponent u t j)))) x *
        (thirdTransportCommutatorAxisGradientBlock
          (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r) x) =
      (fun x : Point3 => Q₁ x + (Q₂ x + (Q₃ x + Q₄ x))) := by
    funext x
    simp only [thirdTransportCommutatorAxisGradientBlock]
    rw [hComponent j, hComponent r]
    dsimp only [Q₁, Q₂, Q₃, Q₄, jj, rr,
      h3OldPhysicalGradientTripleDensity244]
    simp only [h3AxisOfFin3_h3ClassicalizationFinOfAxis]
    ring
  have h12 := integral_add h₁ (h₂.add (h₃.add h₄))
  have h23 := integral_add h₂ (h₃.add h₄)
  have h34 := integral_add h₃ h₄
  simp only [Pi.add_apply] at h12 h23 h34
  calc
    spatialEnergyPairing
      (spatial3.d i (spatial3.d k (spatial3.d l
        (loggedVelocityComponent u t j))))
      (thirdTransportCommutatorAxisGradientBlock
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r) =
        2 * (∫ x : Point3, Q₁ x + (Q₂ x + (Q₃ x + Q₄ x))) := by
          unfold spatialEnergyPairing
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          exact congrFun hDensity x
    _ = 2 * ((∫ x : Point3, Q₁ x) +
        ((∫ x : Point3, Q₂ x) +
          ((∫ x : Point3, Q₃ x) + (∫ x : Point3, Q₄ x)))) := by
          congr 1
          calc
            (∫ x : Point3, Q₁ x + (Q₂ x + (Q₃ x + Q₄ x))) =
                (∫ x : Point3, Q₁ x) +
                  (∫ x : Point3, Q₂ x + (Q₃ x + Q₄ x)) := h12
            _ = (∫ x : Point3, Q₁ x) +
                  ((∫ x : Point3, Q₂ x) +
                    (∫ x : Point3, Q₃ x + Q₄ x)) := by rw [h23]
            _ = _ := by rw [h34]
    _ = h3PhysicalGradientFourTripleSum244 u t j i k l r := by
          dsimp only [h3PhysicalGradientFourTripleSum244, Q₁, Q₂, Q₃, Q₄,
            jj, rr]
          ring

/-- The FOUR strong 2–2–infinity Schwartz limits converge to the actual
OLD physical axis pairing, retaining factor 2 on every gradient orientation. -/
theorem h3MatchedSchwartz_gradientAxis_tendsto_oldPhysical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier))
    (j i k l r : A3) :
    Tendsto (fun n => fullSchwartzGradientAxis244
        (F.family.approximants n) j i k l r) atTop
      (𝓝 (spatialEnergyPairing
        (spatial3.d i (spatial3.d k (spatial3.d l
          (loggedVelocityComponent u t j))))
        (thirdTransportCommutatorAxisGradientBlock
          (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r))) := by
  have h1 := h3MatchedSchwartz_fullGradientTriple_tendsto_oldPhysical244
    hNS ht hFourier F
    (h3ClassicalizationFinOfAxis j) (h3ClassicalizationFinOfAxis r)
    (h3ClassicalizationFinOfAxis j) i k l i k l r
  have h2 := h3MatchedSchwartz_fullGradientTriple_tendsto_oldPhysical244
    hNS ht hFourier F
    (h3ClassicalizationFinOfAxis j) (h3ClassicalizationFinOfAxis j)
    (h3ClassicalizationFinOfAxis r) i k l i k r l
  have h3 := h3MatchedSchwartz_fullGradientTriple_tendsto_oldPhysical244
    hNS ht hFourier F
    (h3ClassicalizationFinOfAxis j) (h3ClassicalizationFinOfAxis j)
    (h3ClassicalizationFinOfAxis r) i k l i r l k
  have h4 := h3MatchedSchwartz_fullGradientTriple_tendsto_oldPhysical244
    hNS ht hFourier F
    (h3ClassicalizationFinOfAxis j) (h3ClassicalizationFinOfAxis j)
    (h3ClassicalizationFinOfAxis r) i k l r k l i
  have hAll := ((h1.add h2).add h3).add h4
  rw [h3PhysicalGradientAxis_eq_fourTriples244 hNS ht hFourier]
  -- The two fourfold expressions have the same derivative order, slot
  -- ordering, and association. Only axis<->Fin coordinate decoding differs.
  simpa only [fullSchwartzGradientAxis244,
    h3PhysicalGradientFourTripleSum244,
    h3AxisOfFin3_h3ClassicalizationFinOfAxis] using hAll

/-- The old physical r-axis gradient integral is linear in its gradient
block. The three terms are separately integrable, by the new actual physical
L²–L²–L∞ gradient-axis theorem. -/
theorem h3PhysicalGradient_sumAxisPairing244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j i k l : A3) :
    spatialEnergyPairing
      (spatial3.d i (spatial3.d k (spatial3.d l
        (loggedVelocityComponent u t j))))
      (thirdTransportCommutatorGradientBlock
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j) =
      ∑ r : A3, spatialEnergyPairing
        (spatial3.d i (spatial3.d k (spatial3.d l
          (loggedVelocityComponent u t j))))
        (thirdTransportCommutatorAxisGradientBlock
          (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r) := by
  let Q : Point3 → ℝ :=
    spatial3.d i (spatial3.d k (spatial3.d l
      (loggedVelocityComponent u t j)))
  let B : A3 → Point3 → ℝ := fun r =>
    thirdTransportCommutatorAxisGradientBlock
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r
  have hAxes := h3ActualPhysicalGradientAxesIntegrable244 hNS ht hFourier
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
  -- Normalize BOTH sides to the local abbreviations. The previous
  -- wildcard `change` left the RHS expanded and `simp` did not reduce Q/B.
  change spatialEnergyPairing Q
    (fun x => B xAxis x + (B yAxis x + B zAxis x)) =
    ∑ r : A3, spatialEnergyPairing Q (B r)
  simpa only [axis_sum_three] using hSplit

/-- A finite real sum preserves scalar sequential limits. -/
private theorem h3GradientFiniteSum_tendsto244
    {J : Type*} [Fintype J]
    (f : ℕ → J → ℝ) (g : J → ℝ)
    (h : ∀ p : J, Tendsto (fun n => f n p) atTop (𝓝 (g p))) :
    Tendsto (fun n => ∑ p : J, f n p) atTop
      (𝓝 (∑ p : J, g p)) := by
  classical
  have hs (S : Finset J) :
      Tendsto (fun n => Finset.sum S (f n)) atTop
        (𝓝 (Finset.sum S g)) := by
    induction S using Finset.induction_on with
    | empty =>
        simpa using (tendsto_const_nhds : Tendsto
          (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | @insert p S hp ih =>
        simpa only [Finset.sum_insert hp] using (h p).add ih
  exact hs (Finset.univ : Finset J)

/-- Finite, completely ordered five-axis summation preserves limits of
signed physical gradient pairings. There is no interchange of infinite
integrals and sums in this argument. -/
private theorem h3GradientFiniteFiveSum_tendsto244
    (f : ℕ → A3 → A3 → A3 → A3 → A3 → ℝ)
    (g : A3 → A3 → A3 → A3 → A3 → ℝ)
    (h : ∀ j i k l r : A3,
      Tendsto (fun n => f n j i k l r) atTop (𝓝 (g j i k l r))) :
    Tendsto (fun n => ∑ j : A3, ∑ i : A3, ∑ k : A3,
      ∑ l : A3, ∑ r : A3, f n j i k l r) atTop
      (𝓝 (∑ j : A3, ∑ i : A3, ∑ k : A3,
        ∑ l : A3, ∑ r : A3, g j i k l r)) := by
  have hR (j i k l : A3) :=
    h3GradientFiniteSum_tendsto244
      (fun n r => f n j i k l r) (fun r => g j i k l r)
      (fun r => h j i k l r)
  have hL (j i k : A3) :=
    h3GradientFiniteSum_tendsto244
      (fun n l => ∑ r : A3, f n j i k l r)
      (fun l => ∑ r : A3, g j i k l r) (hR j i k)
  have hK (j i : A3) :=
    h3GradientFiniteSum_tendsto244
      (fun n k => ∑ l : A3, ∑ r : A3, f n j i k l r)
      (fun k => ∑ l : A3, ∑ r : A3, g j i k l r) (hL j i)
  have hI (j : A3) :=
    h3GradientFiniteSum_tendsto244
      (fun n i => ∑ k : A3, ∑ l : A3, ∑ r : A3, f n j i k l r)
      (fun i => ∑ k : A3, ∑ l : A3, ∑ r : A3, g j i k l r) (hK j)
  exact h3GradientFiniteSum_tendsto244
    (fun n j => ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
      f n j i k l r)
    (fun j => ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
      g j i k l r) hI

/-- The SAME matched real Schwartz family converges in its complete
972-term gradient scalar to the original OLD spatial gradient transport,
without a physical Schwartz-realization or extra nonlinear trace premise. -/
theorem h3MatchedSchwartz_gradientTransport_tendsto_oldPhysical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier)) :
    Tendsto (fun n => fullSchwartzGradientTransport244
      (F.family.approximants n)) atTop
      (𝓝 (thirdOrderGradientTransportSum u t)) := by
  let P : A3 → A3 → A3 → A3 → A3 → ℝ := fun j i k l r =>
    spatialEnergyPairing
      (spatial3.d i (spatial3.d k (spatial3.d l
        (loggedVelocityComponent u t j))))
      (thirdTransportCommutatorAxisGradientBlock
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r)
  have hSlots := h3GradientFiniteFiveSum_tendsto244
    (fun n j i k l r => fullSchwartzGradientAxis244
      (F.family.approximants n) j i k l r) P
    (fun j i k l r =>
      h3MatchedSchwartz_gradientAxis_tendsto_oldPhysical244
        hNS ht hFourier F j i k l r)
  have hPhysicalSum :
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
        ∑ r : A3, P j i k l r) = thirdOrderGradientTransportSum u t := by
    unfold thirdOrderGradientTransportSum
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    exact (h3PhysicalGradient_sumAxisPairing244 hNS ht hFourier j i k l).symm
  rw [hPhysicalSum] at hSlots
  change Tendsto (fun n => fullSchwartzGradientTransport244
    (F.family.approximants n)) atTop
    (𝓝 (thirdOrderGradientTransportSum u t)) at hSlots
  exact hSlots

/-- The LAST independent analytic identification of the weighted spectral
third-order gradient completion with the genuine old physical Navier–Stokes
H³ gradient transport. No approximation hypotheses beyond Fourier-compatible
H³ and admissibility are introduced. -/
theorem h3PhysicalGradient_eq_weightedCanonical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    thirdOrderGradientTransportSum u t =
      weightedH3CanonicalGradientTransport244
        (velocityH3SpectralStateAt u t hInt hMeas hFourier) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  let F : H3MatchedSchwartzGradientCompletion244 U :=
    Classical.choice (exists_h3MatchedSchwartzGradientCompletion244 U)
  have hPhysical := h3MatchedSchwartz_gradientTransport_tendsto_oldPhysical244
    hNS ht hFourier F
  have hCanonical := weightedH3CanonicalGradientTransport_tendsto244 U F
  exact tendsto_nhds_unique hPhysical hCanonical

/-- Complete physical/canonical H³ top commutator equality: the signed
3–2–2 discrepancy was already closed, and the genuine 3–3–1 physical
pairing has now been identified with its canonical Schwartz completion.
This concerns the *top-order transport functional*, not automatically
smooth continuation or a global Navier–Stokes regularity result. -/
theorem h3PhysicalFullThird_eq_weightedCanonical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (htNS : t ∈ Set.Ioo (0 : ℝ) T)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3TransportDerivative3At u t =
      h3PhysicalSnapshotCanonicalFullThird244 u t hFourier := by
  apply (h3PhysicalFullThird_eq_canonical_iff_gradient_eq244
    hH3 hClass ht hFourier).2
  exact h3PhysicalGradient_eq_weightedCanonical244 hNS htNS hFourier

end
end PrimeTensor.FirstMonomialTriad
