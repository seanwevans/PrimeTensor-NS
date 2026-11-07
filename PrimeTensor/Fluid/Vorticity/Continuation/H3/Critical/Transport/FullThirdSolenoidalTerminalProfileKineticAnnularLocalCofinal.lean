import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSecondaryAnnularCutoffEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileAnnularPersistence
import Mathlib.Tactic

/-!
# Kinetic-only local annular PDE persistence without terminal H³ integrability

The earlier natural-annular charge uses finite H³ dissipation up to terminal
T in order to compare its finite-band integral against the full terminal
real integral. The PDE persistence and the finite-band integral themselves
need no such hypothesis. Here they are separated from terminal summability.

At any genuine high-radial snapshot above M, choose a finite natural outer
cutoff using fixed-time high-tail decay. Actual physical kinetic energy alone
controls the time modulus of the finite annular dissipation. The resulting
positive window has the explicit kinetic rate and pays an honest ordinary
real integral of the FINITE annulus, with no terminal-integrable full H³
rate and no attained full-H³ source/state maxima.

The previously proved unconditional-on-H³-integrability no-H³-trace
arbitrary-height diagonal now carries the same witnesses into this stronger
kinetic PDE window. No sum of potentially overlapping intervals is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Local physical finite-annulus PDE charge with all frequency and time
parameters explicit. Importantly, the charged integral is the ordinary real
finite-BAND integral: no full terminal H³ dissipation integrability occurs. -/
def ThirdFullKineticNaturalAnnularLocalWitness244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x : ℝ) (n N : ℕ) (M δ : ℝ) : Prop :=
  n ≤ N ∧
  0 < δ ∧
  δ = min ((T - x) / 4)
    ((M / 4) /
      (2 * (thirdFullPhysicalKineticLowBandDissipationRate244 N
              (velocityH3Energy0At u b) +
            thirdFullPhysicalKineticLowBandDissipationRate244 n
              (velocityH3Energy0At u b) + 1))) ∧
  x + δ < T ∧
  (∀ r : ℝ, r ∈ Set.Icc x (x + δ) →
    M / 4 <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r) ∧
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r) ≤
      velocityH3DissipationAt u r) ∧
  (let I : ℝ := ∫ r in x..(x + δ),
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r)
   δ * (M / 4) ≤ I ∧
     ((T - x) * (M / 2) ≤ 16 * I ∨
       (M / 2) ^ 2 ≤ 8 *
         (thirdFullPhysicalKineticLowBandDissipationRate244 N
              (velocityH3Energy0At u b) +
          thirdFullPhysicalKineticLowBandDissipationRate244 n
              (velocityH3Energy0At u b) + 1) * I))

/-- A genuine positive-time high-radial H³ dissipation snapshot has an
EXPLICIT kinetic-only annular PDE persistence radius and finite real annular
integral charge. No `IntervalIntegrable D a T` hypothesis, no terminal source
ceiling, and no high-order spectral time regularity are introduced. -/
theorem thirdFullPhysical_highRadialSnapshot_kineticLocalAnnularWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (n : ℕ) (M : ℝ) (hM : 0 < M)
    (hHigh : M < h3PathActualHighRadialDissipation244
      ((n : ℝ) + 1) (h3AuditActualSpectralVelocityTotal hH3 x)) :
    ∃ (N : ℕ) (δ : ℝ),
      ThirdFullKineticNaturalAnnularLocalWitness244 hH3 b x n N M δ := by
  let U : ℝ → H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3
  have hxClass : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hQuarter : 0 < M / 4 := by linarith only [hM]
  have hTail := h3Path_actualHighRadialDissipation_tendsto_zero_fixedTime244
    hH3 hClass x hxClass
  have hEvent : ∀ᶠ j : ℕ in atTop,
      h3PathActualHighRadialDissipation244 ((j : ℝ) + 1) (U x) < M / 4 :=
    hTail.eventually (eventually_lt_nhds hQuarter)
  rw [Filter.eventually_atTop] at hEvent
  obtain ⟨N₀, hN₀⟩ := hEvent
  let N : ℕ := max N₀ n
  have hnN : n ≤ N := le_max_right N₀ n
  have hN₀N : N₀ ≤ N := le_max_left N₀ n
  have hOuter :
      h3PathActualHighRadialDissipation244 ((N : ℝ) + 1) (U x) < M / 4 :=
    hN₀ N hN₀N
  have hPartInner := h3Path_actualRadialDissipation_partition244
    hH3 hClass x hxClass ((n : ℝ) + 1)
  have hPartOuter := h3Path_actualRadialDissipation_partition244
    hH3 hClass x hxClass ((N : ℝ) + 1)
  let Ann : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1) (U r) -
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1) (U r)
  have hPeak : 2 * (M / 4) < Ann x := by
    dsimp only [U, Ann] at hOuter hPartInner hPartOuter ⊢
    linarith only [hHigh, hOuter, hPartInner, hPartOuter, hM]
  let Λ : ℝ := thirdFullPhysicalKineticLowBandDissipationRate244 N
      (velocityH3Energy0At u b) +
    thirdFullPhysicalKineticLowBandDissipationRate244 n
      (velocityH3Energy0At u b)
  have hΛ : 0 ≤ Λ := add_nonneg
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 N _)
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 n _)
  have hd : 0 < (T - x) / 2 := by linarith only [hx.2]
  obtain ⟨δ, hδ, hδHalf, hδEq, hRate⟩ :=
    h3Critical_scalar_annularPDE_positivePersistenceRadius
      (M / 4) Λ ((T - x) / 2) hQuarter hΛ hd
  have hEnd : x + δ < T := by linarith only [hδHalf, hx.2]
  have hRadN : 0 ≤ (N : ℝ) + 1 := by positivity
  have hRadn : 0 ≤ (n : ℝ) + 1 := by positivity
  have hFloor (r : ℝ) (hr : r ∈ Set.Icc x (x + δ)) :
      M / 4 < Ann r := by
    have hrTail : r ∈ Set.Ioo b T :=
      ⟨lt_of_lt_of_le hx.1 hr.1, lt_of_le_of_lt hr.2 hEnd⟩
    have hVar := thirdFullPhysical_kineticNaturalAnnularDissipationLipschitz244
      hH3 hClass b hb n N x r hx hrTail hr.1
    change |Ann x - Ann r| ≤ Λ * (r - x) at hVar
    have hError : Ann x - Ann r ≤ Λ * (r - x) :=
      (le_abs_self (Ann x - Ann r)).trans hVar
    have hElapsed : r - x ≤ δ := by linarith only [hr.2]
    have hBound : Λ * (r - x) ≤ Λ * δ :=
      mul_le_mul_of_nonneg_left hElapsed hΛ
    linarith only [hError, hBound, hRate, hPeak]
  have hSub : Set.Icc x (x + δ) ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hxClass.1 hr.1, lt_of_le_of_lt hr.2 hEnd⟩
  have hFull (r : ℝ) (hr : r ∈ Set.Icc x (x + δ)) :
      Ann r ≤ velocityH3DissipationAt u r := by
    exact h3Path_actualFiniteAnnulusDissipation_le_fullAt244
      hH3 hClass r (hSub hr) ((n : ℝ) + 1) ((N : ℝ) + 1)
  have hCont : ContinuousOn Ann (Set.Ioo a T) :=
    h3Path_finiteAnnularDissipation_continuousOn244
      hH3 hClass ((n : ℝ) + 1) ((N : ℝ) + 1) hRadn hRadN
  have hAnnInt : IntervalIntegrable Ann volume x (x + δ) :=
    (hCont.mono hSub).intervalIntegrable_of_Icc
      (by linarith only [hδ])
  let I : ℝ := ∫ r in x..(x + δ), Ann r ∂volume
  have hCost : δ * (M / 4) ≤ I := by
    have hIntegral := h3Path_localPositiveHeight_forces_integratedCost244
      Ann x (x + δ) (M / 4) (by linarith only [hδ]) hAnnInt
      (fun r hr => (hFloor r hr).le)
    dsimp only [I]
    calc
      δ * (M / 4) = ((x + δ) - x) * (M / 4) := by ring
      _ ≤ ∫ r in x..(x + δ), Ann r ∂volume := hIntegral
  have hxMid : x ∈ Set.Icc x (x + (T - x) / 2) := by
    constructor
    · exact le_rfl
    · linarith only [hx.2]
  have hWidth : δ = min (((T - x) / 2) / 2)
      (((M / 2) / 2) / (2 * (Λ + 1))) := by
    simpa only [show ((T - x) / 2) / 2 = (T - x) / 4 by ring,
      show (M / 2) / 2 = M / 4 by ring] using hδEq
  have hFork := thirdFull_scalar_secondaryAnnularClockOrRate244
    T x x (M / 2) Λ δ I
    (by linarith only [hM]) hΛ hxMid hWidth
    (by simpa only [show (M / 2) / 2 = M / 4 by ring] using hCost)
  refine ⟨N, δ, hnN, hδ, ?_, hEnd, ?_, ?_⟩
  · simpa only [Λ,
      show ((T - x) / 2) / 2 = (T - x) / 4 by ring] using hδEq
  · intro r hr
    exact ⟨hFloor r hr, hFull r hr⟩
  · change δ * (M / 4) ≤ I ∧
      ((T - x) * (M / 2) ≤ 16 * I ∨
       (M / 2) ^ 2 ≤ 8 * (Λ + 1) * I)
    exact ⟨hCost, hFork⟩

/-- The ORIGINAL two attained secondary observations can carry this local
kinetic-only annular charge WITHOUT a terminal full-H³ dissipation integral.
Neither observation time is reselected when the lower frequency or height
is specified. In particular this theorem applies directly to the selected
high-radial branch of the previous cofinal ledger. -/
theorem thirdFullPhysical_secondaryTwoSlice_kineticLocalAnnularWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s zState zSource : ℝ) (hs : s ∈ Set.Ioo b T)
    (hzState : zState ∈ Set.Icc s (s + (T - s) / 2))
    (hzSource : zSource ∈ Set.Icc s (s + (T - s) / 2))
    (n : ℕ) (M : ℝ) (hM : 0 < M)
    (hHigh : M < h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 zState) ∨
      M < h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 zSource)) :
    ∃ (x : ℝ) (N : ℕ) (δ : ℝ),
      (x = zState ∨ x = zSource) ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b x n N M δ := by
  have hHalfEnd : s + (T - s) / 2 < T := by
    linarith only [hs.2]
  have hStateTime : zState ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le hs.1 hzState.1,
      lt_of_le_of_lt hzState.2 hHalfEnd⟩
  have hSourceTime : zSource ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le hs.1 hzSource.1,
      lt_of_le_of_lt hzSource.2 hHalfEnd⟩
  rcases hHigh with hState | hSource
  · obtain ⟨N, δ, hWitness⟩ :=
      thirdFullPhysical_highRadialSnapshot_kineticLocalAnnularWindow244
        hH3 hClass b hb zState hStateTime n M hM hState
    exact ⟨zState, N, δ, Or.inl rfl, hWitness⟩
  · obtain ⟨N, δ, hWitness⟩ :=
      thirdFullPhysical_highRadialSnapshot_kineticLocalAnnularWindow244
        hH3 hClass b hb zSource hSourceTime n M hM hSource
    exact ⟨zSource, N, δ, Or.inr rfl, hWitness⟩

/-- If a certified local annular charge cannot be explained by clock
compression and its finite-window integral is small relative to every
kinetic rate through n0, its ACTUAL outer cutoff exceeds n0. The local
integral replaces the earlier terminal full-H³ budget. -/
theorem thirdFullPhysical_kineticLocalAnnular_forces_outerEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x : ℝ) (n N n0 : ℕ) (M δ : ℝ)
    (hM : 0 < M)
    (hWindow : ThirdFullKineticNaturalAnnularLocalWitness244
      hH3 b x n N M δ)
    (hClock : 16 *
      (∫ r in x..(x + δ),
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r)) <
      (T - x) * (M / 2))
    (hSmall : 8 *
      ((∑ j ∈ Finset.range (n0 + 1),
          thirdFullPhysicalKineticLowBandDissipationRate244 j
            (velocityH3Energy0At u b)) +
        thirdFullPhysicalKineticLowBandDissipationRate244 n
          (velocityH3Energy0At u b) + 1) *
      (∫ r in x..(x + δ),
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r)) < (M / 2) ^ 2) :
    n0 < N := by
  let I : ℝ := ∫ r in x..(x + δ),
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 r) -
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 r)
  rcases hWindow with ⟨_hnN, hδ, _hδEq, _hEnd, _hFloor,
    hCost, hFork⟩
  change δ * (M / 4) ≤ I at hCost
  have hB : 0 ≤ I := by
    have hM4 : 0 ≤ M / 4 := by linarith only [hM]
    exact (mul_nonneg hδ.le hM4).trans hCost
  rcases hFork with hShort | hFast
  · have hImpossible : (T - x) * (M / 2) < (T - x) * (M / 2) :=
      lt_of_le_of_lt hShort (by simpa only [I] using hClock)
    exact False.elim ((lt_irrefl _) hImpossible)
  · let L : ℕ → ℝ := fun j =>
      thirdFullPhysicalKineticLowBandDissipationRate244 j
        (velocityH3Energy0At u b)
    have hL (j : ℕ) : 0 ≤ L j :=
      thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 j _
    exact thirdFull_scalar_kineticAnnularRate_forces_outerCutoffEscape244
      L n N n0 (M / 2) I hL hB
      (by simpa only [L] using hFast)
      (by simpa only [L, I] using hSmall)

/-- Same unconditional-on-terminal-dissipation cofinal high-radial time
sequence as the existing arbitrary-height diagonal. Every selected physical
observation has an independently selected natural outer cutoff and the
kinetic-only local integral certificate. The full terminal dissipation need
NOT be interval-integrable; annular windows are not summed. -/
theorem thirdFullPhysical_noH3Trace_kineticLocalAnnularCofinal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo b T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ThirdFullKineticNaturalAnnularLocalWitness244
          hH3 b (τ n) n (N n) (M n) (δ n)) := by
  obtain ⟨τ, hτ, _hDist, hLimit, hHigh, _hFull⟩ :=
    thirdFullPhysical_noH3Trace_arbitraryViscousHeightDiagonal244
      hH3 hClass b hb hNoTrace M
  have hWindow (n : ℕ) : ∃ (N : ℕ) (δ : ℝ),
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ n) n N (M n) δ :=
    thirdFullPhysical_highRadialSnapshot_kineticLocalAnnularWindow244
      hH3 hClass b hb (τ n) (hτ n) n (M n) (hM n) (hHigh n)
  choose N δ hInfo using hWindow
  exact ⟨τ, N, δ, hτ, hLimit, hInfo⟩

end
end PrimeTensor.FirstMonomialTriad
