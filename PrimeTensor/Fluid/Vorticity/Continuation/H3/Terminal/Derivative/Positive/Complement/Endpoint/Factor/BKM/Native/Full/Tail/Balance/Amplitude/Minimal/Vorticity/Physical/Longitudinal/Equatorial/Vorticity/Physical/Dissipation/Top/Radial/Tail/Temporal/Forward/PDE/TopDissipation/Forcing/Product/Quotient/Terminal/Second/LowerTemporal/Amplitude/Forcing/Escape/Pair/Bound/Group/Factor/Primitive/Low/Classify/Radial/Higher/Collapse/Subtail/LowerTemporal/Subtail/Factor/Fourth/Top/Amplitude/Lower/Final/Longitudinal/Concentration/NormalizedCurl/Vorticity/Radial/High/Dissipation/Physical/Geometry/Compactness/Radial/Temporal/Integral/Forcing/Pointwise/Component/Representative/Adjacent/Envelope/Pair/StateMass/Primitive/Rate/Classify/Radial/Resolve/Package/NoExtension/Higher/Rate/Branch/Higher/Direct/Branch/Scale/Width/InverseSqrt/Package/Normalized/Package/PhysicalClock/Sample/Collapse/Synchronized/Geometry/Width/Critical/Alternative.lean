import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct.Branch.Scale.Width.InverseSqrt.Package.Normalized.Package.PhysicalClock.Sample.Collapse.Synchronized.Geometry.Width.Critical

/-!
# Exhaustive critical-width alternative

Expose failure of sampling-clock normalized vanishing in either radial family.
When both families vanish, retain energy escape or the synchronized radial
critical-width witness. No vanishing assumption is added to this theorem.

The full terminal package keeps the same parent sequence, forward interval,
positive vanishing left clock, and inherited geometry. The nonvanishing cases
state only failure to converge to zero; no divergence claim is made for them.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

def H3TerminalResolvedCanonicalForcingForwardWidthCriticalAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s σ : ℕ → ℝ) (δ : ℝ)
    : Prop :=
    (∃ qRadial : Fin 2,
      ¬ Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (Real.sqrt (T - τ n)) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass (h3TerminalForcingThirdQHigherRadialShift qRadial)
              (τ n) (hτ n))
        atTop (𝓝 0)) ∨
    (∃ qRadial : Fin 2,
      ¬ Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (Real.sqrt (T - τ n)) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass (h3TerminalForcingFourthQHigherRadialShift qRadial)
              (τ n) (hτ n))
        atTop (𝓝 0)) ∨
    (∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (v n))) atTop atTop) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialForwardWidthCriticalThreshold
        hH3 hClass τ hτ s σ
        (h3TerminalForcingThirdQHigherRadialShift qRadial)
        (h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient δ qRadial)) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialForwardWidthCriticalThreshold
        hH3 hClass τ hτ s σ
        (h3TerminalForcingFourthQHigherRadialShift qRadial)
        (h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient δ qRadial))

theorem resolvedCanonicalForcingForwardWidthCriticalAlternative_of_physicalLeftClockBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s σ : ℕ → ℝ) (δ : ℝ)
    (hs : ∀ n : ℕ, s n < T)
    (hForward : ∀ n : ℕ, s n < σ n)
    (hOrder : ∀ n : ℕ, τ n ≤ σ n)
    (hσ : ∀ n : ℕ, σ n < T)
    (hBranch : H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
      hH3 hClass τ hτ δ (fun n : ℕ => T - s n)) :
    H3TerminalResolvedCanonicalForcingForwardWidthCriticalAlternative hH3 hClass τ hτ s σ δ := by
  classical
  by_cases hSecondZero : ∀ qRadial : Fin 2,
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (Real.sqrt (T - τ n)) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass (h3TerminalForcingThirdQHigherRadialShift qRadial)
              (τ n) (hτ n))
        atTop (𝓝 0)
  · by_cases hFourthZero : ∀ qRadial : Fin 2,
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (Real.sqrt (T - τ n)) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass (h3TerminalForcingFourthQHigherRadialShift qRadial)
              (τ n) (hτ n))
        atTop (𝓝 0)
    · exact Or.inr (Or.inr
        (resolvedCanonicalForcing_energy_or_forwardWidthCriticalThreshold
          hH3 hClass τ hτ s σ δ hs hForward hOrder hσ hBranch hSecondZero hFourthZero))
    · exact Or.inr (Or.inl (not_forall.mp hFourthZero))
  · exact Or.inl (not_forall.mp hSecondZero)

def H3TerminalPhysicalTopDissipationResolvedCanonicalForcingForwardWidthCriticalAlternativeEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ j₀ : Fin 3,
      ∃ m q φ ψ : ℕ → ℕ,
        Tendsto m atTop atTop
          ∧
        Tendsto q atTop atTop
          ∧
        StrictMono φ
          ∧
        StrictMono ψ
          ∧
        ∃ s r : ℕ → ℝ,
          ∃ hs :
            ∀ n : ℕ,
              s n ∈ Set.Ioo a T,
            ∃ hσ :
              ∀ n : ℕ,
                σ n ∈ Set.Ioo a T,
              ∃ hr :
                ∀ n : ℕ,
                  r (φ (ψ n)) ∈ Set.Ioo a T,
                Tendsto (fun n : ℕ => s (φ (ψ n))) atTop (𝓝 T)
                  ∧
                Tendsto
                  (fun n : ℕ => σ (m (q (φ (ψ n)))))
                  atTop
                  (𝓝 T)
                  ∧
                (∀ n : ℕ,
                  s (φ (ψ n)) < σ (m (q (φ (ψ n)))))
                  ∧
                (∀ n : ℕ,
                  r (φ (ψ n)) ∈
                    Set.Icc
                      (s (φ (ψ n)))
                      (σ (m (q (φ (ψ n))))))
                  ∧
                Tendsto (fun n : ℕ => r (φ (ψ n))) atTop (𝓝 T)
                  ∧
                ∃ χ ω : ℕ → ℕ,
                  StrictMono χ
                    ∧
                  StrictMono ω
                    ∧
                  Tendsto
                    (fun n : ℕ => s (φ (ψ (χ (ω n)))))
                    atTop
                    (𝓝 T)
                    ∧
                  Tendsto
                    (fun n : ℕ => σ (m (q (φ (ψ (χ (ω n)))))))
                    atTop
                    (𝓝 T)
                    ∧
                  Tendsto
                    (fun n : ℕ => r (φ (ψ (χ (ω n)))))
                    atTop
                    (𝓝 T)
                    ∧
                  let τ : ℕ → ℝ :=
                    fun n : ℕ =>
                      r (φ (ψ (χ (ω n))))
                  let hτ :
                      ∀ n : ℕ,
                        τ n ∈ Set.Ioo a T :=
                    fun n : ℕ =>
                      hr (χ (ω n))
                  let clock : ℕ → ℝ :=
                    fun n : ℕ => T - s (φ (ψ (χ (ω n))))
                  (∀ n : ℕ, 0 < clock n) ∧
                  Tendsto clock atTop (𝓝 0) ∧
                  H3TerminalResolvedCanonicalForcingForwardWidthCriticalAlternative
                    hH3 hClass τ hτ
                    (fun n : ℕ => s (φ (ψ (χ (ω n)))))
                    (fun n : ℕ => σ (m (q (φ (ψ (χ (ω n)))))))
                    δ

theorem resolvedCanonicalForcingForwardWidthCriticalAlternativeEscapeSubsequenceOf_of_physicalLeftClockEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hWidth :
      H3TerminalPhysicalTopDissipationResolvedCanonicalForcingPhysicalLeftClockPositiveFloorEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationResolvedCanonicalForcingForwardWidthCriticalAlternativeEscapeSubsequenceOf
      hH3 hClass σ := by

  obtain
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      ψ,
      hmTop,
      hqTop,
      hPhiMono,
      hPsiMono,
      s,
      r,
      hs,
      hσ,
      hr,
      hsTendsto,
      hSigmaTendsto,
      hForward,
      hPoint,
      hrTendsto,
      χ,
      ω,
      hChiMono,
      hOmegaMono,
      hsFinal,
      hSigmaFinal,
      hrFinal,
      hClockPos,
      hClockZero,
      hBranch
    ⟩ :=
    hWidth

  refine
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      ψ,
      hmTop,
      hqTop,
      hPhiMono,
      hPsiMono,
      s,
      r,
      hs,
      hσ,
      hr,
      hsTendsto,
      hSigmaTendsto,
      hForward,
      hPoint,
      hrTendsto,
      χ,
      ω,
      hChiMono,
      hOmegaMono,
      hsFinal,
      hSigmaFinal,
      hrFinal,
      hClockPos,
      hClockZero,
      ?_
    ⟩

  let τ : ℕ → ℝ := fun n : ℕ => r (φ (ψ (χ (ω n))))
  let hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T := fun n : ℕ => hr (χ (ω n))
  let left : ℕ → ℝ := fun n : ℕ => s (φ (ψ (χ (ω n))))
  let right : ℕ → ℝ := fun n : ℕ => σ (m (q (φ (ψ (χ (ω n))))))
  have hLeftBranch : H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
      hH3 hClass τ hτ δ (fun n : ℕ => T - left n) := by
    simpa only [τ, hτ, left] using hBranch
  have hAlternative : H3TerminalResolvedCanonicalForcingForwardWidthCriticalAlternative hH3 hClass τ hτ left right δ :=
    resolvedCanonicalForcingForwardWidthCriticalAlternative_of_physicalLeftClockBranch
      hH3 hClass τ hτ left right δ
      (fun n : ℕ => (hs (φ (ψ (χ (ω n))))).2)
      (fun n : ℕ => hForward (χ (ω n)))
      (fun n : ℕ => (hPoint (χ (ω n))).2)
      (fun n : ℕ => (hσ (m (q (φ (ψ (χ (ω n))))))).2)
      hLeftBranch
  simpa only [τ, hτ, left, right] using hAlternative

end

end Euclidean
end Bridge
end PrimeTensor
