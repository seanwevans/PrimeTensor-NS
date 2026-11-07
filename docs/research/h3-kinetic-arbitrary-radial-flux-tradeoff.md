# Arbitrary-radius radial Fourier tradeoff on the original kinetic H³ PDE gaps

**Exact baseline:** `ce0b4f125d1488f7158784879b62e2c0c379d83e` — the original no-terminal-H³-trace kinetic gaps admit a common low-maximum Fourier radius on each compact gap, with the cutoff chosen before an adverse snapshot.

## Why the arbitrary-radius quantifier is useful

The preceding statement was `∀ gap k, ∃ radius R_k`, with no terminal growth restriction on `R_k`. This patch proves a **quantitative alternative for every prescribed natural radius R** and at every actual adverse physical time. It uses the existing solenoidal sixth-power Fourier flux, the exact physical weighted H³ snapshot encoder and the high-maximum trilinear estimate. No new analytic moment hypothesis or global H³ bound is introduced.

Let `E(t)=velocityH3EnergyAt u t`, `U(t)=h3AuditActualSpectralVelocityTotal hH3 t`, `P_R` be the exact weighted-H³ high-radial cutoff, and `A=(2π)^7/3`. The existing solenoidal Schwartz recovery yields states `V_n → U(t)` and the genuine top-order transport representation:

`A Im∫ F₆(Ψ_n) → T₃(t)`.

For every *fixed* radius `R` and approximation tolerance `γ>0`, sufficiently late recovery indices satisfy both

`‖V_n‖≤E(t)+1` and `‖P_R V_n‖<‖P_R U(t)‖+γ`.

The existing trilinear high-maximum estimate therefore yields

`‖∫_{HighMax(R)} F₆(Ψ_n)‖ ≤ 1944 C₁ (E(t)+1) (‖P_R U(t)‖+γ)²`.

The complex flux integral splits *exactly* into high-maximum and low-maximum pieces, including frequency ties. If `η < -T₃(t)`, the first theorem proves, eventually in `n`,

`η < -A Im∫_{LowMax(R)} F₆(Ψ_n) + A·1944 C₁ (E(t)+1) (‖P_R U(t)‖+γ)²`.

Consequently there is a genuine two-way alternative:

1. **Weighted-H³ high-tail obstruction:** `η/2 < A·1944 C₁ (E(t)+1) (‖P_R U(t)‖+γ)²`.
2. **Signed low-maximum transport:** the same divergence-free recovery satisfies `η/2 < -A Im∫_{LowMax(R)} F₆(Ψ_n)` for all sufficiently large `n`.

This is a *necessary* condition on the actual frequency-resolved physical H³ transport. The raw moving-band kinetic mass cannot be substituted for the weighted H³ tail without paying the frequency factors. No claim is made that the first alternative is absent, nor that the low-maximum transport integral is terminal-time integrable.

## Exact original kinetic gaps

The third theorem establishes this tradeoff for **every R, every γ>0, and every genuinely adverse physical time inside any strict compact gap**. The four theorem reuses the existing no-H³-trace kinetic construction and carries the arbitrary-radius property to all gaps `(τ(v k)+δ(v k),τ(v(k+1)))`. The original annular witnesses, strict separation, cofinality, finite extended viscous packing, projected-source L¹ decay and uniformly vanishing raw annular kinetic mass remain unchanged.

**Open analytic question:** show that the low-maximum Fourier contribution has a terminal-time constraint strong enough to turn this necessary tradeoff into a lower bound for `‖P_R U(t)‖`, uniformly along adverse gap times. Only then would the estimate quantify how fast required Fourier radii must escape.

## Lean declarations

* `thirdFullPhysical_adverseThird_arbitraryRadiusFluxTailBudget244`
* `thirdFullPhysical_adverseThird_arbitraryRadiusTailOrLowMax244`
* `ThirdFullKineticGapArbitraryRadialTradeoff244`
* `thirdFullPhysical_strictGap_allRadialFluxTradeoffs244`
* `thirdFullPhysical_noH3Trace_kineticArbitraryRadialGapTradeoff244`

No `sorry`, `admit` or new axioms. Pinned Lean/mathlib elaboration remains required; static validation cannot establish that the proofs compile.
