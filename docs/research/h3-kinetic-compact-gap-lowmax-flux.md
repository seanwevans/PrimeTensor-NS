# A common low-maximum solenoidal sixth-flux carrier on each kinetic PDE gap

**Base:** `250364df3a3a1deebe12da3826292a2252a3dcae` — force off-shell sixth Fourier flux from kinetic H³ gap excess.

## The missing quantifier in earlier fixed-time off-shell persistence

The previous off-shell theorem chooses a real-solenoidal Schwartz recovery for *one* adverse snapshot, then proves that any bounded vanishing-width common-radius annulus may be removed from the sixth-order flux without changing its signed physical limit. It does not pick a single Fourier cutoff for different times in a physical gap, nor constrain the cutoff as those gaps approach the terminal time.

For an actual compact strict-time gap `[x,y] ⊂ (a,T)` the weighted H³ Fourier path `U(t)` is continuous. Its image is compact. Two existing frequency-localized estimates apply:

1. Uniform tightness of the **genuine weighted Fourier state** on compact state families: for all `δ>0`, some `R` satisfies `‖P_R U(t)‖<δ/2` for **every** `t∈[x,y]`.
2. The exactly partitioned solenoidal sixth-order Fourier trilinear high-maximum bound, where `F₆` is the full complex six-orbit kernel:

   `‖∫_{HighMax(R)} F₆(Ψ)‖ ≤ 1944 C₁ K ‖P_R V_Ψ‖²`.

Choose the common cutoff `R` using compactness **before** choosing a time, and select for each time `t` its previously established exactly divergence-free real Schwartz recovery `Ψ_{t,n}`. The recovery states `V_{t,n}` converge strongly in weighted H³. A common physical slab energy ceiling gives the same coefficient `K` across times, while the recovery index `n` may depend on time.

The first theorem therefore proves:

`∀ ε>0, ∃ R, ∀ t∈[x,y], ∃ Ψ_t, (solenoidal Ψ_t) ∧ (full sixth-flux → actual physical T₃(t)) ∧ (eventually ‖∫_{HighMax(R)} F₆(Ψ_t,n)‖<ε)`.

This is stronger than a time-by-time choice `∀ t,∃R_t`. No assumption about a *jointly measurable* Schwartz recovery family is used.

## Quantitative low-maximum persistence of adverse transport

For `η>0`, choose `ε=η/[8(1+A)]`, with `A=(2π)^7/3`. At every physical gap time satisfying `η< -T₃(t)`, the full sixth-power flux has signed imaginary part below `-3η/4` at sufficiently large recovery indices. The common high-maximum component satisfies `|A Im∫_{HighMax(R)}F₆|≤η/8`. The exact measurable two-way integral partition gives

`η/2 < -A Im ∫_{HighMax(R)^c} F₆(Ψ_t,n)` eventually.

Thus the same `R` works at **all potentially adverse physical times** within that gap. The low-maximum region is the complementary measurable triad region where the largest of the three physical Fourier-gradient magnitudes is less than `2(R+1)`.

## Same original kinetic windows and remaining obstruction

The third theorem enhances the previous finite-window three-way test. Either one of the *original* annular PDE windows reaches the Riccati scale; the finite viscous charge fits below initial H³ energy plus the explicit lower-order gap integrals; or an *original* gap has both an adverse physical top-third sample and this gap-wide low-maximum signed Fourier carrier.

The last theorem transports the gap carrier to the original no-strong-terminal-H³-trace kinetic construction, retaining its cofinal sequence, exact annular witnesses and widths, disjointness, global extended-dissipation cost packing, vanishing absolute projected-source-L¹ action, and uniform moving raw Fourier kinetic tightness.

**Crucial limitation:** We obtain `∀k,∃R_k`, **not** a single cutoff radius valid for every terminal gap. The radii `R_k` can diverge as `k→∞`; the full physical H³ energy may simultaneously grow. This remains a necessary localization constraint, not a global regularity theorem or a terminal-uniform sixth-flux estimate.

## Lean declarations

- `thirdFullKineticGapUniformLowMaxCarrier244` (predicate)
- `thirdFullPhysical_strictSlab_independentRecovery_highMaxUniform244`
- `thirdFullPhysical_strictGap_adverseThird_uniformLowMax244`
- `thirdFullPhysical_kineticCumulativeMarginOrGapLowMax244`
- `thirdFullPhysical_noH3Trace_kineticCompactGapLowMaxCarriers244`

No `sorry`, `admit` or new axioms. Compiling with the pinned Lean/mathlib toolchain is required; static archive and audit checks cannot establish elaboration.
