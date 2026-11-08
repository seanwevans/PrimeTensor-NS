# Single-snapshot signed LowMax flux: cofinal baseline/clock/viscous trichotomy

**Exact baseline:** `d55f6c9945a55940f4da35ed68764d787b18639e` — cofinal two-snapshot signed LowMax gap compression.

## The actual logical gap

The normalization lemma `thirdFull_scalar_negativeWeightedSignedFlux_to_oneSided244` transfers any actual scaled negative signed observation `eta <= -(C * Im Phi)` with positive Fourier coefficient `C` to the one-sided lower bound `eta/C <= |Im Phi|`, keeping the physical prefactor explicit.

The existing `ThirdFullKineticGapArbitraryRadialTradeoff244` is a one-time physical theorem: a strictly adverse physical transport observation gives a real-solenoidal Schwartz recovery sequence with one signed low-maximum flux branch (or the alternative high-H3 tail cost). It does *not* prove a positive signed flux **difference** between two physical observation times. The previous `ThirdFullKineticSignedLowMaxCofinalGapSamples244` assumed that positive difference.

## A genuine one-sided transfer

At the same natural radius `R`, choose an independent earlier reference Schwartz representative `q` and a one-sided late Schwartz representative `p`, each with exactly realized weighted-H3 Fourier state `W` and `V` respectively. If the late signed imaginary LowMax flux obeys

`eta <= |Im Phi_R(p)|`, `eta > 0`,

then the real triangle inequality yields the disjoint test

`eta/2 <= |Im Phi_R(q)|` or `eta/2 < |Im Phi_R(p) - Im Phi_R(q)|`.

If the second arm holds, the *already proven* strict physical closed-gap signed flux theorem applies with adverse margin `eta/2`, retaining the original observation times `s,t`, the original physical interval `[x,y]`, and the entire weighted Fourier recovery/source cost. The result is the exact trichotomy:

1. `eta/2 <= |Im Phi_R(q)|` (the **baseline** itself is a significant signed flux carrier);
2. `eta/4 < A_R(V,W)*(||V-U(t)|| + C_R*SourceL1[x,y] + ||U(s)-W||)` (actual **clock/recovery** cost);
3. an actual forward- or backward-oriented positive annular time width `width` within `[x,y]` obeys `width*(H_R(V,W,eta/2)/4) <= ∫_[x,y] D3` (real **viscous** cost).

Here `A_R(V,W) = 243*[2(R+1)]^7*C0*(1+||V||+||W||)^3` and `H_R` is exactly the previously established cutoff/amplitude-weighted positive physical viscous height. The numerical margin is halved a second time because the one-sided-to-difference argument spends `eta/2`.

## Cofinal transfer

Retain every original cofinal annular kinetic window, its strict temporal gap, and moving radius `R(k)`. Assume **one-sided** signed LowMax samples of size at least `eta` on each gap, with one reference profile and actual weighted Fourier recoveries, not an adverse difference as in the previous bridge.

The previously accepted theorem proves the full actual physical H3 dissipation integral of these gaps tends to zero if full terminal H3 dissipation is integrable. Therefore for every `epsilon > 0` and all sufficiently late `k`, exactly the same three branches hold with the viscous arm compressed to

`width_k * H_(Rk)(Vk,Wk,eta/2) / 4 < epsilon`.

The earlier `source L1 -> 0` is **not** enough to dismiss branch (2), since the cubic recovery amplitude and seventh-power moving cutoff may diverge. The gap's short physical time scale is also not enough to dismiss branch (3), since the certified viscous height may shrink.

## What remains open

The original single-snapshot physical replenishment must be connected to the **specific one-sided** LowMax flux observations along the cofinal gaps. For an actual continuation obstruction, either the earlier-reference baseline (1) must be controlled, or it must be tracked as a genuine persistent source of signed flux. Even after controlling (1), a quantitative bound on the amplitude-weighted recovery/source clock and the width/height noncompression product is required. The present proof does not assert those facts and does not derive unconditional Navier–Stokes regularity.

## Verification

The registrar checks five public declarations, imports the new source and appends `#check` / `#print axioms` for all. Run `proof/generate_index.py` first, then pinned `lake env lean`, targeted Lake build, full build and fragment audit. Static tests do not establish Lean elaboration.
