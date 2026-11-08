# Cofinal physical signed LowMax escape on the original kinetic gaps

**Exact base:** `a3abca595bb113433d7bcdbdb981c57d8ec25c99` — physical baseline and viscous height, no Schwartz state in the four physical alternatives.

## What actually follows from the kinetic terminal hypotheses

The previous physical theorem `thirdFullPhysical_gapAdverseThird_physicalLowMaxFourCosts244` supplies four necessary signed-flux channels on any strict original gap: a true high-radial H3 tail, an earlier physical cubic/radial baseline, the product of a physical radius/energy clock coefficient and actual projected-source L1 action, or an annular positive-width full-H3 viscous charge. It does not claim any of those channels vanishes as the cutoff moves.

The repository separately proves, on the **same separated cofinal natural kinetic windows**, both

- `thirdFullPhysical_kineticGaps_sourceL1_tendsto_zero244`: the absolute projected momentum-source integral on each intervening gap tends to zero;
- `thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244`: the full actual H3 dissipation integral on each intervening gap tends to zero.

These are not assumptions about Schwartz approximation or additional regularity. They follow from the accepted `PreterminalH3EnergyClass`, finite terminal dissipation, and the original kinetic natural-annulus windows.

## A quantitative threshold, not merely a soft `o(1)` statement

Set `mu=(eta/2)/((2*pi)^7/3)>0` and choose any `K>=0`. Once the absolute source integral `S_k` falls below `mu/(8*(K+1))`, the physical clock alternative

`mu/8 < B_R(U(t),U(x)) * C_R * S_k`

forces `K < B_R(U(t),U(x)) * C_R`. The proof keeps strict inequalities and the exactly existing seventh-power radius coefficient; no uniform-in-R estimate is inserted.

Likewise, for every `epsilon>0`, the full physical dissipation integral of the original gap is eventually below `epsilon`, so the certified actual viscous arm is

`width * Hphys_R(U(t),U(x),mu/2)/4 < epsilon`.

## Main cofinal theorem

`thirdFullPhysical_kineticGaps_signedLowMax_physicalCofinalEscape244` proves that for **every** prescribed `K>=0` and `epsilon>0`, **all sufficiently late** original kinetic gaps have the following property: **for every** cutoff `R`, every positive high-tail tolerance `gamma`, and every actual adverse third-order physical observation `t` in that gap, at least one of:

1. physical high-radial H3 tail pays the native positive signed margin;
2. physical left-endpoint cubic LowMax baseline pays it;
3. the physical radius/energy/source multiplier `B_R*C_R` exceeds `K`;
4. an actual positive-width, inside-gap physical annular charge is smaller than `epsilon`.

The threshold index may depend on `K,epsilon` but **not** on `R,t,gamma`, because the only smallness inputs are the unweighted physical source and dissipation integrals of the whole gap. This order of quantifiers matters.

`thirdFullPhysical_kineticGaps_signedSurplus_physicalCofinalEscape244` also starts from the genuine integrated signed surplus; at each qualifying late gap it constructs the adverse physical time by the accepted signed energy theorem. The premise that the surplus exceeds the lower-order budget remains an explicit **per-gap implication**, not an assertion of adverse transport on every cofinal gap.

## Missing hard implication

This theorem does **not** establish continuation. To exclude the moving source branch one still needs an actual cutoff/energy rate bound on `B_R*C_R`; to rule out the baseline one needs additional signed structure, not merely its positive cubic upper bound. The high-radial tail remains a physical escape channel, and finite dissipation alone permits the positive annular persistence width times height to shrink. No false uniform-in-R bound, lower bound on that width, or unconditional H3 energy bound has been assumed.

## Verification

The registrar adds one predicate, three theorems, and the import. Run `proof/generate_index.py`, targeted Lean and Lake builds, full project build, and the proof fragment audit. Local ZIP static checks do not establish Lean elaboration.
