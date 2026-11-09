# Native signed sixth flux: tenth-power radius/energy and kinetic gauge coupled obstruction

**Pinned base:** `911defbbbf4160c7a7de2775a89bf4d1e461c3e6` — force signed sixth flux outer gauge escape or finite kinetic rate compression.

## The two independently accepted estimates

The original actual physical projected-source sixth-flux clock at natural radius R and two states X,Y is bounded by the tenth-power coefficient

`A_clock(R,X,Y) <= 62208*C0*(R+1)^10*(3+||X||+||Y||)^3`.

Thus for prescribed radius J and physical H3 energy E, with R<=J and the physical H3 energies at t and the original kinetic gap left endpoint x both <=E, the source-clock factor is <= the fixed numerical threshold `K(J,E)=62208*C0*(J+1)^10*(3+2E)^3`. The accepted cofinal radius/energy theorem invokes that threshold and leaves the old signed baseline, physical radius/energy escape, old quadratic-height positive in-gap charge, or a gamma-offset *high-radial carrier*.

Separately, the accepted kinetic finite-gauge result proves for a genuine gamma-FREE carrier, uniformly over original late gaps, natural cutoff R, outer gauge G, and physical observation t, that an actual finite outer annulus Q>=R must pay one of

1. `(y-x)*H_linear < 16*epsilon`;
2. `G < Q`;
3. `H_linear^2 < 32*(2*sum_{j<=G} L_j(E0(b))+1)*epsilon`.

Here `H_linear = (R+1)^2*(eta/2) / (2*(A(t)+1))`, and `A(t)=((2*pi)^7/3)*1944*C1*(E3(t)+1)`; the finite-rate sum is nonnegative and does not rely on monotonicity of `L_j`.

## The hard coupling

The new cofinal theorem `thirdFullPhysical_kineticGaps_signedLowMax_tenthGaugeCoupling244` intersects the two eventual thresholds **before** choosing G,R,t. Then it removes the auxiliary positive Schwartz error `gamma` at this same physical t using `thirdFull_scalar_signedLowMax_removePositiveTailTolerance244`.

For EVERY cutoff R, EVERY outer gauge G, and EVERY genuine adverse observation t on sufficiently late original kinetic gaps, one of the following necessary conditions holds:

1. the physical signed cubic baseline at the actual earlier endpoint x;
2. `J<R` or `E<E3(t)` or `E<E3(x)`;
3. the original positive-width, quadratic-height integrated annular charge is `<epsilon`;
4. there is an actual `Q>=R` for which the kinetic gap clock compresses, the annulus escapes the gauge G, or the finite kinetic rate budget compresses.

This is not a claim that G<Q always happens, and does not discard the earlier physical signed baseline or compressing viscous charge. The new `thirdFullPhysical_kineticGaps_signedSurplus_tenthGaugeCoupling244` supplies the actual adverse time from the genuine integrated signed physical surplus, when that surplus exceeds its lower-order margin on the specific gap.

## New uniform positive floor under a physical energy cap

A separate analytic step proves

`eta/(8*(A(E)+1)) <= H_linear(R,eta,E3(t))` whenever `eta>0` and `0<=E3(t)<=E`, uniformly for all natural R. This uses the genuine first-moment deweighting constant and `(R+1)^2>=1`, and is registered as `thirdFullKinetic_signedLowMax_linearHeight_ge_cappedFloor244`.

Therefore if the tenth-power residual branch is independently excluded, the physical H3 energy at t is capped by E, and the gap clock and finite-gauge rate budgets are unable to pay the **fixed cap-dependent floor**, the new `thirdFullKinetic_signedLowMax_tenthGauge_forcesOuter_of_energyCap244` forces `G<Q` for some certified actual outer cutoff Q>=R.

This is the promised separation of the physical energy cap from the genuine kinetic rate / terminal clock. It does not assert a uniform lower bound on `(y-x)` or `D_gap / (y-x)`, and is not an unconditional Navier–Stokes continuation result.

## Verification

Apply the registrar, run `proof/generate_index.py` plus `--check`, the targeted Lean elaboration and Lake build, the global import elaboration/build, and `proof/check_fragment.py --all`. The archive is statically verified; Lean/kernel verification must run on the pinned local toolchain.
