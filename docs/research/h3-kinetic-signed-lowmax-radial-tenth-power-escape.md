# Signed sixth-flux source clock: tenth-power radial and physical energy obstruction

**Pinned base:** `4d54dbbf891698c2f6e5c090ca59c59bf572dd2d`.

## The nontrivial quantitative step

The accepted cofinal theorem `thirdFullPhysical_kineticGaps_signedLowMax_physicalCofinalEscape244` proves that if its actual signed source-clock branch survives on sufficiently late original kinetic gaps, then for every prescribed `K>=0`,

`K < B_R(U(t),U(x)) * C_R`, where

- `B_R(X,Y)=243*[2(R+1)]^7*C0*(3+||X||+||Y||)^3` is the **physical** clock factor;
- `C_R=sqrt(1+(R+1)^2+(R+1)^4+(R+1)^6)` is the exact finite-band H3 multiplier;
- `C0=h3SobolevDeweightingConstant` is the existing Fourier L1 constant.

The new Fourier-polynomial inequality, for every natural `R`, is

`C_R <= 2*(R+1)^3`.

It uses `R+1>=1`, hence each of `1,(R+1)^2,(R+1)^4` is bounded by `(R+1)^6`. Taking a square root yields the claimed cubic ceiling. This is independent of the LowMax cutoff `2(R+1)`, which remains untouched.

Consequently the **exact** source multiplier satisfies

`B_R(X,Y)*C_R <= 62208*C0*(R+1)^10*(3+||X||+||Y||)^3`.

The coefficient `62208=243*2^7*2` is calculated, not postulated. Its **tenth** radius exponent comes from seven signed sixth-flux powers and three H3 multiplier powers.

## A true radius or energy dichotomy

For any natural radial cap `J` and real energy cap `E>=0`, define

`K(J,E)=62208*C0*(J+1)^10*(3+2*E)^3`.

If `R<=J` and both physical spectral norms are at most `E`, the full original clock coefficient is at most `K(J,E)`. Therefore a strict escape `K(J,E)<B_R*C_R` forces one of

`J<R`, `E<||U(t)||`, or `E<||U(x)||`.

The accepted exact Fourier energy ceiling gives `||U(s)|| <= velocityH3EnergyAt(u,s)` at every strict physical time. Thus the latter two alternatives imply actual physical **H3 energy** growth, not just large arbitrary Schwartz recoveries.

## New cofinal signed physical theorem

`thirdFullPhysical_kineticGaps_signedLowMax_radiusEnergyEscape244` substitutes `K(J,E)` into the already established source-L1 and viscous terminal limits for the **original separated kinetic gaps**, with no additional terminal compactness assumptions. For every radial cap `J`, energy cap `E>=0` and `epsilon>0`, sufficiently late gaps satisfy the following *universal-in-radius-and-adverse-observation* four-way alternative:

1. the physical high-radial H3 tail costs the prescribed positive signed margin;
2. the earlier physical cubic/radial signed-flux baseline costs its margin;
3. `J<R` or `E<velocityH3EnergyAt(u,t)` or `E<velocityH3EnergyAt(u,x)`;
4. a genuine positive-width inside-gap (including the right-endpoint backward window) physical annular viscous charge is `<epsilon`.

`thirdFullPhysical_kineticGaps_signedSurplus_radiusEnergyEscape244` also obtains the adverse time from the original positive integrated physical signed surplus, when the original lower-order gap margin is exceeded. That per-gap premise is still conditional.

Neither theorem assumes the actual Navier--Stokes solution has bounded H3 energy or an upper bound on its chosen radius. They describe *necessary costs* and do not prove an endpoint continuation contradiction. The earlier baseline, high-tail, and compressed-viscous arms remain valid escape channels.

## Verification

New Lean module: `FullThirdSolenoidalTerminalProfileKineticSignedLowMaxRadialTenthPowerEscape.lean`. The audit registrar adds two definitions and eight theorems. Regenerate `proof/generate_index.py` and run targeted Lean, targeted Lake, full `PrimeTensor` Lean and Lake, and `proof/check_fragment.py --all` in the pinned Lean 4/mathlib environment. Static archive checks are not Lean kernel verification.
