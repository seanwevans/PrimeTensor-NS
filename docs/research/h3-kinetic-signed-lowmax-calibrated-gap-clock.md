# Energy-calibrated signed LowMax H3 PDE clock on physical kinetic gaps

**Exact base:** `217708bc2730a852bce3be273b0b1166b3ba6cf5` — physical signed sixth-flux gap replenishment with two automatically recovered solenoidal Schwartz fields.

## The hard obstruction: a recovered, not physical, clock coefficient

The accepted one-sided gap theorem separates four genuine costs: a high-radial physical H3 tail; an earlier signed LowMax flux baseline; a recovery/PDE clock; and a strictly positive annular physical viscous charge on the **same gap**. The preceding physical recovery theorem constructs both Schwartz representatives automatically, but the clock contained

`A_R(V,W) * (||V-U(t)|| + C_R * SourceL1[x,y] + ||U(x)-W||)`

with `A_R(V,W) = 243 * [2(R+1)]^7 * h3SobolevDeweightingConstant * (1+||V||+||W||)^3`. Choosing tiny raw approximation errors without accounting for the cubic recovered amplitude cannot justify dropping the two error terms.

## Physical amplitude ceiling selected *before* recovery

Set `X=U(t)`, `Y=U(x)`, `mu=(eta/2)/((2*pi)^7/3)>0` and define

`B_R(X,Y) = 243 * [2(R+1)]^7 * h3SobolevDeweightingConstant * (3+||X||+||Y||)^3`.

Choose **both** approximation tolerances as the same positive physical quantity

`d_R(X,Y,mu) = min(1, mu/(32*(B_R(X,Y)+1)))`.

For any exact weighted-H3 Schwartz recoveries with `||V-X||<d` and `||Y-W||<d`, the physical triangle inequality gives

`||V||<=||X||+1`, `||W||<=||Y||+1`, hence `A_R(V,W)<=B_R(X,Y)`.

The exact coefficient-weighted recovery error then satisfies

`A_R(V,W)*(||V-X|| + ||Y-W||) <= mu/16`.

There are no terminal-uniform radius or energy assumptions. The choice `d` can be arbitrarily small when the physical states or radial cutoff grow, but **is positive at every selected strict physical gap**.

## Genuine physical-source consequence

The earlier one-sided flux theorem forces a clock arm

`mu/4 < A_R(V,W)*(||V-X|| + C_R*SourceL1[x,y] + ||Y-W||)`.

Absorbing the above error budget yields

`mu/8 < A_R(V,W)*C_R*SourceL1[x,y] <= B_R(X,Y)*C_R*SourceL1[x,y]`.

The last inequality uses the actual nonnegative Bochner norm integral and the existing nonnegative finite-band Fourier ceiling. Thus the resulting source branch has a coefficient built **only from the actual physical H3 states and prescribed radius**, not from any arbitrarily selected Schwartz recovery.

The new theorem `thirdFullPhysical_gapAdverseThird_calibratedSignedLowMaxSourceOrCharge244` starts directly from a physical adverse third-transport observation, automatically recovers both solenoidal Schwartz profiles, and concludes high radial H3 tail OR an earlier baseline OR the above *fully physical* source-clock obstruction OR the existing in-gap physical viscous charge. The source bound and the viscosity integral are taken on precisely the original `[x,y]`.

The theorem `thirdFullPhysical_gapSignedSurplus_calibratedSignedLowMaxSourceOrCharge244` selects the adverse physical observation automatically from a genuine positive integrated surplus exceeding its lower-order budget, via the accepted Navier-Stokes signed energy law. No time-dependent Schwartz selection or false two-snapshot signed flux assumption is introduced.

## Scope and next hard task

This step **does not** eliminate the earlier LowMax signed-flux baseline. It does not infer that moving-radial coefficients remain bounded on cofinal gaps, or that the forward/backward viscous charge widths do not collapse. It converts the previously arbitrary Schwartz approximation cost into an explicit physical source cost, permitting honest interaction with the known source-L1 terminal tail estimates. A further quantitative gauge/energy-vs-radius estimate is still required to exclude the source arm at moving frequency, while a physical earlier-time flux condition is required to exclude the baseline arm.

## Verification

Register two definitions and six theorems via `tools/audit/register_h3_full_third_kinetic_signed_lowmax_calibrated_gap_clock.py`; regenerate `proof/generate_index.py`, run targeted `lake env lean`, targeted and full Lake builds, and `proof/check_fragment.py --all`. No `sorry`, `admit`, or new axioms. Static packaging is not Lean elaboration.
