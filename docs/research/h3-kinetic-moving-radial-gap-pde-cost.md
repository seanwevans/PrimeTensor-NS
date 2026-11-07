# Moving radial cutoff costs on exact kinetic H3 sixth-flux gaps

**Base commit:** `eeb6d979f047bbe9d4da943a62e199f67cddd46f` — freeze H3 low radial bands across kinetic sixth flux gaps via physical PDE.

## The missing quantifier

The accepted fixed-radius result shows that `Q_R U(t)` becomes uniformly constant on each late *original* inter-window gap `J_k`, for each fixed `R`. It does not justify substituting `R = R(k)` because the native H3 weight ceases to have a uniform multiplier bound. The present patch specifies precisely the allowed moving-radius cost and a converse obstruction.

Let `U(t)` be the actual physical weighted H3 Fourier velocity, `G(t)` the actual projected physical L2 momentum source, and

`J_k = [tau(v(k)) + delta(v(k)), tau(v(k+1))]`,

`S_k = integral_(J_k) ||G(t)|| dt`.

The physical Hilbert FTC, Plancherel and native finite-band multiplier yield the **uniform-in-time** gap bound

`||Q_R U(s) - Q_R U(t)|| <= C_R S_k`

for every `s,t` in the same gap, where

`C_R = sqrt(1+(R+1)^2+(R+1)^4+(R+1)^6)`.

## Quantitative radial growth

We prove both monotonicity of the genuine finite-band H3 multiplier ceiling and the explicit cubic bound

`C_R <= 2(R+1)^3`.

The exponent three is the number of spatial derivatives in the native Sobolev multiplier, not an arbitrary window gauge. Therefore, even when `R(k)->infinity`, if

`(R(k)+1)^3 S_k -> 0`,

then for every `epsilon>0`, eventually

`||Q_(R(k)) U(s) - Q_(R(k)) U(t)|| < epsilon`

for **all** `s,t in J_k`. The stronger exact-ceiling version assumes merely `C_(R(k)) S_k -> 0`.

Conversely, suppose there exists `eta>0` such that at every sufficiently late kinetic gap one can find `s_k,t_k in J_k` with

`eta <= ||Q_(R(k)) U(s_k) - Q_(R(k)) U(t_k)||`.

Finite physical H3 dissipation already proves `S_k -> 0`. The physical modulus forces `eta <= C_(R(k)) S_k`. A finite-cutoff bound would contradict the vanishing source action. The monotonicity of the exact ceiling yields the **full limit**

`R(k) -> +infinity`,

not merely an unbounded subsequence. This is a necessary *temporal* concentration condition, conditional on the positive low-band excursion.

## Original no-trace witnesses and signed flux

The final theorem takes the **same** cofinal kinetic annular PDE windows from the accepted no-strong-terminal-H3-trace constructor, keeping their strict separation, original radii and time widths, extended finite viscous-charge packing, projected-source L1 decay on windows and gaps, moving raw kinetic tightness, universal-in-radius signed solenoidal sixth-flux / weighted H3 high-tail alternatives, and fixed-radius all-pairs freezing. It adds that any positive gap excursion observed in a moving low-H3 band necessarily uses radii escaping to infinity.

**Not proved:** that an adverse *low-maximum sixth-power Fourier flux* creates a positive low-band **state excursion**. This demands a trilinear continuity bound with controlled spectral norms; a static low-frequency flux may remain nonzero while the low-band state is frozen. Nor is an arbitrary moving radius automatically permitted: the multiplier-weighted source action must be small. No Navier--Stokes continuation or terminal-uniform H3 tightness is claimed.

## Lean declarations

1. `thirdFullKineticGap_finiteBandCeiling_mono244`
2. `thirdFullKineticGap_finiteBandCeiling_le_cubic244`
3. `thirdFullKineticGap_scalar_movingCeilingEscape244`
4. `thirdFullPhysical_strictGap_uniformLowBandPDEModulus244`
5. `thirdFullPhysical_kineticGaps_movingLowBandPDEFreeze244`
6. `thirdFullPhysical_kineticGaps_cubicMovingCutoffFreeze244`
7. `thirdFullPhysical_kineticGaps_lowBandExcursion_forcesRadialEscape244`
8. `thirdFullPhysical_noH3Trace_kineticMovingRadialGapCost244`

No `sorry`, `admit`, or new axioms are introduced. As the pinned Lean toolchain is not available in the package construction environment, compilation must be verified locally.
