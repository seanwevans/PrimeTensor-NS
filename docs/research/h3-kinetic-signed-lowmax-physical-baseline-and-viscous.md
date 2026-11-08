# Completely physical signed LowMax gap costs: cubic baseline and viscous height

**Exact base:** `29348e3acc48e8f2abb075506328bf6f62b7e5e5` — calibrated physical signed-flux recovery errors into the true projected-source clock.

## Goal and novelty

The accepted theorem `thirdFullPhysical_gapSignedSurplus_calibratedSignedLowMaxSourceOrCharge244` already selects an adverse physical observation from the integrated signed surplus, constructs two real-solenoidal Schwartz recoveries with a physically calibrated error, and converts the recovery/PDE clock branch to the actual projected-source L1 action. Two artifacts of the proof remained in its outcome: an *earlier Schwartz signed LowMax flux baseline*, and a viscous persistence height depending on the two recovered Schwartz norms.

This module removes both artifacts. Its final theorem has only original **physical** H3 spectral states, the actual physical source integral and the full H3 dissipation integral. The real-solenoidal Schwartz approximants are used in the proof and eliminated from the statement. The original observation times and exact moving cutoff are retained.

## 1. Cubic physical reference baseline

At an arbitrary fixed radius R, the previously established automatic weighted-H3 mixed-Schwartz integrability theorem gives the actual LowMax flux bound, with the unit Young parameter and three identical Fourier profiles:

`|Im Phi_R(q)| <= 81 * [2(R+1)]^7 * C0 * ||W||^3`.

Here `W` is the *exact* Fourier weighted-H3 representative of the reference Schwartz function q. The constant `81` is from `9 * 3 * 3` in the accepted mixed Young estimate, not inferred from the old Lipschitz coefficient. The proof uses the true complex integral norm inequality on the exact complement of HighMax(R), so the original signed phase is not replaced by a hypothetical scalar model.

The calibrated earlier recovery obeys `||Y-W||<d<=1`, with `Y=U(x)` the **actual** physical weighted-H3 state at the left gap endpoint. Consequently

`|Im Phi_R(q)| <= 81 * [2(R+1)]^7 * C0 * (||U(x)||+1)^3`.

This yields a purely physical earlier-time cubic/radial amplitude alternative. It does *not* assert the baseline is small at an unbounded radius or with growing physical H3 energy.

## 2. Genuine physical viscous annular height

The existing calibrated coefficient inequality gives

`A_R(V,W) <= B_R(U(t),U(x))`

where `A_R(V,W)=243*[2(R+1)]^7*C0*(1+||V||+||W||)^3` and `B_R(X,Y)=243*[2(R+1)]^7*C0*(3+||X||+||Y||)^3`. Since the old physical viscous height is

`H_R(V,W,mu/2) = (R+1)^2 * ((mu/2)/4)^2 / (2*(A_R(V,W)^2+1))`,

it is bounded from below by the *entirely physical* height

`Hphys_R(X,Y,mu/2) = (R+1)^2 * ((mu/2)/4)^2 / (2*(B_R(X,Y)^2+1))`.

Multiplying by the positive certified persistence width and using the old exact annular charge therefore gives

`width * Hphys_R(U(t),U(x),mu/2)/4 <= ∫_[x,y] velocityH3DissipationAt(u,r) dr`.

There is no hidden lower bound on `width` or `Hphys`: the coefficient grows with the moving radius, so height compression remains possible.

## 3. All four branches depend only on physical quantities

On the same original closed strict gap `[x,y]`, with a physical adverse third-order snapshot exceeding `eta>0`, the new theorem proves the disjunction:

1. Actual physical high-radial H3 tail: `eta/2 < C*1944*C1*(E3(t)+1)*(||P_R U(t)||+gamma)^2`.
2. Actual physical earlier baseline: `mu/2 <= 81*[2(R+1)]^7*C0*(||U(x)||+1)^3`.
3. Actual projected-source action: `mu/8 < B_R(U(t),U(x))*C_R*∫_[x,y]||G(r)||dr`.
4. Actual physical viscous charge: a certified forward-inside or backward-from-right-endpoint window of positive width `w` obeys `w*Hphys_R(U(t),U(x),mu/2)/4 <= ∫_[x,y]D3(r)dr`.

Here `mu = (eta/2)/((2*pi)^7/3)`. The following integrated-surplus theorem automatically supplies the adverse time when the *original signed gap surplus exceeds its lower-order physical budget*.

## What remains open

The project does not yet rule out the earlier physical cubic/radial baseline, the moving-radius and growing energy factors in the source clock, the high-tail carrier, or the compression of the positive viscous width times height. Finite H3 dissipation forces gap dissipation tails to vanish, but does not alone bound the moving coefficients. The result is a rigorously specified necessary condition, **not** a claim of unconditional three-dimensional Navier–Stokes regularity.

## Audit

Register `thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244`, `thirdFullKineticSignedLowMaxPhysicalViscousHeight244`, the two coefficient lemmas and the two physical theorems. Regenerate `proof/generate_index.py` and compile with pinned Lean/mathlib before committing. This archive is statically checked, not kernel-verified locally.
