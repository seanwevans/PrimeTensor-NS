# Finite Z³ Leray-Galerkin: right-maximal endpoint alternative

2026-11-17 · base: `d206ebb4672e0f4fbba891b92b3e3023962bee38`

## Exact result

For any finite cutoff S and exact complex Leray-Galerkin field F_S, take
0 ≤ μ ≤ 1/10, an initial datum satisfying W_{log 2}(u(a)) < 100, and any
strong ODE path on [a,b) with a < b. Write

    τ = (log(2) - log(9/5))/100 = log(10/9)/100.

The endpoint alternative is

    (∃ δ>0, a strong same-field continuation across b on [a,b+δ),
       equal to the old path on [a,b)) OR (τ < b-a).

The alternative does not posit a later analytic ball, a uniform local
Picard radius, or a terminal derivative. If b-a ≤ τ, earlier results
construct the endpoint analytic trace, Picard restart, and exact seam
derivative. The extension preserves the initial datum and the entire
preterminal history. Thus any genuinely right-maximal finite strong path,
**if one exists**, cannot terminate with b-a ≤ τ; indeed τ < b-a.

This strict endpoint inequality includes b-a = τ; a solution that lives
exactly to the boundary of the analytic window is still extendible by
ordinary local Picard theory. No claim is made about Wiener control beyond
τ, only the existence of an honest strong ODE continuation.

## Remaining hard mathematical step

Construct a maximal forward solution for each finite S and initial state,
with compatibility/uniqueness on overlapping intervals. A maximal-solution
construction (or alternative direct finite-horizon gluing construction)
must then feed the established endpoint alternative to obtain actual
existence on the whole cutoff-independent horizon. It is not sufficient
to assume the existence of a maximal solution without proving it.

## Verification

The checker establishes source integrity and no admitted proofs. The
repository build on the pinned Lean/mathlib toolchain establishes whether
the actual propositions and tactics type-check. The finite-dimensional
result is not a solution to the 3D Navier–Stokes regularity problem.
