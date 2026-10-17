# Fixed-kinetic concentration defeats static **full** H³ absorption

Baseline: `15085706` (`close fixed kinetic concentration scalar and physical divergence proof`).

For any positive first-monomial divergence-free real Schwartz field `f`, consider its physical Point3 spatial concentration `f_t(x) = t^3 f(t² x)`, `t>0`. This patch derives all five exact scaling identities for the *actual finite-index physical Schwartz functionals*:

| Mass | Identity |
|---|---|
| E0(f_t) | E0(f) |
| E1(f_t) | t^4 E1(f) |
| E2(f_t) | t^8 E2(f) |
| E3(f_t) | t^12 E3(f) |
| D4(f_t) | t^16 D4(f) |
| M(f_t) | t^17 M(f) |

Here `M` is the signed complete 243-slot **first** interpolation monomial, not the whole third-order Navier–Stokes transport. The normalized full H³ energy is `1 + E0 + E1 + E2 + E3`, and all velocity components and ordered derivative slots are retained.

For any `C,K : ℝ`, the quarter-packet supplies two physical Point3-solenoidal Schwartz velocities with exactly equal kinetic energy such that

    C * D4(g) + K * (1 + E0(g) + E1(g) + E2(g) + E3(g)) < M(g).

In particular, the static bound fails even if one pays the *entire* H³ energy, not just kinetic energy. The fixed-kinetic constraint is exact rather than asymptotic.

## Where the actual hard analytic work remains

The repository independently proves on appropriately admissible physical Navier–Stokes paths:

    T3 = G3 + 3 * M.

The new theorem `lowNormalQuarter_fixedKinetic_forces_gradient_compensation244` shows a necessary condition on the same concentrated **Schwartz snapshot**: if the total quantity `G + 3M(g)` is absorbed by `C D4(g) + K E_H3(g)`, then `G < -2 M(g) < 0`. This is a sharp directional demand for compensation from the **gradient** block; it does not identify `G` as the actual physical gradient commutator on this snapshot or prove the profile occurs along a solution. That calculation and any dynamical restriction excluding the concentration scenario are the genuine future PDE-specific tasks.

The theorem **does not refute global regularity**, does not imply blow-up, and does not rule out estimates involving nonlinear/superlinear energy remainders or actual time integration.
