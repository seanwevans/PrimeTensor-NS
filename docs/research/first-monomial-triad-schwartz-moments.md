# Automatic Schwartz moment finiteness

Base: 85798103, triad shell integral bounded by weighted L2 and L1 moments.

For the Euclidean Fourier vector amplitude A(p)=|U(p)|_2, the patch proves

    A(p)² = sum_j |U_j(p)|²,
    A(p) <= sum_j |U_j(p)|,

and continuity of A. Each U_j is a Schwartz Fourier transform.
The coordinate sum majorizes every polynomial L1 moment. The Schwartz
product U_j U_j has norm |U_j|² and supplies every squared moment.
Consequently, for every natural n, both functions

    p -> |p|^n A(p),
    p -> |p|^n A(p)²

are integrable. In particular (|p|² A(p))² and |p|³ A(p) satisfy the
hypotheses of the previous integral bound.

The resulting theorem h3SchwartzTriadShellKernel_integral_norm_le_of_schwartz
requires only Schwartz data and Fourier incompressibility. It concludes

    |integral S| <= 2 (integral |p|⁴ A(p)²) (integral |q|³ A(q)).

The earlier theorem with explicit moment hypotheses remains available.
Physical Schwartz divergence supplies Fourier incompressibility through
the existing divergence transport theorem.

## Remaining analytic issue

Finiteness for each Schwartz snapshot is not a uniform bound in terms of
H3 energy and dissipation. In particular the third-order Fourier L1 moment
on the right is not controlled by H3 alone. This patch closes the moment
finiteness interface; it does not close the critical absorption argument.

The next estimate must retain useful frequency separation or otherwise
handle the comparable-frequency contribution. Introducing an uncontrolled
higher moment as though it were bounded by H3 would lose the actual problem.

## Checks

Source index, fragment consistency and whitespace checks are run before
packaging. Lean compilation and the audit remain pending on the pinned
local toolchain. No axioms or sorry declarations are introduced.
