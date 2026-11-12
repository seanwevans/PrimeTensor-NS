# Cap-free annular deficit charge via a truncated physical H³ clock

Base commit: `862c8fa7b528ba313c15f8779bcbfdbe4c9c9a06`.

## New result

The preceding module proves a physical viscous floor `epsilon/C(b,rho,H)` on
the cap-bounded branch `D_3(t)<=H`, leaving an alternative that a selected
window contains a cap spike `D_3(t)>H`. The spike branch DOES NOT defeat a
uniform height lower bound: there the physical viscosity itself exceeds H.

Define the strictly positive (when H,epsilon>0) *truncated charge*

    A(b,rho,H,epsilon) = min(H,epsilon/C(b,rho,H)),
    C(b,rho,H) = max(1,E_0(b)*(rho^2)^3*L(b,H)),

with the same earlier physical kinetic energy E_0(b) and the genuine
linear cap-slope L(b,H) from the established PDE source bound. For each
physical time `b<t<T` with the precise kinetic-excess condition and the
positive actual annular kinetic deficit floor, two exhaustive cases yield

    D_3(t)<=H -> D_3(t)>=epsilon/C >= A;
    D_3(t)> H -> D_3(t)>H>=A.

No full-H³ pointwise cap is presumed. The truncation is a property of the
physical dissipation density, not an imposed substitute density.

If the two kinetic premises persist across the selected pairwise separated
closed physical windows `[p_k,p_k+delta_k]`, each with `H_k>0` and
`epsilon_k>0`, the prior disjoint physical integration theorem gives

    for all m, sum_{k<m} delta_k*A_k <= integral_a^T D_3(t) dt.

Nonnegativity and the finite physical terminal H³ dissipation integral
imply summability of the entire series and termwise convergence to zero.
This has NO cap-spike disjunct. The cost can be optimized by a choice of
`H_k`; no optimization is claimed in the formal statement.

## Remaining analytic obstruction

The new theorem removes the artificial cap-spike escape but not the true
persistence problem. A positive annular kinetic-excess sample and a positive
Young-gap/width/outer-base deficit sample do not by themselves imply either
premise over a nonzero interval; a quantitative temporal modulus of the
full nonlinear annular deficit at moving frequency cutoffs is still needed.
Finite dissipation and kinetic energy monotonicity alone do not supply this
modulus for the exact high-frequency nonlinear Young-gap expression.

The source contains no new axioms, `sorry`, or `admit`. This ZIP has not
been kernel-compiled in the packaging environment; the user-side script
runs the pinned Lean/mathlib build and axiom/index audits before commit.
