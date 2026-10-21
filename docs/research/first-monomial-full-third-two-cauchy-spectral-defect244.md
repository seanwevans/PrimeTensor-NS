# Physical two-Cauchy decomposition of the sharp top Fourier Young deficit

Base commit: `abff300a` — *identify sharp H3 Fourier Young deficit and spectral frequency rigidity*.

## New identity

The fourth-moment interpolation inequality used in the sharp Young bound is
not one atomic step. It came from two separate Fourier Cauchy estimates,

\[
 E_2^2\le E_0D_3,\qquad E_3^2\le E_2D_3.
\]

Write their nonnegative defects as

\[
 F_1=E_0D_3-E_2^2,\qquad F_2=E_2D_3-E_3^2.
\]

The exact polynomial decomposition is

\[
 E_0D_3^3-E_3^4=F_1D_3^2+F_2(E_2D_3+E_3^2).
\]

Combining this with the earlier sharp 27/256 Young certificate gives, for
any nonnegative Landau coefficient K,

\[
\begin{aligned}
 256D_3^3\left(D_3+\frac{27}{256}K^4E_0-KE_3\right)
   ={}&27K^4\left[F_1D_3^2+F_2(E_2D_3+E_3^2)\right]\\
    &+(3KE_3-4D_3)^2
      \left[3(KE_3)^2+8KE_3D_3+16D_3^2\right].
\end{aligned}
\]

Every displayed right-hand term is nonnegative on an admissible physical
H³ path. The Lean module proves the individual upper budgets for each Cauchy
term, not merely their sum.

## Equality and the analytic frontier

If the physical fourth-moment inequality is saturated with positive E3 and D3,
then **both** Cauchy deficits vanish. Exact saturation in the sharp Young
inequality separately imposes the critical frequency ratio 3KE3=4D3.

Nothing here says such equality actually occurs for a nonzero Fourier density.
The missing analytic input is a **quantitative, dynamically controlled** lower
bound on one of these deficits or on the mismatch, sufficient to weaken the
quadratic energy-growth estimate. Thin frequency shells can make ordinary
Cauchy interpolation nearly sharp, so pointwise strictness by itself would
not close continuation.

## Workflow

Run `tools/audit/register_first_monomial_two_cauchy_spectral_defect244.py`,
`python3 proof/generate_index.py`, its `--check`, `proof/check_fragment.py --all`,
`lake env lean` on the new module, `lake build`, and the existing full baseline
audit before committing. The registration script is idempotent and inserts
no root-level shell scripts.
