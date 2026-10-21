# Sharp top-Fourier Young constant in the kinetic-anchored H³ corridor

Base: `fc09fb54` — essential top-frequency Landau corridor.

## Analytic improvement

The previously formalized physical moment interpolation gives

\[
 E_3^4 \le E_0 D_3^3.
\]

For any nonnegative \(K\), the exact sharp fourth-power Young bound is

\[
 K E_3-D_3\le \frac{27}{256} K^4 E_0.
\]

Unlike the earlier bound \(K E_3-D_3\le K^4E_0\), this spends **one
full unit** of top-order dissipation with optimal constant \(27/256\). The
polynomial certificate is

\[
27x^4-256(x-d)d^3=(3x-4d)^2(3x^2+8xd+16d^2)\ge0.
\]

Equality in the abstract cone occurs for \(x=27/64\), \(d=81/256\),
\(b=1\). Sharpness refers to the abstract fourth-moment inequality;
no Navier–Stokes state saturating all physical estimates is asserted.

With \(K(t)=4398C_1\sqrt{E(t)}\), the previously introduced
\(\mathcal L(t)=(K(t)E_3(t)-D_3(t))/E(t)\) obeys

\[
 \mathcal L(t)\le\frac{27}{256}\frac{K(t)^4E_0(t)}{E(t)}.
\]

Kinetic energy monotonicity on the path gives \(E_0(t)\le E_0(b)\), hence

\[
 \mathcal L(t)\le\frac{27}{256}(4398C_1)^4E_0(b)E(t),
\]

and the actual physical energy evolution has the bound

\[
 E'(t)\le K_b E(t)+\frac{27}{256}(4398C_1)^4E_0(b)E(t)^2,
 \qquad K_b=(3C_1+441C_1^2)E_0(b).
\]

This is a *quantitative* improvement but still has a quadratic energy term.
It cannot, by itself, prove global regularity or rule out a terminal
obstruction. Additional dynamical cancellation or a genuinely subcritical
estimate remains necessary.

## Registration and checks

Run `tools/audit/register_first_monomial_sharp_top_fourier_young244.py` and
then `python3 proof/generate_index.py`, `--check`, and `proof/check_fragment.py
--all` before the Lean builds. Run the full baseline audit before committing.
