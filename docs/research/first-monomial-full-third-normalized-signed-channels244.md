# Normalized signed third-order H³ channel obstruction

Base checkpoint: `2d938161` — isolate fixed cofinal signed H3 gradient or interpolation obstruction.

## Exact algebra

At an admissible physical time, let `U(t)` be the path's canonical weighted spectral state, `E(t)` its positive actual H³ energy, and `D(t)` its physical dissipation. The completed physical third commutator is exactly

\[
C_3(U)=G_3(U)+3M_3(U).
\]

Define two REAL signed *normalized excess rates*

\[
\begin{aligned}
X_G(t)&=12C_1\sqrt{E(t)}-2211-\frac{G_3(U(t))+D(t)}{E(t)},\\
X_I(t)&=12C_1\sqrt{E(t)}-2211-\frac{3M_3(U(t))+D(t)}{E(t)}.
\end{aligned}
\]

Then the equality of scalars, not an estimate, is

\[
S_3(t)-4422=X_G(t)+X_I(t),\qquad
R_3(t)=\max\{0,X_G(t)+X_I(t)\}.
\]

The physical `2 D(t)` dissipation is accounted for exactly (one `D` in each channel), and the factor `3` remains attached to the signed interpolation block.

## Transfer from the cofinal signed half-budget theorem

The preceding theorem says that under **hypothetical nonextension**, a fixed channel falls below half of the physical budget at every arbitrarily late terminal threshold. The budget is

\[
B_L(t)=24C_1\sqrt{E(t)}E(t)-(4422+L)E(t)-2D(t).
\]

The new exact quotient identities show

\[
\frac{B_{2K}(t)/2-G_3(U(t))}{E(t)}=X_G(t)-K,
\qquad
\frac{B_{2K}(t)/2-3M_3(U(t))}{E(t)}=X_I(t)-K.
\]

Since `E(t)≥1`, each half-budget failure at threshold `2K` yields a **strict** normalized rate excess above `K`.

Consequently, if an admissible physical H³ path fails to extend, **one fixed choice** (either `X_G` or `X_I`) is unbounded above on every strict terminal subtail. For any preselected strict terminal subtail one can choose a natural-number-indexed collection of actual times `t_n` in that subtail with `X_channel(t_n)>n`. No temporal monotonicity is asserted for those times.

Conversely, if both normalized channel excess rates have any finite upper bounds on some common strict terminal subtail, smooth continuation follows from the original physical criterion by contradiction.

## Critical interpretation

These normalized growth-rate obstructions are NOT claims that the gradient cubic or interpolation cubic becomes negative. An excessive `X_G` or `X_I` can result from the growing `12 C₁ √E` term. The static full-third Schwartz sign obstruction elsewhere in the repository already rules out naïve uniform coercivity over all solenoidal Schwartz snapshots. To close continuation one needs a *dynamical* constraint coupling the actual Navier–Stokes flow with its signed cubic, not a global static inequality obtained from these algebraic rewrites.

Source: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdNormalizedSignedChannels244.lean`.
