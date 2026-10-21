# A fixed cofinal obstruction in the canonical H³ signed cubic

Base: `ef3fae35` — *transfer exact physical H3 signed energy rate to canonical weighted spectral cubic*.

Let `E(t)` denote the original physical H³ energy, `D(t)` the physical H³ dissipation, `G₃(U(t))` the canonical 972-term gradient contribution, and `M₃(U(t))` the signed 243-slot interpolation contribution. The physical third-order transport is now identified pointwise on the energy-class tail:

\[
T_3(t)=G_3(U(t))+3M_3(U(t)), \qquad
E'(t)+2D(t)\le 24C_1\sqrt{E(t)}E(t)-T_3(t).
\]

Define the **remaining signed budget** at normalized threshold `M ≥ 0`:

\[
B_M(t)=24C_1\sqrt{E(t)}E(t)-(4422+M)E(t)-2D(t).
\]

Under hypothetical nonextension, the previous checkpoint gives, for every strict terminal subtail and every `M ≥ 0`, an instant with

\[
G_3(U(t))+3M_3(U(t))<B_M(t).
\]

By elementary addition, at each such instant at least one of the following must hold:

\[
G_3(U(t))<\tfrac12B_M(t),\qquad
3M_3(U(t))<\tfrac12B_M(t).
\]

The new **fixed cofinal channel** theorem proves something stronger than an instant-by-instant disjunction. One of these *same two* inequalities holds at a possibly different time for **every** pair consisting of a strict terminal subtail and a nonnegative threshold, without switching its selected channel:

\[
\begin{aligned}
&[\forall d\in(a,T),\;\forall M\ge0,\;\exists t\in(d,T):G_3(U(t))<B_M(t)/2]\\
&\quad\text{or}\\
&[\forall d\in(a,T),\;\forall M\ge0,\;\exists t\in(d,T):3M_3(U(t))<B_M(t)/2].
\end{aligned}
\]

The proof uses threshold monotonicity `B_N(t)≤B_M(t)` for `M≤N` and cofinality of `max(d,d₀)` in the tail and of `max(M,M₀)` among thresholds. No new PDE assumptions or spectral estimates are introduced.

**Two-channel sufficient criterion.** If both reversed half-budget inequalities hold throughout an energy-class tail at `M=0`, their sum supplies the full canonical signed-cubic dominance criterion from `ef3fae35` and therefore smooth continuation. This is a conditional sufficiency result and does not establish either half-bound.

**Important limitation.** The budget `B_M` need not be negative. Thus this result neither asserts `G₃ < 0` nor `M₃ < 0`, and does not prove unconditional continuation. The remaining hard analytic step is a genuine one-sided signed inequality ruling out both cofinal alternatives using the physical constraints of the canonical spectral state. Any claim that the two terms cancel or each has a favorable sign requires an independent proof.

Lean module: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdSignedChannelAlternative244.lean`.
