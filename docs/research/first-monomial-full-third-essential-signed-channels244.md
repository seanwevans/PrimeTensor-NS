# Essential signed-channel obstruction at the physical H³ endpoint

Base checkpoint: `f7ed53b1` — **normalize fixed cofinal signed H3 channels and extract high-rate sequences**.

The previous checkpoint established the exact rate identity

\[
 S_3-4422 = X_G+X_I,\qquad
 X_G=12C_1\sqrt E-2211-\frac{G_3+D}{E},\quad
 X_I=12C_1\sqrt E-2211-\frac{3M_3+D}{E}.
\]

The fixed-channel high-rate sequence theorem is pointwise. It does **not**
exclude the possibility of very narrow time spikes of measure zero.

## New measure-theoretic obstruction

The old, physically measurable, unabsorbed Riccati rate `U(t)` satisfies

\[
0\le U(t)\le \max(0,X_G(t))+\max(0,X_I(t))
\]

at every strict H³ energy-class time. The old essential barrier shows that
hypothetical nonextension precludes an almost-everywhere finite upper bound
on `U` on every strict terminal subtail. Consequently on any such subtail,
for every real `M`, at least one of `X_G` or `X_I` fails to be `≤ M` almost
everywhere. Nested-tail selection then fixes the same channel for *all*
subtails and thresholds:

\[
 \bigl[\forall d\in(a,T),\ \forall M\in\mathbb R,\
 \neg(X_G\le M\ \text{a.e. on }(d,T))\bigr]\quad\lor\quad
 \bigl[\forall d\in(a,T),\ \forall M\in\mathbb R,\
 \neg(X_I\le M\ \text{a.e. on }(d,T))\bigr].
\]

This is essential unboundedness: each failed a.e. bound forces a *non-null*
set of violating times. It gives no uniform lower bound on its measure.
The theorem does **not** claim that either individual spectral channel is
measurable; the a.e. statements themselves are well-defined without it.

## Continuation and temporal integrability

If the positive parts of *both* normalized channels are integrable on a
strict tail, their sum provides an integrable upper majorant for the old
measurable physical Riccati rate. The old continuation theorem then applies.
Contrapositively, under nonextension, one fixed positive-part channel must
fail integrability on every strict terminal subtail.

## Still open

None of these implications proves a uniform signed bound. The old static
Schwartz concentration counterexample precludes simply bounding the entire
adverse cubic by fixed multiples of H³ dissipation and energy. The remaining
work needs a dynamical mechanism from actual Navier–Stokes evolution that
excludes the fixed-channel essential obstruction, not merely an abstract
static estimate or pointwise witness.

New source module:
`PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdEssentialSignedChannels244.lean`.
