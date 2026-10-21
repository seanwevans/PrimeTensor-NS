# Fixed signed H³ channel obstruction against integrable envelopes

Checkpoint: `1d13735c` — strengthen normalized signed H3 channels to fixed essential terminal obstruction.

## New result

For the genuine H³ path and the actual canonical weighted spectral state, let

\[
X_G=12C_1\sqrt E-2211-(G_3+D)/E,\quad
X_I=12C_1\sqrt E-2211-(3M_3+D)/E.
\]

Their exact signed sum remains `S₃ - 4422`, and the measurable physical unabsorbed rate satisfies

\[
0\le U(t)\le [X_G(t)]_++[X_I(t)]_+.
\]

Suppose both channels had almost-everywhere upper majorants `r_G(t)` and `r_I(t)` integrable on a strict terminal tail. Then

\[
U(t)\le |r_G(t)|+|r_I(t)|\quad\text{for a.e. }t
\]

on the same tail. The right side is integrable; this contradicts the *previously formalized physical* non-domination of the Riccati rate under hypothetical nonextension. No measurability of `X_G` or `X_I` is used.

A nested-tail two-channel selection strengthens this into one fixed choice of `X_G` or `X_I`, made **before** both the terminal subtail and the integrable candidate envelope: on every strict terminal subtail, this channel cannot be almost-everywhere bounded above by *any* integrable time-dependent function. In particular it cannot be hidden under an integrable exceptional growth allowance, not merely under a fixed constant ceiling.

Conversely, integrable time-dependent almost-everywhere envelopes for both channels on one strict terminal tail suffice for smooth continuation, even if the spectral channel functions are not separately measurable.

## Interpretation and limitation

This is a conditional necessary obstruction and an improved continuation **criterion**. It supplies no universal signed spectral bound and does not resolve Navier–Stokes regularity. The existing static Schwartz counterexamples also rule out trying to close it with a universal fixed-coefficient spatial absorption inequality. The missing input remains a genuinely dynamical control on actual NS paths.

Source: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdIntegrableMajorantObstruction244.lean`.
