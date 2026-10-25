# Fixed cofinal signed H³ transport or rapid energy decay

Base checkpoint: `906de954` — isolate signed physical H3 transport or fast energy decay.

The preceding exact physical Navier–Stokes H³ balance gives a cofinal disjunction:
for every strict left-terminal subtail and every real normalized rate B, there is
an actual time t where either

    E′(t) < -B E(t)

or

    B E(t) < -Transport(t).

The channels initially need not be identical for different rates or times.

## Quantifier-stable finite-channel cofinal selection

Because E(t) >= 1 for actual physical H³ energy, the two-channel
pigeonhole argument proves a *fixed* cofinal alternative. Either the negative
normalized physical energy slope has arbitrarily large magnitude on every
terminal subtail, or adverse normalized transport has arbitrarily large
magnitude on every terminal subtail. In the second case, if the first
property fails, one already has a late subtail and a finite rate bound B
excluding fast slope decay. Selecting the mixed alternative at max(B,C) then
forces transport above an arbitrary requested C in any later subtail.

The lemma is independent of PDE semantics and is specialized to the actual
physical H³ energy and transport. It does not invoke H³ nonextension.

## One-channel refinements

* A terminal lower bound E′ >= -B E turns the cofinal mixed obstruction into
  cofinal adverse signed transport above C E for any C.
* A terminal upper bound -Transport <= B E turns it into cofinal fast H³
  energy decay E′ < -C E for any C.

All terminal assertions remain conditional on a positive canonical terminal
kinetic mass and *failure* of the strong physical kinetic L² terminal trace.
The argument neither derives that failure from H³ nonextension nor excludes
its alternative. A further logical step can choose a single cofinal time
sequence for the selected channel and synchronize the physical signed
first-monomial spectral realization.
