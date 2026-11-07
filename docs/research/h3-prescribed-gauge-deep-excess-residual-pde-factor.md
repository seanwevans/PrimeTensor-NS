# Deep-excess residual physical PDE square-height barrier

**Base:** `c64904fa9bd4d2da37ecd1eb466f77ad78e9fcc3`.

The cofinal residual certificate retains the exact actual H³ two-clock
overlap envelope, the *same* second finite-band cutoff `J2`, and attained
secondary source/state norm maxima. Write `A=V/(2P)`, `B=integral_m^T D_H3`,
`R=96*C0*(J+2)^5`, `H=A/(24 sqrt(R B))`, and `E=B-eta1*A-L*A`.

Under the actual two-slice rate, kinetic gap and **deep excess** condition
`48 sqrt(R B) <= 1`, the secondary floor satisfies `A <= H/2`, so the
previous residual physical PDE gate yields

    (T-s)*H <= 8*B
    OR
    H^2 <= (96*K2*C2*(J2+2)^5 + 4)*B.

The first arm constrains terminal-clock width relative to the *full height*
`H`, not just absolute proximity to T. The second arm forces actual physical
source/state/frequency amplification if the height remains large compared
with the dissipation tail. Neither cutoff nor physical maxima is assumed
uniformly bounded, and no global Navier--Stokes regularity is asserted.

The cofinal lift keeps the same original minimal crossing witnesses,
frequency escape, disjoint viscous charges, and existing residual ledger.
No `sorry` or unproved axioms are added. The pinned Lean toolchain must
compile the new file on the user's repository.
