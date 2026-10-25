# Moving radial spectral concentration: a dominant high-frequency fraction

**Base:** `b33d9f8d` — derive moving radial H3 spectral mass and physical dissipation cascade.

## The new quantitative selection

Write `G(t) = h3AuditActualSpectralVelocityTotal hH3 t`,
`R_n = n+1`, and use the exact complementary integral definitions

- `LowMass_R(G) = integral_{|D|<R} sum_j |G_j|²`,
- `HighMass_R(G) = integral_{|D|>=R} sum_j |G_j|²`,
- `TotalSquare(G) = LowMass_R(G) + HighMass_R(G)`.

Fix the anchor `b=(a+T)/2`. Physical order-zero kinetic monotonicity gives
`E0(t)<=E0(b)` for `b<t<T`. Consequently the proved radial ceiling gives

    LowMass_R(G(t)) <= K(R) E0(b),
    K(R)=1+R²+R⁴+R⁶.

Under positive terminal kinetic mass and *failure of the strong physical L²
terminal trace*, high-radial H3 mass exceeds every threshold arbitrarily
close to T for each fixed radius. For the nth selection, set R=R_n and choose

    HighMass_Rn(G(t_n)) > R_n * (K(R_n)*E0(b) + 1),
    T-t_n < 1/R_n.

The same time has

    R_n LowMass_Rn(G(t_n)) < HighMass_Rn(G(t_n)),
    (R_n+1) HighMass_Rn(G(t_n)) > R_n TotalSquare(G(t_n)).

Thus its fraction of *total weighted H3 square energy* lying at frequencies
|D| >= R_n is strictly larger than `R_n/(R_n+1)`, hence approaches 1 along
the selected times. This does NOT mean kinetic L² mass fraction tends to 1;
the two measures use different Fourier weights.

Finally, the previously formalized exact spectral dissipation inequality
`D_H3(t_n) >= R_n² HighMass_Rn(G(t_n))` implies
`D_H3(t_n)>R_n³`. The actual lower bound from our stronger threshold is
`D_H3(t_n)>R_n³*(K(R_n)*E0(b)+1)`; the Lean statement retains the simpler
cubic consequence, while the proof preserves the dominating high-mass
inequality.

## Interpretation and unresolved issue

This is a necessary concentration mechanism on the *no physical strong L²
trace* branch. It does not prove that branch occurs for nonextending H3 paths,
nor contradict nonextension. It isolates a stronger target for future PDE
control: a dynamical bound preventing arbitrarily large proportions of the
weighted H3 square energy from moving beyond growing cutoffs at terminal times.
