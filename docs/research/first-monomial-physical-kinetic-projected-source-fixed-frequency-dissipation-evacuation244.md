# Fixed-frequency dissipation evacuation on the four-channel witness

Base commit: `acf1e935`.

Under the previously proved terminal alternative, one sequence approaching T satisfies
`(n+1) D_low(n+1,t_n) < D_high(n+1,t_n)`. The exact physical radial
partition implies `D(t_n)>0` and normalized moving-cutoff low share is
strictly below `1/(n+2)`.

Because the Fourier dissipation density is nonnegative, the low-cutoff
integral is monotone in the cutoff. For every **fixed** `rho >= 0`,
once `n+1 >= rho`,

    0 <= D_low(rho,t_n)/D(t_n)
       <= D_low(n+1,t_n)/D(t_n) < 1/(n+2).

Thus one and the same sequence has `D_low(rho,t_n)/D(t_n) -> 0`
for **every** fixed finite cutoff rho. This is the weak escape of the
normalized spectral H3 dissipation distribution from all compact Fourier
balls (no measure-level convergence framework is assumed).

The stronger terminal dichotomy retains the strong kinetic L2 trace with its
exact canonical kinetic mass. The no-trace consequence explicitly assumes
positive canonical terminal kinetic mass. No control over temporal persistence,
terminal dissipation integrals, or smooth continuation is claimed.
