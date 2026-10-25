# Quantitative physical H³ radial dissipation windows

Base commit: `7ca8bed5` (`extend terminal H3 dissipation evacuation to growing subcutoffs`).

The existing four-channel witness gives, at `R_n=n+1`,

    R_n D_low(R_n,t_n) < D_high(R_n,t_n),
    D(t_n)=D_low+D_high>0.

The preceding subcutoff module proved `D_low/D < 1/(n+2)` at each t_n,
and local persistence of that *ratio* under continuity of the two scalar
physical dissipation functions.

The new scalar algebra retains an absolute height. Under `R>=2`, a partition
`L+H=D`, `L/D<1/R`, and `D>D_0/2`,

    H > D_0/4.

Continuous low-share and total dissipation guarantee positive local windows
about each t_n with exactly those inequalities; hence the *actual high
radial Fourier dissipation* stays above `D(t_n)/4` on the local interval.
The terminal sequence is the same one supplied by the four-channel result.

An independent finite-interval lemma states

    f(r)>=m on [s,t], s<=t, interval-integrable f
       => (t-s)*m <= integral_s^t f(r) dr.

This isolates the quantitative temporal frontier. Integrating on the selected
windows requires local time-integrability of the physical high dissipation,
which is not established by these declarations. A terminal obstruction also
requires quantitative **width** or summability/disjointness information:
positivity of each width alone does not imply any positive total integrated
cost.

No claim is made that continuity of full physical H³ dissipation or its
finite-frequency truncation has already been deduced from the minimal
`LoggedPreterminalH3PathAdmissible` structure; those are explicit hypotheses.
