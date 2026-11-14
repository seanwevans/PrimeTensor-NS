# Exact signed highpass source work and viscous/Leray separation

Base: `b17c35cb0` — forced one-sided selected outer highpass drain.

## Exact physical momentum polarization

For each positive-time selected annulus, let `H_x=P_{>=rho}u(x)`,
`J_rho=P_{>=rho}(integral_x^s F(t)dt)`, and `M_t=||P_{>=rho}u(t)||_2^2`,
where `F=Delta u - Leray div(u tensor u)` is the actual projected physical
Navier–Stokes momentum source. The unconditional strong physical Bochner FTC
and the sharp-highpass linearity imply `P_{>=rho}u(s)=H_x+J_rho`.
Hence *exactly*

    M_x - M_s = -2 <H_x,J_rho> - ||J_rho||_2^2
              = 2 W_rho - S_rho^2,

where `W_rho = -<H_x,J_rho>` and `S_rho=||J_rho||_2`.

No Cauchy bound, source-smallness premise, or artificial positive
quadratic error remains. A strict highpass kinetic drain forces
`W_rho>0`; this is an inward direction of physical momentum action,
not merely a large norm of `J_rho`.

## Full early-anchored nonlinear residual

Under the existing selected strict kinetic excess, positive initial
annular deficit, actual deficit drop `epsilon>0` and no signed increase
of the original Young-width cost, the earlier exact polynomial identity
and one-sided signed-slope positivity give

    epsilon < K_rho,sigma,x (M_x-M_s)
            = K_rho,sigma,x (2 W_rho - S_rho^2),

    K_rho,sigma,x = 2 rho^6 sigma^4 M_x.

This retains the entire original deficit drop, but still requires
control of the frequency-weighted signed physical source work.

## Actual viscosity and nonlinear projected-source split

The positive-time strict H3 physical path makes both the actual
physical Laplacian source `D(t)` and the actual Leray forcing `N(t)`
Bochner-integrable over every interior ordered interval. The projected
momentum source is `F=D-N`. Thus with `J_D=int_x^s D`, `J_N=int_x^s N`,

    W_rho = -<H_x,P_{>=rho}J_D> + <H_x,P_{>=rho}J_N>.

A positive highpass drain forces **at least one** of these two summands
strictly positive. There is deliberately no sign assigned to the
cross-time viscosity contribution: fixed-initial-state Laplacian work
need not have a pointwise dissipation sign without an additional
heat-flow/commutator argument.

## Remaining frontier

A stronger frequency-weighted estimate for
`rho^6 sigma^4 M_x (2W_rho-S_rho^2)` must come from genuine spectral
coercivity, a signed transfer bound, or triad cancellation. Finite H3
dissipation alone does not imply that this weighted quantity vanishes.
No endpoint continuation is asserted.

## Audit

New module: 10 theorem declarations and 1 noncomputable definition.
The Lean files contain no new axiom, sorry, or admit. The archive and
registration can be checked without Lean; compilation and proof audit
must be run with the pinned Lean/mathlib environment.
