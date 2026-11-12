# Actual annular Young-gap ledger: physical source and viscous-rate outer budget

**Accepted parent:** `34dedb843f245a005984e93de7af0f7ede69190e` — connect physical kinetic rigidity to annular Young gap and outer tail.

## Hard mathematical increment

The accepted sharp Plancherel/anti-heat result has a fully physical kinetic
excess on its left and a genuine three-component Fourier outer-tail square on
its right. A Fourier-tail error is not yet a quantity that existing physical
viscous clocks can charge. This increment identifies a physical upper ledger
*without assuming* that temporal dissipation has any pointwise ceiling near T.

For each actual strict `t`, each `0 <= rho <= sigma`, and kinetic anchor `b<t`:

* `U(t)` is the actual three-component physical velocity in real L2.
* `R(t)` is the actual projected physical Navier--Stokes momentum source.
* `P_sigma` is the accepted componentwise real sharp Fourier cutoff.
* `rate=(rho^2+sigma^2)/2`; `E=velocityH3Energy0At u b`.
* `D=velocityH3DissipationAt u t` is the actual **full H3 dissipation**.
* `C=(3+h3AuditInitialLerayEnergyCoefficient)*(1+6 E+3 D)`.

The true outer mismatch obeys the Plancherel and Hilbert Young inequalities:

    sum_j integral_{m>=sigma} |Rhat_j-rate*Uhat_j|^2
       = ||(I-P_sigma)R-rate*(I-P_sigma)U||_2^2
       <= 2||(I-P_sigma)R||_2^2
            +2 rate^2 ||(I-P_sigma)U||_2^2
       <= 2 C^2+2 rate^2 E.

The final bound uses two accepted physical facts: (i) the sharp highpass
is an L2 contraction by exact low/high Pythagoras; (ii) the projected physical
source norm is <= C by the physical full-H3 dissipation estimate. The
velocity highpass is <= sqrt(E) by actual order-zero kinetic monotonicity.

The package retains the exact bounded-annulus Young gap G_ann and the width
expenditure W_ann. It defines the explicit *physical-viscous outer budget*

    B_outer(t) = 2 C(t)^2 + 2 rate^2 E

and derives the same physical kinetic-excess gate with its Fourier-tail cost
replaced by this actual physical bound:

    rho^6 * (rate*M - K)^2
      <= M * [ 2 G_ann + W_ann + rho^6 B_outer(t) ]

under the accepted nonnegative-excess hypothesis `K <= rate*M`, where
`M=||(I-P_rho)U||_2^2` and `K=3 sqrt(E)*Ckin(rho,E)`.

## Why this does NOT yet close a disjoint viscous clock

`C(t)` is affine in `D(t)`, so `C(t)^2` is **quadratic** in the instantaneous
full-H3 dissipation. Even if the selected original disjoint viscous clocks
have finite total `integral D(t) dt`, this alone does not bound their total
`integral D(t)^2 dt`. Moreover the annular Young-gap and width expenses have
not been charged to those disjoint windows. One must establish an independent
square-integrable/source-persistence or localization mechanism, and keep the
selected disjoint times/windows consistent throughout. Replacing `D^2` by
`D` silently would be mathematically invalid.

No continuation, terminal-uniform source ceiling, or new PDE axiom is claimed.
All Lean declarations are proof candidates until compiled in the pinned
project toolchain. The six theorems and two definitions are registered for
`#check` and `#print axioms` auditing.
