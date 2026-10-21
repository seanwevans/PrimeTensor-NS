# Exact physical Fourier variance secant and finite-rate signed-excess obstruction

Base checkpoint: `00c72d01` — compare physical H³ Fourier variance by signed middle-moment excess.

## Mean value: the exact missing quantitative rate

The physical normalized Fourier Cauchy variance is

    R(t) = 1 - E₂(t)^2/(E₀(t)D₃(t)),

where `E₀` is actual kinetic Fourier mass, `E₂` the actual weighted
second moment, and `D₃` the actual fourth-radial Fourier dissipation.
The previous module provides the pointwise derivative identity

    R'(r) = -X(r)/(E₀(r)D₃(r))²,

with `X` the named signed middle-moment excess assembled from **closed
physical energy derivatives** and the actual fourth-radial Hilbert pairing.

The scalar function is differentiable at every strict physical time where
`E₀,D₃>0`. For any `s<t` in the same energy class, assuming those two
positive quantities on the closed interval `[s,t]`, the real mean-value
theorem supplies an `r∈(s,t)` with the **exact** equality

    X(r)/(E₀(r)D₃(r))² = (R(s)-R(t))/(t-s).

This is strictly stronger than the previous existence of some positive
`X(r)` when normalized Fourier variance falls: it specifies the necessary
**average concentration rate**. It does not assert any new regularity of
`X` or an unproved integrability statement; no signed transport sign is
assumed.

## Finite-rate anti-concentration comparison

If, at every interior time, the actual normalized signed rate is at most
`M`, the mean-value identity implies

    R(s)-R(t) ≤ M(t-s).

Thus a uniform time-rate ceiling constrains Fourier concentration. This
is conditional on that specific ceiling, not an assertion that Navier--Stokes
provides it for free. A drop of at least `η` requires an actual interior
normalized excess rate at least `η/(t-s)`.

## Sharp Young gap consequence

At a later time t with `K>0` and physical sharp Young gap bounded by `δ`,
prior work gives

    27 K⁴ E₀(t) R(t) ≤ 256 δ.

Substituting the finite-rate floor for `R(t)` yields the new necessary
condition

    27 K⁴ E₀(t) [R(s)-M(t-s)] ≤ 256 δ.

This reduces to the previous nonpositive-excess gap obstruction for `M=0`,
but permits a **finite positive** middle-moment growth rate. If future PDE
estimates bound that rate in terms of the physical transport and dissipation,
this form can be combined with terminal data. The current result does not
establish such a uniform PDE bound or global NSE regularity.

## Audit

The registrar imports the module in `PrimeTensor.lean` and the central
`FirstMonomialTriad` audit, and adds `#check` and `#print axioms` for the one
definition and four new theorems. Regenerate proof index, run fragment
checks, compile the module, central audit and full library, then run the
baseline audit before committing.
