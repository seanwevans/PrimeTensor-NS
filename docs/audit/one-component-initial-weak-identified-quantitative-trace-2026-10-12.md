# Identification of quantitative initial physical momentum and kinetic limits

Base checkpoint: `077a47fd` — derive quantitative initial physical kinetic energy convergence rate.

New Lean file:
`PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialWeakIdentifiedQuantitativeTrace.lean`

The earlier subcritical-energy theorems derive a *strong* physical L² right limit `L`, but do not identify that limit with the time-zero physical data. This module adds an independent **weak** initial Hilbert pairing trace against every test in the actual three-component physical L² space. Strong convergence to `L` automatically implies convergence of every pairing to `inner L ψ`. Uniqueness of scalar real limits and the real Hilbert norm-square identity force `L = actualInitialPhysicalHilbertAtZero`.

The module also proves the exact time-zero norm identity `‖actualInitialPhysicalHilbertAtZero‖² = velocityH3Energy0At u 0`. Thus the already derived quantitative moment and kinetic limits can be rewritten with the actual stipulated initial physical velocity and kinetic energy:

`‖old(t) - old(0)‖ ≤ δ(t)`

`|E₀(t) - E₀(0)| ≤ δ(t)*(2*‖old(0)‖+δ(t))`

where `δ(t) = ((3 + C_L) M) * t^(1-α)/(1-α)`, for `0 ≤ α < 1`, on an initial strict interval.

No physical strong trace, time-zero momentum FTC, or nonlinear old/selected relative-energy residual is assumed. The **weak initial pairing condition**, the subcritical H³ growth assumption and old temporal joint continuity are separate unresolved analytic hypotheses; nothing is established unconditionally from the bare H³ path class. The terminal vorticity endpoint is independent.

This package was checked for ZIP integrity; the Lean files have not been typechecked in the assistant's environment.
