# Real-solenoidal Schwartz canonical E₂/E₃ and signed limit

Base commit: `9df14de7` (*match physical second and third jets along real solenoidal Schwartz H3 density*).

The prior proof constructs one physical real solenoidal Schwartz family `Ψ n`
and a convergent weighted H³ spectral sequence `V n`, with every one of the
27 second and 81 third literal derivatives matched exactly to the canonical
physical `L²` jets. The current increment uses those exact identities to
identify the original spatial Schwartz energies with the canonical spectral
energies, and obtains a common E₂/E₃-Cauchy tail from their finite-product
continuity. It then constructs `WeightedH3MatchedSchwartzCompletion244` from
**the same solenoidal family**, rather than switching to the unconstrained
family selected earlier by choice.

The main theorem `exists_thirdFullRealSolenoidalSchwartz_canonicalEnergySignedLimit244`
keeps the weighted convergence, exact physical divergence and Fourier
representative equations; states the exact `E₂` and `E₃` energy equalities at
every `n`; proves convergence to the canonical 27- and 81-slot energies of
the target; proves E₂/E₃ difference-energy Cauchyness; and proves convergence
of the signed 243-slot real Schwartz first monomial to
`weightedH3CanonicalSignedFirstMonomial244 target`.

The signed functional is the existing choice-independent completed Schwartz
observable. The theorem does **not** equate that observable to the nonlinear
physical Navier–Stokes transport at an arbitrary preterminal time slice. It
is not a continuation or finite-time regularity theorem.

All statements are formulated over the project's `Depth.three` axis carrier,
with no new dimensional constant or reordering of derivative slots.

## Compile and audit

The provided run script calls the registrar with `--apply` and `--check`,
regenerates and checks the proof index, compiles the new Lean module, checks
all fragments, runs the full build, and commits on passing. Lean compiler
verification is required on the project host.
