# Real solenoidal Schwartz recovery of the actual physical H³ PDE transport

Base: `8da99c60` — identify canonical E₂/E₃ energies and signed H³ transport along solenoidal Schwartz density.

## Mathematical content

**The physical/canonical transport identity is not new.** It was established
independently by `h3PhysicalFullThird_eq_weightedCanonical244`, after closing
the physical signed 3–2–2 and gradient 3–3–1 traces. The remaining gap was to
show that the *specific real, exactly divergence-free Schwartz approximants*
constructed in the H³ density theorem share that same **full physical**
nonlinear limit, rather than merely the signed component's canonical limit.

`thirdFullSolenoidalSchwartz_pointwiseDecoderMatch244` applies the already
compiled pointwise uniqueness theorem to the exact real L² decoder, producing
a precise C¹ realization of each actual Schwartz field by its own weighted
spectral state. No new pointwise property of an arbitrary L² representative
is assumed.

`thirdFullSolenoidalSchwartzGradientCompletion244` combines the same
sequence's second- and third-order exact L² jet matching with its derived
pointwise decoder realization. The existing automatic gradient-gauge theorem
then produces a valid `H3MatchedSchwartzGradientCompletion244` with the SAME
solenoidal Schwartz family, not a newly selected reference family.

The main theorem
`exists_thirdFullPhysicalSnapshot_solenoidalSchwartzTransportLimits244`
specializes to an interior Fourier-compatible physical H³ Navier–Stokes
snapshot. The snapshot's spectral incompressibility follows from the
preterminal Navier–Stokes admissibility; raw Hermitian reality follows from
physical real-data Fourier compatibility. It constructs one real solenoidal
Schwartz sequence with:

* Strong weighted-H³ approximation and exact a.e. weighted Fourier state.
* Pointwise spatial divergence zero.
* Exact 27/81 slot real Schwartz E₂/E₃ matching, and convergence to the
  canonical physical-jet energies.
* The full 972-term gradient Schwartz scalar converging to the actual old
  `thirdOrderGradientTransportSum u t`.
* The full 243-slot signed Schwartz scalar converging to the actual old
  `h3PathCanonicalFirstMonomialAggregateAt u t`.
* Their original `G₃ + 3M` combination converging to
  `velocityH3TransportDerivative3At u t`.

The gradient/signed physical identities are reused and not re-proved.
The equality is of the nonlinear top-transport functional at admissible
Fourier-compatible time slices. It does **not** establish a favorable sign,
endpoint H³ bound, finite dissipation, or Navier–Stokes continuation.

## Verification

The registrar checks for one definition, two theorems and six `#check` /
`#print axioms` entries. Lean elaboration and the full build must run on the
project host; they have not been verified in the packaging environment.
