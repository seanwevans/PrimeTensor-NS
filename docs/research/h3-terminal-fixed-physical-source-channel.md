# Fixed physical source-channel obstruction from missing terminal L² trace

Base: `a66e714b57b1433ddb93b5b6000cc58ad0c89241`.

## Main result

Under `LoggedPreterminalH3PathAdmissible` and failure of a strong physical
`L²` terminal velocity trace, there exists a **single fixed choice** between

- the genuine inverse-Fourier physical Laplacian source, and
- the inverse-Fourier physical Leray nonlinear source,

such that on **every** positive terminal interval `(b,T)` the chosen source
is not Bochner `L¹`, and for every amplitude `M` its physical `L²` norm
exceeds `M` at a later time in that interval.

Unlike the prior varying alternative, the channel cannot change with the
terminal cutoff or threshold. No positive terminal kinetic mass, full H³
energy-class hypothesis, or finite dissipation is assumed.

## Why the same channel persists

If both sources were integrable on *some* terminal tails, their starting
times could be replaced by their maximum. Both sources would then be
integrable on a common later tail, forcing their difference (the actual
projected momentum source) to be integrable and hence the velocity to have
a strong terminal trace. Contradiction.

Continuity of each physical source on `(0,T)` is already established by
continuity of the actual weighted spectral state and the reconstructed
physical Laplacian/Leray maps. Consequently a fixed source that fails L¹ on
all tails cannot be bounded on any such finite interval.

## Limitations

This gives a fixed *two-term* physical-source channel, not a fixed spatial
coordinate, Fourier annulus, or direction of the source; the latter require
new concentration or compactness arguments. The theorem is conditional on
missing physical L² trace; it does not show such a failure occurs. Existing
Fourier/source identification assumptions enter through the preterminal H³
path theory and must remain visible in a global-regularity claim.

## Build

Run `lake build PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedPhysicalSourceChannel`,
then the registrar, source index, root audit and baseline. A local pinned
Lean build is required; this package is not certified by the packaging host.
