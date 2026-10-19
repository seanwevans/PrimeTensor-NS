# From Schwartz zeroth-order spectral realization to physical first jets

**Base:** `d691d2e7` — derive Schwartz first jet Linf control from spectral H3 convergence.

The previous `H3SchwartzSpectralFirstJetComparison244` carries two independent
pointwise first-derivative matching assumptions: identification of the target
Schwartz derivative with the canonical spectral C1 representative derivative,
and identification of each derivative difference with the derivative of the
spectral difference state.

These assumptions are **not logically independent** of underlying zero-order
realization. This module proves both identities from

    h3SchwartzPoint3Scalar f = h3SpectralScalarRealC1RepresentativeOnPoint3 S

for each approximate and target component. The proof uses the actual
`h3Point3ToFourierCLM` / `WithLp.ofLp` carrier roundtrip and
`h3SchwartzPoint3Scalar_spatial_d`, not a surrogate scalar field.
Subtraction uses the already-proved
`h3SpectralScalarRealC1RepresentativeOnPoint3_sub` and
`schwartzLineDeriv_sub244`; no commutation of arbitrary distributional
derivatives or new assumptions of differential equality are introduced.

The resulting theorem
`thirdFullSchwartz_firstJetComparison_of_zerothRealization244`
constructs the earlier comparison record automatically. Thus strong weighted
spectral H3 difference convergence and third-jet L2 convergence imply
convergence of the complete actual four-gradient-term, 243-slot signed
Schwartz 3+3+1 transport through the earlier quantitative L2–L2–L∞ estimate.

## Still outstanding

The zero-order **exact** realization of the approximating Schwartz velocity by
weighted spectral states remains explicit. The automatic realization of
arbitrary physical H3 slices, third-jet L2 graph density, mixed second-jet
continuity for the interpolation channel, fourth-jet dissipation limits, and
identification of the final signed limit with the actual PDE transport are
not proved in this module. No global NS regularity claim follows.
