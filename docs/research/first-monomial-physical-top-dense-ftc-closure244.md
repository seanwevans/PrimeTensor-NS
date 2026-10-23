# Dense-time closure of the actual projected Hilbert FTC defect

Baseline: `416a5cb2` (physical defect weak determination).

The existing continuous H³ spectral decoder gives `ContinuousOn U (0,T)` in physical L², and the existing actual projected-RHS theorem gives `ContinuousOn R [a,b]` for `0<a<b<T`. Its Bochner primitive `J(r)=∫_a^r R(s) ds` is continuous on the same interval, so `D(a,r)=U(r)-U(a)-J(r)` is continuous in `r`.

For any dense parameterization `ι : D → [a,b]`, `D(a,ι(d)) = 0` for all `d` implies `D(a,r)=0` for all `r∈[a,b]` by the dense-range equalizer theorem. This is equivalent to compact divergence-free scalar weak FTC by the previous committed Hilbert Leray-fixedness and density bridge. An additional theorem permits testing only compact solenoidal pairings of the defect at those dense endpoints (rather than the Hilbert defect itself). No joint spacetime continuity and no pointwise temporal derivative domination is assumed.

**Unresolved:** establish dense-time defect zero directly from the physical PDE. Physical L² source continuity alone cannot identify the primitive with the physical velocity path. The new result is an analytic simplification, not unconditional continuation or Navier–Stokes regularity.
