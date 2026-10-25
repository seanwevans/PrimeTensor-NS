# Quantitative spectral finite-annulus dissipation modulus (2026-10-25)

Base commit `1cdd40f9`. The mathematical gain is explicit variation control for physical finite-annulus H³ dissipation from native weighted spectral-state increments, using existing bounded radial Fourier multipliers.

Let `B_{R,Q}(G)=D_{<Q}(G)-D_{<R}(G)`. If each of the three Fourier coordinates of `G` and `H` has L² norm at most `K`, and each coordinate increment has norm at most `ε`, then

`|B_{R,Q}(G)-B_{R,Q}(H)| ≤ 6*((Q+1)^2+(R+1)^2)*K*ε`.

For a physical path with increments bounded by `V*(s-t)` on `[t,t+δ]`, annular dissipation remains above height `A` whenever the initial height exceeds `A+6*((Q+1)^2+(R+1)^2)*K*V*δ`. This also yields `∫ B ≥ δ*A` from the already-established bounded-frequency continuity.

**Unresolved physical input:** estimate the actual weighted spectral increment rate `V` from the projected Navier–Stokes evolution, ideally with a uniform modulus along the cubic snapshots. Without such an estimate, no lower bound for the selected terminal window widths or blowup-exclusion claim is established.

The bounded multiplier estimates intentionally use the already-proved `ρ+1` operator bound, not an unproved sharp constant.
