# H3 old-pressure joint continuity and physical momentum — checkpoint cc74b7c6

The existing pressure compactness proof is local to a selected restart slab, but
`LoggedPreterminalH3PathAdmissible.exists_localCanonicalRestartWindowAt` covers
every `s ∈ (0,T)` by such a slab. Shorten the selected radius if necessary to
remain before the local terminal time `S`. The old preterminal pressure-gradient
is jointly continuous on this selected slab because:

- the committed curl weak-FTC branch already provides selected physical evolution;
- selected pressure force is jointly continuous within its existence radius;
- selected/old pressure forces agree on the physical overlap;
- any two classical pressure witnesses for one velocity have equal gradients.

The local `ContinuousOn` statements glue into joint continuity on all of
`(0,T) × ℝ³` by `continuousOn_of_forall_continuousAt`, without asserting temporal
continuity of the pressure scalar itself (its additive gauge remains free).
The pressure witness on any shorter interval inherits the same gradient
continuity by the pressure-gradient uniqueness lemma.

The repository's `Pressure.Joint` result then bounds the compact-tested old
pressure-gradient mass uniformly on each closed elapsed interval `[0,τ]`
strictly inside `(0,S)`. A constant profile is integrable on `(0,τ)`, proving
the old-pressure L1 predicate required by the prior Fubini reduction.

The local canonical window around each `s` supplies an earlier anchor `t₀`,
a terminal `S`, an H3 tail, and `t₀ < s < S`. Choosing
`τ = ((s - t₀) + (S - t₀))/2` makes `s ∈ (t₀,t₀+τ)` and `t₀+τ<S`.
Therefore the old-pressure L1 profile, old-product Fubini, physical Hilbert
strong derivative, time-test distributional momentum, and zero interior
projected-momentum FTC defect follow relative to H3-path admissibility.

**Scope:** This closes a consistency/differentiation gap on open strict time
intervals, not at the terminal endpoint. It uses previously committed
curl weak-FTC and physical selected/old agreement. It does not prove a new
independent continuation criterion or global Navier–Stokes regularity. The
particular Lean module is not compiler-verified in the artifact environment.
