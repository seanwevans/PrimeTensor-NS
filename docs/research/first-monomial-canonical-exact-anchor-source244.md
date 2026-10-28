# Exact canonical source/PDE spectral anchor coefficient

Parent: `2174f9c1` (`force canonical H3 source spectral amplification under critical width`).

## Missing type-level fact

The earlier physical minimal annular constructor selects its coefficient
`K = ‖h3AuditActualSpectralVelocityTotal hH3 t‖` at its original strict
preterminal anchor, but the exported existential statement only retained
`0 ≤ K`. Consequently the cofinal amplification statement involving
`K(v(k)) C(v(k))` cannot legitimately be replaced with a statement in
physical H³ energy by unfolding its *old* witness K. The previous
cofinal coefficient is not yet verified as an exact norm at the type level.

## New source theorem

`h3Path_cubicHighSnapshot_has_exactAnchorCanonicalClock244` replays the
physical first-crossing construction with the same minimal outer annulus,
attained source envelope `C`, and literal quadratic-sharp PDE width, but
puts `‖U₃(t)‖` directly into the linear variation coefficient. It preserves
the actual integrated physical annular persistence floor. This is a NEW
existential witness, not an assertion that any previously chosen K agrees.

The exact physical sum-of-three-squares spectral energy identity gives

    ‖U₃(t)‖² ≤ velocityH3EnergyAt(u,t).

Hence the genuine source–state product obeys

    (‖U₃(t)‖ C)² ≤ E₃(t) C².

Combined with the previously established explicit radial multiplier
bound `Λ ≤ 48 |K C| (Q+1)^5`, the new scalar bridge proves

    Λ(R,Q,K,C)² ≤ 2304 E C² (Q+1)^10

whenever `K² ≤ E` and the original nonnegative radius/coefficient conditions
hold. This is the genuine pointwise PDE bound with `E=E₃(t)` for the new
exact-anchor snapshot.

## Remaining hard step

Rebuild the canonical choice/disjoint-window extraction with this strengthened
snapshot constructor and propagate `K(v(k)) = ‖U₃(τ(v(k)))‖` all the way to
the cofinal amplification theorem. Without that transport, the earlier
cofinal `K` must remain an existential nonnegative coefficient.

No uniform terminal source/energy bound, elimination of the cofinal regime
branches, or unconditional Navier–Stokes continuation is claimed.

Validation: ZIP integrity, registrar syntax and idempotence only. Lean
compilation must run in the repository's pinned toolchain.
