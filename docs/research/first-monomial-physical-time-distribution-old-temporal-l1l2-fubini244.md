# Physical momentum distributions from raw old temporal L¹_t L²_x

Base: `d477ada3` — derive physical momentum distributions from space-time Fubini.

## Result

For an actual preterminal classical solution, let `F_i(r,x)` be the old velocity temporal derivative's measurable continuation, at absolute time `t+r`. On every shortened time window `(0,q)`, require that each spatial slice `F_i(r, ·)` is in `L²_x` and

    r ↦ (∫ |F_i(r,x)|² dx)^(1/2)

is `L¹(0,q)`.

For every compact smooth solenoidal test vector `φ`, sharp spatial Hölder bounds its compact-tested spatial norm mass by

    ∫ |φ_i F_i(r)| dx ≤ ‖φ_i‖₂ ‖F_i(r)‖₂.

The left-hand scalar mass is known measurable in time from the existing joint-measurable temporal derivative extension. Therefore it is time-integrable. The prior mass-reduction theorem supplies the **actual old product-integrability predicate**, allowing existing weak-Fubini/weak-FTC/strong-derivative/time-distribution results to apply on a straddling physical restart.

## What's genuinely new

This avoids every spatially dominating envelope and spatial Lipschitz or equicontinuity bound. The spatial norm can have moving concentrations as long as its temporal L¹ mass is finite. There is no need to control the time-uniform spatial pointwise supremum.

## Outstanding mathematical obligation

The derived implication requires **the full old temporal derivative**, not merely the known continuous projected Leray source, to possess integrable spatial L² norm. The pressure-gradient component cannot be silently discarded. Whether the existing H³ path and old pressure structure directly imply this premise remains a separate PDE regularity question; the new module does not assert unconditional Navier–Stokes closure.

## Validation

No proof holes, no extra axioms, and no changed pre-existing theorem statements. The pinned repository's Lean compiler must check the source. Run `proof/generate_index.py` on every push.
