# Source-driven high-H³ dissipation: extended integrated costs

Base: `6b376b9f` (source-driven common/disjoint source/H³ windows without full-dissipation continuity).

The parent theorem selects one coordinate and a cofinal, strictly separated family
of physical intervals with arbitrary independently prescribed moving source and
dissipation frequency radii and thresholds. On each selected closed interval,
the actual high-radial H³ dissipation is strictly above its prescribed real
height `M(v(k))`. The parent supplied an **ordinary real integral** cost only
under a separate local `IntervalIntegrable` hypothesis.

Here the nonnegative **extended** integral removes that premise entirely:

```
∫⁻_{(t(vk), t(vk)+δ(vk)]} ENNReal.ofReal (M(vk)) ds
  ≤ ∫⁻_{(t(vk), t(vk)+δ(vk)]}
         ENNReal.ofReal (actualHighDiss_{σ(vk)}(s)) ds.
```

The constant on the left equals `ENNReal.ofReal (δ(vk)) *
ENNReal.ofReal (M(vk))` for positive widths, and the resulting inequalities
sum across finite ranges on the **same separated windows**. In particular, a
negative prescribed height gives a zero lower cost, correctly, whereas
positive heights give positive extended costs.

The generic pointwise-to-extended-cost theorem requires neither measurability
nor interval integrability of the real-valued density. The actual-source
and high-H³ pointwise assertions remain under the original `hNoTrace`
branch and the kinetic-anchored physical energy class.

**Limitations.** This does not prove ordinary real-valued time integrals
are defined, that the high-H³ time-density is measurable, that costs are
finite, that the selected widths have a quantitative lower bound, or that
their sum diverges. For a *global upper bound on sums of extended integrals*,
measurability of the time-density must be verified separately; disjointness
alone is insufficient to infer it. No Navier–Stokes regularity conclusion is
claimed.

Declarations:
- `h3Critical_extendedWindowCost_of_pointwiseFloor`
- `h3Critical_noL2Trace_sourceDriven_disjointExtendedDissipationCosts`

The Lean file needs compilation under the pinned repository toolchain.
