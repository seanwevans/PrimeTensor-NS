# Canonical top-order higher-radial universal escape under persistent charge

Base: `420437fb` — bridge canonical H3 high-tail concentration to physical top higher radial moments.

The source-level point is that the established exact canonical disjoint windows
already have cofinal anchors `t_k = τ(v k) -> T`, positive widths `δ_k`, and
`t_k + δ_k < t_(k+1) < T`. Therefore `δ_k -> 0`, without an extra width cap.

If the explicitly conditional anchor-height charge has an eventual positive
floor `η <= δ_k D3(t_k)`, then `D3(t_k) -> +∞`, and the terminal-time
lower-rate obstruction `η <= (T-t_k) D3(t_k)` eventually follows from
`δ_k <= T-t_k` and nonnegativity of actual physical H3 dissipation.

The already proved full-to-top physical bridge gives, for every natural m,

    ofReal((Q_k²)^m * (D3(t_k)/8)) <= M^(top)_(4+m)(t_k)

eventually, by choosing the real tail fraction β=1/2. Since `Q_k=N(v k)+1 >=1`,
its power `(Q_k²)^m >=1`. Thus all **fixed** extended higher-radial moments
`h3TerminalPhysicalExtendedHigherRadialMomentAt m` tend to `+∞` in ENNReal
on the original, **same** canonical sequence (including m=0).

The quantifiers are `∀ m : ℕ, Tendsto (moment m) atTop (nhds top)`, not
an unproved uniform-in-m statement. Higher moments may be infinite at individual
times, as the objects are ENNReal-valued.

This does **not** establish the positive charge premise. If the charge collapses,
none of the new divergence assertions follows from this theorem. In particular,
this is not a proof of smooth continuation or Navier–Stokes regularity.

Declarations:
- `h3Path_scalar_cofinalTerminalWindow_width_vanish244`
- `h3Path_scalar_shrinkingWindow_persistentCharge_heightEscape244`
- `h3Path_scalar_canonicalOuterPower_ge_one244`
- `h3Path_scalar_topHigherMoment_escape_of_heightEscape244`
- `h3Path_noL2Trace_exactAnchor_persistentCharge_universalTopHigherEscape244`


Compilation with the pinned Lean/Mathlib toolchain is unavailable in the packaging container;
the local Lake build and proof audits are required.

## Lean correction (fix1)

The constant-minus-cofinal-time limit is now expressed through an explicitly typed constant `Tendsto` hypothesis, avoiding an unresolved implicit domain in `tendsto_const_nhds.sub`. The `tendsto_nhds_top_mono'` comparison is pointwise; the previous eventually-only moment bound is handled by the pointwise minimum of the comparison sequence and the target, which agrees eventually with the comparison sequence. Neither correction changes a mathematical assumption or conclusion.
