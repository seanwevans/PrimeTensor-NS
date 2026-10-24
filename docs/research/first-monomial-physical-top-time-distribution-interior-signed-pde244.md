# Physical time distributions from interior signed PDE momentum domination

Base: `a3d94cfb` — derive physical momentum distributions from joint PDE regularity.

A local temporal majorant for each compact solenoidal test is sufficient to
justify physical weak temporal evolution, without assuming continuity of the
whole function `(t,x) ↦ ∂ₜu(t,x)` on a product neighborhood. Earlier restart
predicates used an observation time at the *right endpoint* of their interval,
which does not prove an ordinary **two-sided** time derivative there.

`h3PathInteriorTimeTemporalDominationAt244` requires a canonical H3 restart
window `(t₀,S)` and an elapsed interval `[0,τ]` whose **absolute** interval
`(t₀,t₀+τ)` contains the observation time strictly inside. The existing
parametric-integral lemma and projected-RHS weak-evolution-to-weak-FTC bridge
then prove that the old physical Hilbert path has strong derivative

    HasDerivAt U (ΔU - Leray(u·∇u)) s.

`h3PathInteriorTimeSignedMomentumBoundAt244` makes the analytic premise
PDE-facing: on compact spatial test supports, the *signed sum*

    Δu_j - (u·∇)u_j - ∂_j p

has a local time-neighborhood bound. It preserves nonlinear/pressure
cancellations instead of bounding each term separately.

With this premise at every interior time of `(a,b)` the established
strong-derivative ⇔ distributional-momentum characterization gives a genuine
compact-time distributional equation. A nonzero physical Hilbert FTC defect
forces this signed straddling-window bound to fail at some interior time.

**Scope:** The new theorems do **not** prove existence of such straddling
uniform signed bounds from H3 path admissibility. Separate continuity and
pointwise spatial compactness only provide bounds at fixed times, and are
not substituted for time-uniform domination.

Build using the registration script and `proof/generate_index.py`, then Lean
on the new module, audit and full `lake build`.
