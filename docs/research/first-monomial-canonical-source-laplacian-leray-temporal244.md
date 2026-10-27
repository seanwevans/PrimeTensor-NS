# Canonical physical source escape: anchor, diffusion jump, or Leray jump

Base: `43a5fc0a` ("isolate canonical projected source anchor escape or temporal jump").

## Exact physical decomposition

The source is **defined** (on the actual strict-time path) as the difference of
its inverse-Fourier physical Laplacian and Leray components:

\[
\mathcal P(t) = \mathcal D(t)-\mathcal L(t).
\]

For a selected cofinal disjoint annular clock anchored at
`t_k = τ(v(k))`, and its **preselected** canonical source maximizer
`s_k ∈ [t_k,(t_k+T)/2]`, norm triangle gives:

\[
\|\mathcal P(s_k)\|_{L^2} \leq
\|\mathcal P(t_k)\|_{L^2}+
\|\mathcal D(s_k)-\mathcal D(t_k)\|_{L^2}+
\|\mathcal L(s_k)-\mathcal L(t_k)\|_{L^2}.
\]

The previous canonical critical-width theorem forces the left side to tend
to infinity **conditionally** on the eventual noncompression, sixth-order
linear-rate bound, and bounded ninth/eighth annular width, together with
its underlying no-strong-terminal-L²-trace and finite-full-H³-dissipation
hypotheses. The present module derives:

1. For each fixed threshold M, every sufficiently late index has anchor
   source ≥ M, diffusion increment ≥ M, or Leray increment ≥ M.
   The disjunction may change with the index.
2. If the anchor source and diffusion increments are each eventually
   bounded, then the Leray increment tends to +∞ on that same sequence.
3. If the anchor source and Leray increments are each eventually bounded,
   then the diffusion increment tends to +∞ on that same sequence.

No inequality is assumed between the maximizing-time lag `s_k-t_k` and the
short persistence width `δ(v(k))` beyond what is already known, and the
maximizing times are **not** asserted to lie in the disjoint dissipation
windows. The theorem does **not** imply a uniform temporal modulus of the
source or a contradiction with finite H³ dissipation. A further genuinely
quantitative bridge would bound component increments by a spectral state
increment or its time-integrated derivative in the required terminal
frequency regime.

## Registered Lean declarations

- `h3Path_physicalSourcePeak_le_anchor_diffusionJump_lerayJump244`
- `h3Path_physicalSourceTemporalJump_le_componentJumps244`
- `h3Path_sourcePeaks_force_anchor_diffusionOrLerayTemporal244`
- `h3Path_boundedDiffusionJump_forces_lerayJumpEscape244`
- `h3Path_boundedLerayJump_forces_diffusionJumpEscape244`
- `h3Path_noL2Trace_canonicalWidth_diffusionLerayTemporalAlternative244`

Source proof is designed for `lake env lean` against commit `43a5fc0a`.
Lean elaboration cannot be executed in the packaging environment and must
be verified locally before committing.
