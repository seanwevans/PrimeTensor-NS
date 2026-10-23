# Physical eighth moments from compact momentum-term control

**Baseline:** `2ec2cfee` (`reduce physical eighth moments to local compact-test temporal domination`).

The selected/old uniqueness route needs local temporal domination of each compact weak-test pairing. That condition is a parametric-integral hypothesis on the actual physical temporal derivative; it does **not** follow from separate continuity of `∂ₜu(t,x)` in time and space.

This increment replaces that derivative-level assumption with a PDE-side compact estimate. On each compact spatial test support and a sufficiently small elapsed-time neighborhood, assume a common finite upper bound `C` for the norms of the physical Laplacian, advection, and pressure gradient coordinates. The exact preterminal momentum equation gives

\[
 \partial_t u_j(t,x)=\Delta u_j(t,x)-(u\cdot\nabla)u_j(t,x)-\partial_j p(t,x),
\qquad |\partial_tu_j(t,x)|\le 3C.
\]

Consequently `3C |φ_j(x)|` is an integrable majorant because `φ_j` is continuous with compact support. The previously formalized parametric-integral theorem gives projected-RHS weak evolution and scalar weak FTC; Grönwall then gives selected/old uniqueness and the physical raw eighth Fourier moment for each positive-time slice.

The new `h3PreterminalMomentumTermsCompactBoundOnElapsed244` is a **real, explicit hypothesis** about local uniformity in time on compact sets. It is not proved from H³ admissibility or a pointwise spatial `C⁵` slice alone. In particular, no global boundedness or joint spacetime continuity has been smuggled into the theorem.

### Next substantive analytic proof

Identify a source of local spacetime bounds for the three momentum terms from the actual positive-time PDE / parabolic smoothing. Alternatively, replace pointwise compact control by uniform-in-time `L²` or `L^{6}` bounds and prove an appropriate weak differentiation-under-integral theorem. The latter could follow from local H³ energy ceilings together with pressure estimates, without requiring time-uniform bounds of second spatial derivatives in `L∞`.
