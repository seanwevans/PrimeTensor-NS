# Local compact-test temporal domination and physical eighth moments

Baseline: `c6f7c0b9` (`derive eighth moments using local shortened restart windows`).

## Precise reduction

At a strict physical time, the already proved sliding canonical H³ restart window supplies `t₀ < t < S < T`, an energy ceiling `E`, and a radius larger than the elapsed width `q=t-t₀`. Instead of separately assuming the scalar projected-RHS weak fundamental theorem of calculus on `[0,q]`, the new condition demands for **each compact divergence-free test** and each elapsed time `s` a neighborhood on which the product `φ_i(x) ∂ₜu_i(t₀+r,x)` is bounded almost everywhere by some spatially integrable function. The bound may depend on the test, component and neighborhood; there is **no uniform terminal envelope**.

The established `Projected/RHS/Weak/Evolution/Local/Domination.lean` theorem differentiates the compact-test velocity pairing under this domination and integrates in elapsed time to obtain projected-RHS weak evolution. The existing `.../Reduction.lean` theorem supplies scalar projected-RHS time integrability and packages the weak FTC. The previous local-short-restart theorem applies selected/old weak–strong uniqueness, weighted H³ spectral equality and selected mild finite-moment regularity to transfer raw order-eight Fourier moments to the physical state.

## Necessary terminal obstruction

Under local domination at every strict physical time, unbounded physical top dissipation `D₃` requires unbounded lower physical dissipation `D₁` or cofinally unbounded raw eighth velocity moments. Without that assumption, there is a three-way necessary alternative including failure of local compact-test temporal domination at some strict time.

This is a **conditional** necessary alternative, not a contradiction and not a Navier–Stokes regularity proof. In particular, the project's old preterminal regularity package proves separate temporal and spatial continuity of the old temporal derivative, but separate continuity does not imply jointly continuous or locally uniformly dominated spacetime behavior. Closing domination from the original physical PDE data is the substantive unresolved analytic step.
