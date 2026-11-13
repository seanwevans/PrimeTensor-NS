# Physical selected outer carriers: integrated sixth-power compression

Base: `6f875c84e1b14bae3d4502a62dca7d9df4f3d984`.

## Physical mathematics

The committed actual-Navier–Stokes sharp Fourier highpass theorem established

`119 * margin * sigma^6 <= 80 * velocityH3DissipationAt u t`

at a strict physical time for a selected annulus with `rho>0`, `sigma>=2*rho`, **strict positive kinetic-excess margin**, and a **nonnegative exact Young-width annular deficit**. The inequality does not itself imply a lower bound on integrated dissipation over a nonzero interval.

The new Lean source retains a *quantitative* half-margin after small perturbations in physical time using `thirdFullPhysical_actualSharpHighMass_continuousAt244`. It also retains positive exact annular deficit via `thirdFullPhysical_actualAnnularKineticDeficit_continuousAt244`, whose continuity is established using the actual nonlinear Young-width Fourier representation. No assumption of a uniform time-modulus is made.

On every interval `[x,x+delta]` where the full positive excess and nonnegative deficit persist, the original physical viscosity satisfies

`delta * (119 * margin * sigma^6 / 80) <= integral_x^T D_H3`.

For a single positive-deficit snapshot (`2*epsilon <= Deficit(x)`), the proof **constructs** a window with half the snapshot margin, so

`delta * (119 * margin * sigma^6 / 160) <= integral_x^T D_H3`.

For a cofinal increasing family `x_k -> T` of such snapshots, shorten the constructed windows to be disjoint. Finite full-H³ dissipation then gives **both** the individual terminal-tail inequalities and

`delta_k * (119 * margin_k * sigma_k^6 / 160) -> 0`.

If margins have a fixed positive floor and sigma grows, these constructed windows necessarily compress faster than the reciprocal sixth-power scale. This does **not** supply a positive lower bound for delta; no total-dissipation contradiction or Navier–Stokes continuation follows without an independent PDE time-width lower bound.

## Lean statements

- `thirdFullPhysical_selectedOuterMargin_rightWindow244`
- `thirdFullPhysical_selectedOuterMargin_integratedWindow244`
- `thirdFullPhysical_selectedOuterMargin_snapshotIntegratedSpike244`
- `thirdFullPhysical_cofinalSelectedOuterMargins_integratedCompression244`

Proofs contain neither `sorry` nor introduced axioms. Compilation must be checked in the project's pinned Lean/mathlib environment.
