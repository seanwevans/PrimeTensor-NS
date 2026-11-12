# Cutoff-uniform cubic-weighted nonlinear Young modulus (HEAD f11a2b56f)

## Exact research target

The previous `AnnularYoungWidthTemporalContinuity` module closed temporal continuity of the **full actual** nonlinear Young-gap plus finite-annulus width cost for each fixed pair of radii. It consequently removed the assumed `hYoung` parameter from the strict single-snapshot physical viscous clock. Its proof, however, supplied no common modulus when the radii vary with time or along a cofinal sequence.

This module quantifies the actual nonlinear term **uniformly across every annulus inside a fixed frequency ball**. It works with the already verified quotient `H3FourierComplexL2` construction and real squared norms, never by evaluating a Fourier `L²` class at one prescribed point.

For `0 ≤ rho ≤ sigma ≤ R` define the genuine operator

`A_{rho,sigma} F = M_sigma (P_sigma F - P_rho F)`

where `P` is the sharp Fourier `L²` projection, `M_sigma` is the bounded `sqrt(q³)` operator, and `q` is the physical Fourier gradient square. The triangle inequality plus the existing operator bounds give

`‖A_{rho,sigma} F‖ ≤ 2 R³ ‖F‖`

and, exactly because the operator is linear,

`‖A_{rho,sigma} F - A_{rho,sigma} G‖ ≤ 2 R³ ‖F-G‖`.

For the actual nonlinear residual `G_j(U) = Leray_j(U,U) - 2 LaplacianRaw_j(U)`, the existing algebraic difference estimate gives

`‖A G_j(U) - A G_j(V)‖ ≤ 2 R³ [576π C_3(‖U‖+‖V‖)+2] ‖U-V‖`.

The squared nonlinear Young mass obeys the **uniform** bound

`|‖A G_j(U)‖² - ‖A G_j(V)‖²|`
` ≤ 4 R⁶ [‖G_j(U)‖+‖G_j(V)‖] [576π C_3(‖U‖+‖V‖)+2] ‖U-V‖`.

This is valid for every radii pair simultaneously as long as both radii lie in the *same* bounded spectral ball, independent of the lower radius. By the preceding exact integral identity it bounds the true cubic-weighted annular Young-gap integral, not a model surrogate. Substitution of the actual preterminal H³ spectral states makes it a two-physical-time inequality.

## What it does not yet establish

The whole original Young-width cost also has a separate annular velocity-width term, with a radius-dependent polynomial coefficient. A common modulus for that term and its assembly with the nonlinear term remain to be formalized. Moreover, even a radius-uniform modulus for each **fixed** spectral bound `R` would not prevent degeneration as `R → ∞` or along non-uniform terminal H³ states. No terminal-time H³ continuation theorem is claimed.

## Build / audit

Build the new module; register in `PrimeTensor.lean` and `tools/audit/FirstMonomialTriad.lean`, run `proof/generate_index.py --check` and `proof/check_fragment.py --all`. No new axiom, sorry, admit, or change in existing hypotheses.
