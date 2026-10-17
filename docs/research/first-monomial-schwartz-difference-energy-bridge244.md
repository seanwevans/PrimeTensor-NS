# Schwartz difference-jet energy bridge (7beed4ca)

## Actual analytic content

For the true physical Euclidean real Schwartz velocity difference `h_j = f_j - g_j`, the 81-term integrated third-jet **square** mass of `D³f - D³g` equals `E₃(h)` *exactly*. Likewise the 27-term integrated second-jet **fourth**-power mass equals the previously formalized `Q₄(h)`. The key input is linearity of the Schwartz directional derivative, using `LineDeriv.lineDerivOpCLM.map_sub`.

Consequently the proven Gagliardo–Nirenberg theorem gives

`Q₄(h)^2 ≤ S^6 · E₂(h) · (card(Axis 3) · E₃(h))^3`.

The identities are sensitive to indices and have no unexplained 243-slot multiplicity. They use the existing physical derivative axes and actual spatial integrals.

## Next mathematical obstruction

To eliminate the 81+27 norm Cauchy hypothesis, derive quantitative **root/sum** control from these integral energy bounds, then show ordinary Schwartz H³ Cauchy convergence implies mixed-graph Cauchy convergence. Constructing Schwartz approximants for a general physical Sobolev field and proving physical pairing identification remain separate obligations.

## Verification

No `sorry`, `admit`, or new axioms. ZIP/source syntax and registration verified; this patch has **not** been compiled under the target Lean/mathlib toolchain in the artifact environment. Run the module build, full project build and `tools/audit/baseline.sh --reuse-build` before committing.
