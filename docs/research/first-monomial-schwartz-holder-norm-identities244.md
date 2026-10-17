# Real Schwartz L2/L4 root identities for the 243 physical slots

Parent commit: `517b9404` — identify actual Schwartz Holder 244 roots.

This module provides the exact real-norm bridge postponed by the actual-roots module. `SchwartzMap.memLp` proves integrability for the actual physical Euclidean carrier, and the existing `realLpEnorm` representation in terms of mathlib `eLpNorm` is combined with the formula `MemLp.eLpNorm_eq_integral_rpow_norm`.

For Schwartz `g`, the resulting identities are

- `realLpEnorm volume 2 g = ofReal(sqrt(∫ g²))`;
- `realLpEnorm volume 4 g = ofReal(sqrt(sqrt(∫ g⁴)))`.

They apply directly to the third, middle, and cross derivative jets defined in the earlier 243-slot theorem. Therefore the previous three norm-identification hypotheses are all eliminated. The resulting **unconditional-on-extra-norm-premises** bound for real Schwartz fields is

    M(f)^4 <= 16 * card(Axis Depth.three)^9 * S^6 * E2(f) * E3(f)^5.

No divergence-free or Navier–Stokes assumptions are needed for this algebraic/analytic estimate. This inequality alone is neither a critical-half endpoint bound nor an unconditional global smoothness result. It is a standard high-order energy estimate with a supercritical energy exponent that must be treated accordingly in any continuation argument.

Validation: compile the new module with `lake env lean`, build its `.olean` with `lake build MODULE` before checking the audit file, then run `lake env lean tools/audit/FirstMonomialTriad.lean` and the full `lake build`.

## Repair at checkpoint 517b9404

The first local compilation reported two definitional-normalization mismatches.
The generic raw-to-extended norm bridge now takes an explicit `0 ≤ p`
argument to rewrite `(ENNReal.ofReal p).toReal = p`; both applications supply
this for exponents two and four.  The nested square-root proof now uses the
reverse direction of `Real.rpow_mul` to combine the exponents into one
quarter-power. No mathematical hypotheses or output statements were changed.
