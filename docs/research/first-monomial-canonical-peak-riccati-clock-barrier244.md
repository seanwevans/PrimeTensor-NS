# Canonical H³ transport spikes: inverse-root clock versus Landau ceiling

Base commit: `40fc5d82` — the committed Landau overshoot-versus-slow-clock dichotomy.

Set `A = ‖U₃(s)‖` (the product SUP norm), `B = ∫ₐᵀ D₃`, `H > 0` the optimized source-peak clock, `C₁` the physical spectral coordinate gradient coefficient, and `K = 4422(C₁+1)`. On the genuine noncompressed half-loss branch, the previously proved transport spike satisfies

    H A² < 8(B+1) Tr₃(q),        q ∈ [s,r],       q-s ≤ (B+1)/H.

The actual physical Landau estimate yields

    Tr₃(q) ≤ 4422(1+C₁ √E₃(q)) E₃(q).

Hence either `E₃(q) > 16 A²`, or

    H < 128(B+1)4422(1+4 C₁ A).

The high-energy branch now meets *another independently proved fact*: the autonomous Riccati estimate implies monotonicity of `E₃(t)^(-1/2) + (K/2)t`, so

    1/√E₃(s) - 1/√E₃(q) ≤ (K/2)(q-s).

The actual sum-of-three-squares energy satisfies `E₃(s) ≤ 1+3A² ≤ 4A²` for `A≥2`. Therefore `E₃(q)>16A²` implies the **fourfold overshoot** `E₃(q)>4E₃(s)`, which forces

    1 < K(q-s)√E₃(s) ≤ K(B+1)·2A/H.

Thus the high-energy branch requires

    H < 2K(B+1)A.

Combining both cases, **every noncompressed half-loss** must satisfy the explicit linear upper clock

    H < M(A,B) := max(128(B+1)4422(1+4C₁A), 2K(B+1)A).

The exact source-peak identity `A⁸ = 16384(E₀(b)+1)H³` implies the root-free, strict eighth-power necessary inequality

    A⁸ < 16384(E₀(b)+1) M(A,B)³.

This is a real improvement over merely detecting an energy overshoot: even an arbitrarily high overshoot cannot occur arbitrarily fast under the proved autonomous H³ growth bound. Since `M` grows linearly in `A` with fixed `B` and `b`, while the left-hand side is eighth order, the inequality excludes sufficiently large **noncompressed** peaks. The theorem in this package does not yet make a cofinal asymptotic extraction or remove the terminal compression alternative; those require a separate formal proof.

**Verification status:** registrar syntax and idempotence, ZIP integrity, source checks only. Lean elaboration/build unavailable in the packaging environment. The local user run script must call `proof/generate_index.py`, full Lake build, and the repository's baseline audit before committing.
