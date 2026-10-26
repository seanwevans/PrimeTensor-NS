# Physical cubic PDE source and cutoff-gain split

Base commit: `c344f144`.

## Mathematical content

For each actual finite annulus, the existing physical projected-PDE
coefficient has the **exact** factorization

`Λ(R,Q,K,C)+Ξ(R,Q,C)+1 = C L(R,Q,K) + C² H(R,Q)+1`,

where the gains `L` and `H` are explicit nonnegative expressions in the
weighted radial Sobolev ceilings and the starting spectral-state ceiling K.

If K,C,S are nonnegative and the coefficient exceeds `B R^6`, then either
`C>S` or `S L(R,Q,K)+S² H(R,Q)+1 ≥ B R^6`. Hence large source ceilings
or large weighted cutoff/spectral gains are the only mechanisms inside
this *particular proved PDE budget*.

On the physical no-terminal-L²-trace, finite-terminal-H³-dissipation
branch, the existing intermittent theorem also gives, at every sufficiently
late noncompressed witness, the **linear-or-quadratic rate alternative**:

`B R_k^6 ≤ 2 Λ_k+1  OR  B R_k^6 ≤ 2 Ξ_k+1`.

This does **not** rule out terminal geometric compression, bound the
outer Fourier cutoff, or bound the source ceiling. It remains an
obstruction theorem, not a Navier–Stokes regularity theorem.

## Validation

The patch is prepared with a source file and an idempotent audit registration
script. Lean compilation and the full project build must be run in the
user's repository before committing.
