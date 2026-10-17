# Real Schwartz roots for exact 243-slot Hölder

Base commit: `5bfdae23` (global E₂/E₃ fourth-power energy closure).

The predecessor theorem accepted four independent premises: a real Hölder
inequality for every slot and three identities equating arbitrary root arrays
to the actual square/fourth-power integral sums.

This patch defines the **actual** arrays, with five-index order `i,k,l,r,j`:

- `a(i,k,l,r,j) = √(∫ (D_i D_k D_l f_j)^2)`;
- `b(i,k,l,r,j) = √√(∫ (D_k D_l f_r)^4)`;
- `c(i,k,l,r,j) = √√(∫ (D_i D_r f_j)^4)`.

It proves nonnegativity, the root-power identities, and all three full
243-slot mass equalities by exact finite reindexing (no slot dropped).

It then takes the **existing, proved** ENNReal spatial 2–4–4 Hölder bound,
uses explicitly stated `realLpEnorm` norm-to-root identities, and obtains
the signed real Hölder bound for each slot. Feeding these actual arrays to
the preceding global energy lemma gives

    M(f)^4 ≤ 16 * card(Axis Depth.three)^9 * S^6 * E₂(f) * E₃(f)^5.

The only remaining prerequisites to make this estimate unconditional are the
Schwartz `L²` and `L⁴` *norm equalities*:

    realLpEnorm volume 2 g = ofReal (√(∫ g²))
    realLpEnorm volume 4 g = ofReal (√√(∫ g⁴)).

Those need genuine `MemLp` and `eLpNorm_eq_integral_rpow_norm`
normalization, and they are **not proved or assumed globally in this patch**.
Thus the new conclusion is explicitly conditional on them. In particular,
no regularity/continuation theorem follows from this estimate alone.

Compile the individual Lean source, build its module to produce the `.olean`,
then compile the audit and run the full build before committing.
