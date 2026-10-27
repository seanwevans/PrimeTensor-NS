# Critical ninth/eighth *annular width* separation on physical first-crossing shells

Base: `27da7784` — force superlinear minimal annular width from critical shell and PDE barrier.

Let `R_k = v(k)+1`, `L_k = N(v(k))-v(k)`, and `m(k)` be the established width-averaged energetic Fourier shell. The project already has a same-witness physical PDE alternative forcing, under eventually noncompressed quadratic-sharp clocks, a sixth-order bound for the linear rate, and a fixed ceiling for the projected physical source,

`∀ M ≥ 0, eventually M * R_k^9 < (R_k + L_k + 1)^8`.

The previous `CriticalShellWidthEscape244` theorem yields `L_k/R_k → +∞` on that branch. In particular, eventually `R_k ≤ L_k`. On such indices, the elementary estimate

`(R_k + L_k + 1)^8 ≤ (2 (L_k + 1))^8 = 256 (L_k + 1)^8`

transfers the ninth/eighth gain to the actual *width*, not just the outer cutoff:

`∀ M ≥ 0, eventually M * R_k^9 < (L_k + 1)^8`.

Equivalently, `(L_k+1)^8/R_k^9 → +∞`. The exponent is not weakened to merely `L_k/R_k → +∞`, and no fractional-power normalization is necessary in the Lean statement.

Four Lean theorems formalize (1) the factor-256 pointwise comparison, (2) eventual transfer on a sequence, (3) exact critical width quotient divergence, and (4) transfer to the *same* cofinal, disjoint, summable physical quadratic-sharp PDE witnesses with the selected positive-kinetic shell retained. The existing alternative under critical width-weighted kinetic depletion is also retained.

**Limitations.** Finite terminal full H³ dissipation, failure of terminal strong L² trace, positive terminal kinetic energy, eventual PDE clock noncompression, the linear rate bound, and the physical source ceiling all remain explicit. No control of the shell location relative to the outer cutoff, no upper bound for width, and no global regularity contradiction are claimed.
