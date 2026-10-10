# One-sided weak-plus-norm bridge for actual physical H³ Fourier trace

Parent: `ac7a1808` — derive initial Picard ball from physical H3 energy.

## New mathematical implication

The repository's interior-time `continuous_of_weakRealPairings_of_norm` uses
`norm_sub_sq` to upgrade weak Hilbert continuity and norm continuity to strong
continuity. The new lemma
`h3Audit_tendstoRight_of_weakRealPairings_and_norm` proves its **one-sided
initial-time convergence** counterpart, using a genuine `𝓝[>] 0` filter.

For an actual encoded scalar velocity component `F(t)` and a proposed H³
initial state `G₀`, the separate obligations are:

- For every weighted complex-L² test state `Φ`, the real part of
  `⟪F(t), Φ⟫` converges to `Re ⟪G₀, Φ⟫` as `t ↓ 0`.
- The genuine scalar weighted-Fourier norm `‖F(t)‖` converges to `‖G₀‖`.

The exact identity
`‖F(t)-G₀‖² = ‖F(t)‖² - 2 Re⟪F(t),G₀⟫ + ‖G₀‖²`
forces `F(t) → G₀` strongly in H³. This is strictly a reduction of the
required initial trace into weak and norm limits; neither limit is proved
from a mere open-time preterminal H³ path.

The existing full-time `L²_t Ḣ^(3/2)_x` results are then available for the
actual physical component(s), conditional on the explicit strong terminal
endpoint. No initial mild equation or Picard-overlap hypothesis is required
for this alternative criterion.

## Still open

Produce the weak test-state initial limits and the top-order H³ norm limits
from the initial-value PDE with rigorous initial data. Connect those to the
published one-component continuation theorem without assuming the conclusion.
