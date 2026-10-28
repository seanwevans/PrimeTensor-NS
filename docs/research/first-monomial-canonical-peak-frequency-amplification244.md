# Same-witness frequency amplification at canonical source maxima

Base: `aa0ee25e`.

The previous fixed-radius coercivity theorem proves for any FIXED radius ρ ≥ 0,
  (ρ² / 2) ‖U₃(sₖ)‖² ≤ D₃(sₖ)
eventually along a weighted spectral H³ peak sequence with diverging norm.
For an arbitrary target M choose a fixed radius ρ ≥ max(1,2M+2).
Consequently M ‖U₃(sₖ)‖² ≤ D₃(sₖ) eventually and
  D₃(sₖ) / ‖U₃(sₖ)‖² → +∞.
No subsequence selection is needed for this amplification conclusion.
The denominator is strictly positive eventually because ‖U₃(sₖ)‖→∞.

The actual physical kinetic anchor also bounds physical low-radial H³
dissipation by ρ² K(ρ) E₀(b). Together with divergence of full
dissipation and the exact low/high dissipation partition, this proves
for every fixed ρ≥0 and R≥0,
  R D_low(ρ,sₖ) ≤ D_high(ρ,sₖ)
eventually on the SAME original peak sequence.

The final canonical theorem retains the no-strong-physical-L² trace,
positive terminal kinetic mass, integrable terminal H³ dissipation,
and explicit canonical critical-width regime. Its selected source maximizers
are unchanged: D₃(sₖ)/‖U₃(sₖ)‖² tends to infinity.
This is an *unbounded coefficient* beyond quadratic, not a proved fixed
power-law lower bound D≥c ‖U‖^p for any p>2.
It is a pointwise concentration statement, not a time-integrated contradiction.

Status: source-level/static validation only; Lean compilation required locally.
