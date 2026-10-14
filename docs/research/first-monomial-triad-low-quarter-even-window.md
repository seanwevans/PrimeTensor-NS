# First-monomial triad: an even sign-preserving window

Checkpoint: `e858bd45` (*prove exact scalar-window scaling of six-order signed triad kernel*).

## Setup

Let `U` denote the fixed quarter-scale, real-compatible, divergence-free Fourier Schwartz field. For each `ρ > 0`, let `χ₀, χ₁, χ₂` be the smooth compactly supported bumps of radius `ρ` at the three original frequency centers. Set

    Bρ(ξ) = χ₀(ξ) + χ₁(ξ) + χ₂(ξ)
    Wρ(ξ) = Bρ(ξ) + Bρ(-ξ)
    Vρ(ξ) = Wρ(ξ) U(ξ).

The new module proves `Wρ ≥ 0`, `Wρ(-ξ) = Wρ(ξ)`, smoothness and compact support of `Wρ`, and that both `Wρ` and `Vρ` are representable by genuine Schwartz maps. By scalar multiplication, `Vρ` remains Fourier-solenoidal, and even real weights preserve Hermitian reality.

## Coherent-support classification

Nonzero `Wρ(ξ)` implies that `ξ` lies within distance `< ρ` of one of the six original or reflected centers. If `ρ ≤ min(1,|1/4|)/4`, and `Wρ(p)`, `Wρ(-p-r)`, `Wρ(r)` are nonzero, the previously proved nonresonance theorem implies that `(p,r)` lies in the `ρ`-thickening of the **exact twelve-pair coherent orbit**.

Take the common positive-tube radius `δ > 0` from the fixed field `U`, and let `ρ = min(δ, 1/16)/2`. Then every nonzero weighted interaction is in `cthickening δ` of the coherent orbit. The exact trilinear scaling identity proves that its signed coefficient is strictly positive there:

    F_V(p,r) = Wρ(p) Wρ(-p-r) Wρ(r) F_U(p,r) > 0.

The primary resonant point `(P,R)` lies in the positive support, since each bump is 1 at its own center. Hence the modified kernel is nontrivial, not identically zero.

## Boundary of this milestone

This file does not yet prove integrability or positivity of the **unlocalized whole-space integral** of the weighted kernel. Those require the continuous compact-support/integrability passage on the product frequency carrier and the positive-measure support argument. No unconditional Navier--Stokes smoothness claim follows from these Fourier symbol calculations.

## Planned audit

Run `lake env lean` on the new module, build it, run `tools/audit/FirstMonomialTriad.lean` with `#print axioms` of each exported declaration, and then run `lake build`. Verify no `sorry`/`admit`, no unexpected assumptions, and the exact final theorem statement.
