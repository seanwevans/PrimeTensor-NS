# Uniform high-radial tightness of the physical solenoidal H³ recovery

Baseline: `18415218ad1a20b1c17810c340ad493f5e6cee01`.

## Mathematical target

The disjoint three-minimum partition controls the unrestricted complex H³
transport by sixth and first Fourier moments. To legitimately use limiting
physical Fourier states, one must distinguish a bound at each recovery index
from control of the far ultraviolet tail *uniformly along the recovery*.

For an exact weighted spectral state G, define the high-radial projection
`P_R G = 1_{|D(ξ)| ≥ R} G(ξ)` in the canonical L² quotient. The already-proved
natural radial exhaustion gives `||P_R G||₂→0` for each fixed G. Here we prove
that P_R is a contraction and additive, so for any strongly convergent
sequence `V_n→U`,

    ||P_R V_n|| ≤ ||V_n-U|| + ||P_R U||.

Thus for every ε>0, there exist R,N such that `||P_R V_n||<ε` for all `n≥N`.
The vector norm is the project's actual finite-coordinate sup norm.
No global Schwartz seminorm assumption or new realization sequence enters.

## Link to the actual sixth Fourier moment

The existing unnormalized cubic comparison `|ξ|³≤W₃(ξ)` yields for a Schwartz
field with genuine weighted representative `G_j=W₃ · 𝓕v_j`:

    ∫_{high(R)} |ξ|⁶ |𝓕v_j(ξ)|² dξ ≤ ||P_R G_j||₂².

Summing over the three axes yields the analogous bound for the genuine
Euclidean vector Fourier amplitude. This localizes the earlier global
sixth-moment estimate to the *identical radial tail*.

## Physical bridge and limitation

The existing physical NS snapshot recovery was already shown to converge
strongly in weighted H³, to be solenoidal at each Schwartz index, to carry a
snapshot-uniform complex H³ flux bound, and to recover the exact signed
transport. The new existential theorem retains **that same witness**, adding
the eventual uniform high-radial tightness conclusion.

The radius and the eventual index depend on the fixed physical snapshot.
This **does not yet** show trilinear high-tail flux is small, since the
frequency partitions and the scalar high-radial cutoff need an additional
localization argument. It **does not** furnish uniformity in physical time
as t approaches T, endpoint regularity, a favorable flux sign, or absorption.

Next: localize the L²-L²-L¹ sector bound to tails of its TWO large input
frequencies and combine with the uniform sixth-moment tail estimates.

## Lean elaboration repair (fix 2)

Explicitly change the norm-composition `Tendsto` expression to its lambda form; specify both real integrands and the restricted measure to `integral_mono_ae`. These are proof-only corrections; theorem statements and bounds are unchanged.

## Lean elaboration fix 3

The vector cutoff limit retains `‖(0 : H3SpectralVelocityState)‖` as the target of `continuous_norm.tendsto` until `norm_zero` is applied. The restricted integral comparison applies `integral_mono_ae` to the fully specified restricted-measure goal before supplying integrability and a.e. order facts, preventing inference of an unknown Fourier operand. No theorem statements or constants change.
