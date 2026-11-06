# Four-channel prescribed-gauge obstruction from actual terminal viscosity

Base commit: `04fb5d89472dbab7521c8d6bfea8c007abe4e76f`.

## Hard PDE transfer

The established triple alternative localized source action at time
`t_k=τ(v(k))` and its half-terminal midpoint `m_k=(t_k+T)/2`. The later
source term was the actual absolute action `J_k=∫_{m_k}^T ||G(r)||_L2 dr`.

The repository already proves an affine **pointwise physical Navier–Stokes
projected source** estimate on every strict terminal interval `(b,T)`:

    ||G(r)||_L2 <= (3+C_L) * (1+6 E_0(b)+3 D_H3(r)).

`E_0(b)` is the real physical kinetic-energy anchor, `C_L` is the existing
nonnegative Leray coefficient, and `D_H3` is the full actual fourth-spatial-
derivative H³ dissipation. Integrating on the late strict interval yields

    J_k <= (3+C_L) * [ (T-m_k)(1+6 E_0(b))
                            + 3 ∫_{m_k}^T D_H3(r) dr ].

The comparison is performed on the open interval, avoiding any unjustified
pointwise source bound at the terminal endpoint T.

## Same-witness quartet

Let `H : ℕ -> ℝ` be prescribed, `H(n)>=1`, and let the existing no-strong-H³
trace theorem choose the same genuine *minimal* first-crossing annuli,
disjoint physical persistence windows, and a single terminal physical L²
Bochner primitive U. With `Q_k=N(v(k))+2` and the true real-linear physical
Fourier map F, the new theorem gives at least one of:

    H(vk)^4 < 14 Q_k^4 ||P^+_{vk} F U||,
    H(vk)^4 < 28 Q_k^4 ||F|| (m_k-t_k) E_k,
    H(vk)^4 < 56 Q_k^4 ||F|| (3+C_L) (T-m_k) (1+6 E_0(b)),
    H(vk)^4 < 168 Q_k^4 ||F|| (3+C_L) ∫_{m_k}^T D_H3(r) dr.

Here `E_k` is the genuine attained maximum of the physical projected source
norm on `[t_k,m_k]`. The original finite total disjoint viscous charge
bound and prescribed-gauge outer-frequency escape are retained.

A separate scalar interval-primitive theorem establishes

    ∫_{m_k}^T D_H3(r) dr -> 0.

The kinetic-time term also tends to zero since `m_k -> T`; nevertheless,
its product and the viscous tail's product by `Q_k^4` are **not shown to
vanish**. In particular, this is a necessary obstruction under the existing
finite-dissipation assumptions, not a contradiction or proof of regularity.
The theorem does not add assumptions or replace the physical source with
an unrelated abstract vector.

## Verification

Four new Lean theorems are registered with `#check` and `#print axioms`.
The package contains no proofs by `sorry`, `admit`, or added axioms. Run the
repository-pinned Lean/Lake toolchain and complete audits before committing:
this artifact-building environment has no Lean/Lake installation.

## Proof fix (same base HEAD)

The scalar terminal primitive continuity proof explicitly produces a
`Tendsto P (𝓝[Set.Icc a T] T) (𝓝 (P T))` witness from `ContinuousOn`,
then converts `a ≤ m(k) ≤ T` to eventual `Icc` membership before
forming `Tendsto m atTop (𝓝[Set.Icc a T] T)`. Composing these Tendsto
results removes the type error caused by using `ContinuousWithinAt.comp`
with a sequential `Tendsto` argument. No theorem statements changed.
