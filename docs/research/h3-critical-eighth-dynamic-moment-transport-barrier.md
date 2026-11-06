# Same-window critical-eighth moment barrier from physical momentum transport

Base commit `8f62fad1ec38f2dbc40dece5d381a520b55732c5`.

## Exact PDE comparison

The existing no-strong-H³-trace branch selects genuinely minimal first-crossing
annuli with inner radius `R_k = v(k)+1`, selected outer radius
`Q_k = N(v(k))+2`, and exact physical windows
`I_k = [τ(v(k)), τ(v(k))+δ(v(k))]`.

Let `M_η(n)=η(n+1)^8+(n+1)`, `η>0`. For **every** `s∈I_k`, the established
anchored-PDE persistence estimate supplies the positive annular dissipation
floor

    M_η(v(k))/4 < D_annulus(s).

The exact (fourth derivative) annular dissipation moment obeys

    D_annulus(s) ≤ 4 Q_k^8 μ_k(s),

where `μ_k(s)` is the actual **unweighted raw Fourier kinetic mass** of the
same selected annulus. The newly proved physical momentum FTC and absolute
source-L¹ transport give

    μ_k(s) ≤ 3 [A_k+‖F‖ I_k^src]^2,

where `A_k = ‖P^+_{v(k)} F(u(τ(v(k))))‖`, `F` is the actual bounded real-linear
physical Fourier map, and

    I_k^src = ∫_{τ(v(k))}^{τ(v(k))+δ(v(k))} ‖G(r)‖_L² dr

for the genuine projected physical momentum source `G`.
Combining those three *on the same physical time and annulus* yields

    η R_k^8 < 48 Q_k^8 [A_k+‖F‖ I_k^src]^2.

No pointwise source ceiling is substituted for the actual integral.

## Vanishing amplitude and interpretation

Finite full H³ dissipation yields a terminal physical L² trace and Bochner-L¹
projected momentum source. Existing moving highpass tightness gives `A_k→0`;
existing absolute source-tail control gives `I_k^src→0`.
Consequently the bracket tends to zero even though the annular fourth-jet
dissipation persists at the critical eighth height on the ENTIRE window.
The quantitative inequality forces the relative outer-to-inner frequency
amplifier to compensate for that vanishing bracket.

This is a necessary condition of the no-terminal-H³-trace branch, **not** a
contradiction: no estimate here bounds `Q_k/R_k` from above. The remaining
hard obligation is a source/viscosity mechanism that limits this amplifier,
or a coercive signed-H³ transport estimate that excludes it.

## Audit and verification

Three new theorems: a scalar real-frequency comparison; an actual on-window
Navier--Stokes Fourier/source estimate; and a same-witness terminal alternative
retaining raw uniform tightness, viscous-clock summability, and ratio escape.
No new axioms or proof placeholders. The source-only packaging environment has
no Lean/Lake installation. Compile with the repository-pinned toolchain and
run the full project audit before committing.
