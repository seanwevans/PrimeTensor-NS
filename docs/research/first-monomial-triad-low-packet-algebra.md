# Reality-symmetric low-normal Fourier packet algebra

Checkpoint: `5bc4b04a`, polynomial solenoidal germs at the six sharp
low-normal centers.

For each positive center η in {p,q,r}, with transverse complex amplitude a,
let G_{η,a}(ξ) = χ_η(ξ) P_ξ(a)/|η|², where χ_η is an arbitrary real scalar
cutoff and P_ξ(a) = |ξ|² a - ξ(ξ·a). The cutoff does not compromise
pointwise solenoidality, because ξ·G_{η,a}(ξ)=0 identically.

Set G = G_{p,A} + G_{q,B} + G_{r,C}, then form

    U(ξ) = G(ξ) + conjugate(G(-ξ)).

The algebraic proof establishes both

    ξ·U(ξ)=0,       U(-ξ)=conjugate(U(ξ))

for all frequencies, without any Fourier-coordinate Jacobians, singular
multipliers or assumptions on the cutoff profiles. If each positive cutoff
is one at its own center and zero at the other positive centers, the
positive half reproduces A,B,C. To recover those values for full U, the
reflected packets must also vanish at the corresponding positive centers.

The pointwise vanishing lemma shows U is supported wherever at least one
cutoff is nonzero at ξ or at -ξ. The previously established six-center
separation theorem can later be applied to localized cutoff supports.

This patch does NOT construct smooth compactly-supported χ_η, identify the
`Fin 3 → ℝ` carrier with `H3FourierPoint3`, package U as a SchwartzMap, or
show integrated noncancellation of its six-order triad coefficient. Those
are separate analytic and Fourier-bridge obligations.

The source is intended for the project's pinned Lean toolchain; Lean
compilation cannot be checked in this patch-authoring environment.
