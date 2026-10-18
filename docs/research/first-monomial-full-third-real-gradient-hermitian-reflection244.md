# Full-third real gradient Hermitian reflection — checkpoint 8f4e627b

## Mathematical advance

Starting from the actual real divergence-free Schwartz velocity (not a sharp-frequency formal model), prove the exact Fourier reflection law U(-ξ)=conj U(ξ). Under simultaneous pair reflection (p,r)->(-p,-r), q=-p-r also negates. Seven real directional frequency factors therefore contribute a sign (-1)^7=-1 and the recovered complex Fourier amplitudes contribute conjugation. Each literal 3+3+1 Fourier kernel obeys K(-p,-r)=-conj K(p,r).

Since the project's Fourier normalization has (2πi)^7= -i(2π)^7, the real signed phase-correct kernel is even under frequency reflection. This pairs the sign behavior of the positive and negative orientation sectors exactly for the physical gradient slots, without asserting their integrals have already been evaluated or the entire physical coefficient has one sign.

## Remaining frontier

Prove the corresponding reflection parity for the genuine 3+2+2 interpolation kernel. Then aggregate all four gradient patterns and five physical indices into one real signed density; identify its twelve coherent-sector contributions and obtain a uniform strict sign (or discover genuine cancellation). The negative local symbol -192 is not by itself a global noncancellation result. No Navier–Stokes regularity assertion follows.

## Verification

Requires Lean/mathlib on the project machine; static archive checks do not substitute for compiling with `lake env lean` and `lake build`.
