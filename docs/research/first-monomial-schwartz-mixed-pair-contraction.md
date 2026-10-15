# Exact physical Schwartz mixed-derivative pair contraction

Base checkpoint: `b5e4bb17` (unconditional physical Schwartz cubic interpolation).

For real Schwartz scalar `F` and real Euclidean directions `u,v`, the new
module proves the equality of mixed derivatives by applying second Fréchet
symmetry to `SchwartzMap.smooth`. It then applies the existing signed
integration-by-parts theorem twice to obtain

    ∫ (D_u D_u F)(D_v D_v F) = ∫ (D_u D_v F)².

Specializing `u,v` to `h3FourierAxisDirection i/k` gives the pairwise identity
for all actual ordered physical velocity/axis slots.

This is stronger than a slotwise Cauchy estimate. The next theorem should sum
over `i,k` and velocity components, establish the full Hessian/Laplacian
contraction, and deduce sharp coefficient-one adjacent energy bounds.

No PDE trajectory hypothesis or Fourier normalization enters the proof.
No global critical-half coefficient is claimed.
