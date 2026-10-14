# Vector-valued Schwartz completion of the sharp low-normal Fourier packets

Checkpoint: `57e20f3f`, smooth compact frequency cutoffs on the six sharp centers.

This module composes the existing smooth cutoffs with the normalized polynomial transverse germs and their reflected-conjugated partners. Its main object is

`lowNormalSmoothSixPacketSchwartz t ht : 𝓢(Fin 3 → ℝ, Fin 3 → ℂ)`.

The proof is split into elementary analytic facts:

- Each real Fourier coordinate embeds smoothly in complex space, yielding smooth squared-radius and mixed-dot polynomials.
- Fixed-center normalization preserves smoothness; multiplication by a smooth scalar cutoff preserves smoothness and inherits compact support from that cutoff.
- Finite sums, conjugation, and reflection preserve smoothness and compact support.
- The Schwartz map is constructed from the complete vector field, using `HasCompactSupport.toSchwartzMap`, without an unproved rapid-decay claim.
- Existing packet algebra supplies exact incompressibility and Hermitian reflection for the resulting Schwartz map.

This solves only the **functional-class construction**. It does **not** establish a nonzero integrated nonlinear triad functional. The latter must be handled by localizing the signed six-order coefficient, controlling all coherent cross-packet contributions, and proving an integral with a definite sign or nonzero imaginary component. Neither a smooth solution of Navier–Stokes nor a singularity assertion follows from these statements alone.
