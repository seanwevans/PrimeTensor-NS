# Full third-order gradient Schwartz Fourier identity

Base: `256b8795` ("close corrected full third Hermitian Fourier phase identity").

## Analytic contribution

This module uses the existing project Fourier triple-product theorem and the
coordinate-direction Fourier derivative theorem to prove the missing
3+3+1 counterpart of the existing 3+2+2 interpolation formula.

For arbitrary complex Schwartz components F,G,H and seven real directions,

    ∫ (D_a D_b D_c F)(D_d D_e D_k G)(D_v H)
       = (2πi)^7 ∫∫ K_{3,3,1}(p,-p-r,r) dp dr.

The frequency-side kernel is shown absolutely integrable by applying the
existing Schwartz multiplier and triple integral estimates. There are no
new assumptions of convergence or any unproved Fourier transform laws.

The four *actual* gradient-block index patterns are then represented by four
frequency integrals, each keeping the physical energy pairing factor two,
and summed over all five axis slots. This supplies the complex Schwartz
Fourier identity for the full twelve-term gradient commutator family.

## What this does not claim

* The theorem is for **complex Schwartz data**; transporting its real part to
  the project's `fullSchwartzGradientTransport244` real functional is another
  necessary bridge.
* It does **not** identify the total integrand with the previously proved
  six-permutation real polynomial `thirdFullPhysicalSixSymbol244` or integrate
  the finite Hermitian orbit. That step requires exact carrier/index matching.
* It does not construct a Hermitian divergence-free packet whose integrated
  coefficient is nonzero, prove a static full-transport counterexample, or
  prove Navier–Stokes regularity.

The source is a Lean candidate: compilation is performed by the user's
project `lake env lean` and full audit workflow.
