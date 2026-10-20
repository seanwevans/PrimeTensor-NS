# One matched Schwartz family for H³ spectral, first-jet and 243-slot transport

Checkpoint: `402a4395`.

The earlier `exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy_matched244` builds real Schwartz velocity approximants whose 27 and 81 genuine derivative L² families agree with the same convergent spectral sequence. The original proof obtains a zero-order L² decoder identity, but the published theorem omitted it. The small idempotent patch `strengthen_first_monomial_matched_energy_decoder244.py` retains that identity in a stronger theorem and restores the old theorem as a compatible projection.

The new `FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzMatchedSobolevJets244.lean` uses that equality to recover pointwise zero-order realization (by uniqueness of continuous representatives), then obtains spectral-H³-to-first-L∞ control. The same E₂/E₃ Cauchy proof already invokes the actual real 27-slot Gagliardo–Nirenberg quartic bound to yield the mixed 81-L² + 27-L⁴ Cauchy graph. It follows that all 243 physical signed 3+2+2 transport slots are Cauchy in genuine jet norms.

Finally the **same** approximants form a `WeightedH3MatchedSchwartzCompletion244` for the target U and hence the signed monomial converges to `weightedH3CanonicalSignedFirstMonomial244 U`, independent of any competing matched family.

This is a compact functional-analytic synchronization step. It does **not** identify the nonlinear completion with the actual physical commutator of an arbitrary preterminal solution. Nor does it upgrade the physical fourth-order dissipation without more than H³ control.
