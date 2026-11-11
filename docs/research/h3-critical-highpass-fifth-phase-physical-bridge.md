# Critical H3 highpass cubic forcing: exact Hilbert / physical phase bridge

Base HEAD: `414875e5c184e764140ce5ac56c56dc2ec7ef4ee`.

## Exact normalization and physical meaning

For `q(ξ)=(2π)^2 ||ξ||^2` the native third-radial Leray Hilbert state
is `|ξ|^3 N_j(ξ)`. The physical cubic density is `q^3 |N_j|^2`.
The exact sharp highpass identity (no inequality and no assumed moments) is

    (2π)^6 ||Hρ F3,j||_L2^2
      = ∫_{sqrt(q)>=ρ} q^3 |N_j|^2 dξ.

The proof first identifies the canonical strict-time Fourier a.e.
representative and then uses the repository's true sharp-cutoff Plancherel
identity. The factor `(2π)^6` is not interchangeable with 1.

## Derivative-free highband expenditure

The accepted scalar Young/phase identity gives at every frequency

    q^3 |N_j|^2 <= 2 q^5 |û_j|^2 + 2 Phase_j,

where `Phase_j = q^5|û_j|^2 + q^3|N_j|^2 +
2q^4 Re⟨û_j,N_j⟩` is nonnegative. Summing the exact physical highpass
norm identities gives, on every strict physical time slice,

    (2π)^6 Σ_j ||Hρ F3,j||²
      <= 2 FifthHigh(ρ,t) + 2 PhaseHigh(ρ,t).

Neither Fourth-Q source nor sixth-radial velocity state occurs here.

## Dyadic physical witness

Combining this estimate with the exact cubic log-balance, kinetic-only
lowband forcing bound, and actual dyadic net-growth witness yields ONE
strict physical time `r` selected before any radius, satisfying for all ρ>0,

    [K + Phi5(r) + PhiPhase(r)] D3(r)
      < 3(2π)^6 LowBudget(ρ,E0(b))
          + 2 FifthHigh(ρ,r) + 2 PhaseHigh(ρ,r).

The theorem returns a proof that `r` lies in the physical class interval;
this is a derived membership witness, not an extra regularity premise.

The result is a necessary spectral-payment condition, NOT closure:
the two highband expenditures have no established terminal-uniform bound,
and the lowband kinetic bound increases with the radius. A new PDE or
solenoidal cancellation estimate is required before continuation follows.

## Declarations

- `thirdFullPhysical_highpassThirdHilbert_eq_actualCubicBand244`
- `thirdFullPhysical_highpassThirdHilbertSum_eq_actualCubicBand244`
- `thirdFullPhysical_highpassThirdHilbert_le_twoHighFifthPhase244`
- `thirdFullPhysicalCriticalHighFifthBand244`
- `thirdFullPhysicalCriticalHighSignedPhaseBand244`
- `thirdFullPhysical_nearCriticalAnchor_forces_highFifthPhaseBand244`

No `sorry`, new axioms or opaque continuation hypotheses.
