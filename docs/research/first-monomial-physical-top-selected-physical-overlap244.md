# Physical-overlap realization of selected eighth velocity moments

Baseline: `37bb998f` — transfer selected positive-time eighth moments to physical velocity.

## Genuine old/physical snapshot identity

For the original preterminal velocity `u`, the intrinsic spectral state
`h3TerminalVelocitySpectralStateAt hH3 t ht` and the canonical old-tail state
`h3PreterminalTailCanonicalSpectralStateOnElapsed ... q` are both the same
`velocityH3SpectralStateAt u t` whenever `t = t₀ + q`. The Fourier-compatible
integrability and measurability witnesses are proposition-valued and do not
change the resulting weighted H³ spectral state. This equality is unconditional
on any old-tail elapsed snapshot for which the indicated prerequisites exist.

## Local selected/old physical overlap

Previous `H3/Selected/Spectral/State/Old/Bridge.lean` proves that pointwise
agreement between the original classical velocity and the selected positive-
time mild velocity upgrades to exact equality of their weighted H³ states,
provided the selected elapsed time lies strictly within its restart radius
and the old elapsed interval stays before `T`.

The new definition `h3PathVelocitySelectedPhysicalOverlapAt244` records exactly
this physical-space input at a point inside a positive slab `[Q/2,Q]`:

- a positive old anchor `t₀`, adequate energy ceiling `E`, and canonical tail;
- `0 < Q < restartRadius(1,E)` and `t₀+Q < T`;
- a time `s ∈ [Q/2,Q]` with `t=t₀+s`;
- the existing `H3PreterminalSelectedPhysicalAgreementAt` predicate.

The theorem `h3Path_selectedSlabRealized_of_physicalAgreement244` combines
(1) the intrinsic old/physical identity and (2) the selected/old spectral bridge
to derive the *exact* spectral realization required by the previous module.
The slab-radius subtype is identified by equality of its underlying time.

## Necessary terminal obstruction

Assume the previously stated unbounded top dissipation branch and that every
strict physical time has a local physical-overlap witness. Then the selected
positive-time eighth-moment theorem transfers to the genuine physical state;
the already-formalized endpoint obstruction says

    D₃ is unbounded on (s,T)
      => D₁ is unbounded on (s,T)
         or the eighth-order raw physical velocity moment
         escapes cofinally on every later terminal subtail.

Neither strict-time eighth-moment integrability nor existence of a Fourier
second-radial L² representative is postulated separately in the resulting
criterion. Both follow from earlier lemmas plus the explicit physical overlap.

## What is *not* proved

The pointwise selected/old physical agreement is **not** inferred from H³
admissibility here. Showing it via local Navier–Stokes uniqueness and proving
that the corresponding positive slabs cover every strict physical time is
still necessary. We do not equate H³ regularity with Schwartz decay, nor infer
terminal-uniform higher moments. The result remains a necessary escape
alternative, not a contradiction or unconditional continuation theorem.
