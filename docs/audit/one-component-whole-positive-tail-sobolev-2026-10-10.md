# Intrinsic physical homogeneous H3/2 on the entire positive time tail

Parent checkpoint: `d05f583f` — package intrinsic physical H3/2 Sobolev time L2 criterion.

The prior result gives an existential terminal subtail `(c,T)` on which the
intrinsic homogeneous 3/2 seminorm of each selected physical velocity
component lies in `L²_t`. The physical Fourier energy density is already
continuous at every strict preterminal time, in particular on `[a,c]`
whenever `0<a<c<T`. Hence it is interval integrable there. Mathlib's
`ContinuousOn.intervalIntegrable_of_Icc`, `IntervalIntegrable.trans`, and
`intervalIntegrable_iff_integrableOn_Ioo_of_le` glue the integrability on
`[a,c]` to integrability on `(c,T)`, obtaining the *whole* `(a,T)` interval.

New results:

- `h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_positiveTail`:
  generic positive-start local-to-terminal integrability transfer for one
  actual velocity Fourier density;
- `h3Audit_complementEndpoint_intrinsicThreeHalves_fullPositiveTail_timeL2`:
  selected component with strong spectral H3 endpoint yields its intrinsic
  physical homogeneous H3/2 norm in `L²((a,T))`;
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullPositiveTail_timeL2`:
  both transverse physical components satisfy the intrinsic criterion on
  the SAME `(a,T)` interval;
- `h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullPositiveTail_timeL2`:
  one component suffices for the *analytic time-norm* part.

Remaining: full `(0,T)` when required by a publication still needs an
independent near-initial-time bridge; no continuity or norm bound at t=0 is
claimed here. More importantly, applying Liu–Zhang's external PDE criterion
requires its local-strong-solution eligibility and extension translation.
These are not proved, not assumed as axioms, and not silently imported.
Neither unconditional Navier–Stokes extension nor Clay Form A follows.
