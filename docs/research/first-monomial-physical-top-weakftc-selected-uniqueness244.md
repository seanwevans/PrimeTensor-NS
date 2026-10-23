# Old projected-RHS weak FTC to physical eighth moments (868ad99a)

## Mathematical result

The previously formalized selected-physical bridge assumed pointwise equality of
selected and old Navier–Stokes velocity on an interior selected restart slab.
This patch invokes the existing derivative-free weak–strong Grönwall theorem
`h3PreterminalSelectedPhysicalAgreementAt_of_allProjectedRHSWeakFTC`, proving
that equality **from the old projected-RHS weak FTC on [0,s]**.

For one physical time `t = t₀+s`, the required data are a positive anchor
`t₀`, an admissible canonical H³ tail at `t₀`, a positive slab
`s ∈ [Q/2,Q]` with `0<Q<R(E)` and `t₀+Q<T`, and the scalar projected-RHS weak
FTC on `[0,s]`. The already proved overlap transport gives exact spectral
identity with the selected positive mild state, hence integrability of all
order-eight raw velocity Fourier moments.

Consequently, under this scalar weak-FTC slab condition at all strict times,
physical fourth-radial dissipation escape implies one of:

1. Physical first-order dissipation grows without bound on the chosen tail.
2. Physical order-eight raw velocity moments are cofinally unbounded on every
   later subtail.

The patch also packages two stronger sufficient hypotheses from existing
restart theory: global projected-RHS weak-FTC frontier, or global old-pressure
weak-energy frontier, *together with geometric positive restart-slab coverage*.
Neither global frontier nor geometrical coverage is asserted automatically.

## Audit/limitations

- No `sorry`/`admit`, no new axioms, no new `.sh` files.
- Lean has **not** been compiled locally; run the repository's `lake env lean`
  and full `lake build` checks before committing.
- The theorem is a conditional necessary escape alternative, **not** a
  contradiction or a Navier–Stokes global regularity claim.
- Next mathematical task: prove actual positive-time geometrical slab coverage
  from local H³ energy continuity and canonical tail construction, and derive
  the relevant projected-RHS weak FTC from the physical pressure-free PDE data.
