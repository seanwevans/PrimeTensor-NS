# Terminal H³ spectral nontrace: arbitrary viscous heights and cubic disjoint charges

**Baseline:** `da64b3273fc182fb61105a476fbc16342c40502f`.

## Genuine H³-frequency escape implies arbitrary prescribed viscous heights

At HEAD the absence of a strong terminal weighted H³ Fourier trace implies a
single threshold epsilon > 0 such that for **any** Fourier radius R and late
time window there is a genuine physical time t with high-pass sup norm >=
epsilon. The exact physical viscous coercivity proves

    (R+1)^2 ||P_R U(t)||^2 <= D_high(R+1,t) <= D_full(t).

Given an arbitrary real height profile M(n), first choose an integer R(n)>=n
large enough that (R(n)+1)^2 epsilon^2 > M(n). THEN choose a terminal time
within 1/(n+1) of T with ||P_R(n) U(t)|| >= epsilon. The antitonicity
of physical high-radial dissipation transfers the high dissipation height
from R(n)+1 to the natural n+1 cutoff. This gives one sequence t(n)->T
with D_high(n+1,t(n)) > M(n) and D_full(t(n)) > M(n).

The threshold epsilon is fixed before M; radii/times may depend on M.
The theorem does NOT assert an interval-integral divergence from tall points.

## Cubic finite annuli

Specializing M(n)=(n+1)^3 feeds the existing actual finite-annulus
persistence theorem `h3Path_cubicHighSnapshot_has_integratedFiniteAnnulusWindow244`.
At each cofinal time t(n), choose N(n)>=n and delta(n)>0 so that

    t(n)+delta(n) < T,
    (n+1)^3/2 < D_low(N(n)+1,s)-D_low(n+1,s)

for every s in [t(n),t(n)+delta(n)]. The same floor holds for the high-radial
physical dissipation. The interval integral of the **finite-annulus**
dissipation is >= delta(n) (n+1)^3/2, with exact frequency normalization.

This strengthens the prior physically nonconvergent kinetic L² branch: it
requires only absence of the strong weighted H³ endpoint trace. It does not
assume positive terminal kinetic mass.

## Disjoint charges and sharp remaining width obstruction

The existing geometric selection lemma extracts strictly increasing indices
v(k) so that the original physical windows are disjoint and t(v(k))->T.
Under the explicitly additional premise that the FULL physical H³
dissipation is Bochner L¹ up to T, the preexisting disjoint nonnegative
height-cost lemma yields

    sum_{k<m} delta(v(k)) * (v(k)+1)^3/2
       <= integral_a^T D_full(s) ds.

Hence the disjoint cubic charge series is summable and

    delta(v(k)) * (v(k)+1)^3/2 -> 0.

This is a width-compression NECESSITY, not a contradiction. A new PDE
lower-bound on the lifetime of peaks, preventing o((v(k)+1)^-3) widths on
an infinite disjoint subsequence, would be needed to rule out this mode
of terminal H³ escape. Tall finite-annulus peaks can have arbitrarily small
uncontrolled persistence widths.

## Audit and dependency discipline

The patch introduces three files in
`H3/Critical/Transport/` and exactly six theorem declarations with twelve
`#check`/`#print axioms` lines. It reuses already-built terminal escape,
frequency-square viscous coercivity, natural radial monotonicity,
finite-annulus persistence, and disjoint viscous cost lemmas. No `sorry`,
`admit`, new axioms, or postulated derivative/endpoint compactness hypothesis.

**Local validation:** static registration/integrity only; Lean compilation
requires the user's pinned Lean/mathlib toolchain.
