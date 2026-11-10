# Certified physical annular escape at the twelfth-power source rate

**Base:** `b6b86ff4072de449913e9b78b73d7248222cd089`.

## The defect requiring repair

The downstream signed LowMax rate/gauge chain (including the degree-12
source gate) retained the `outer` arm only as

`∃ Q : ℕ, R ≤ Q ∧ G < Q`.

This is logically automatic for any pair `R,G` by choosing `Q=max R (G+1)`.
It does NOT certify any physical energy, actual Fourier mass, nontrivial
annular flux, source, or dissipation at that cutoff. The older proofs did
construct a positive annular dissipation peak and a genuine in-gap width, but
then projected them away from the result type. A frequency escape assertion
with no physical property tied to the selected frequency is vacuous.

## Corrected physical theorem

The module copies the already accepted symmetric in-gap kinetic persistence
proof and **retains the last conjunct**

```
H/2 < D_low(N+1, U(t)) - D_low(R+1, U(t))
```

for the *same* outer index `N` appearing in its persistence width and
integrated cost `w * H/4 ≤ D_gap`. The proof uses the original physical
annular construction, PDE Lipschitz transport, and actual H3 dissipation
monotonicity. The new gauge reduction keeps that same `N`; it does not pick
a free natural number.

The scalar Bernstein/source polynomial from the accepted base satisfies,
for `E0≥0`,

```
P_k(E0) ≤ K(E0) * (k+1)^12,
K(E0) = 1 + 192*sqrt(E0)*(sqrt(E0)+54*E0) > 0.
```

The exact four-factor Bernstein expansion and the canonical physical Fourier
cube volume are unchanged; there is no new external volume hypothesis.

For an actual gamma-free high-radial carrier at `t∈[x,y]`, with physical
energy at `t` capped by `E`, set

```
h = eta / (8*(A(E)+1)) > 0,
D = ∫_[x,y] velocityH3DissipationAt(u,r) dr,
H = actual signed LowMax linear viscous height.
```

One certified `N≥R` carries a genuine positive annular H3 dissipation peak,
a positive persistence width `w`, and the genuine in-gap cost. Moreover:

```
(y-x)*h ≤ 16*D
  OR
h^2 ≤ 32*K(E0)*(k+1)^12 * D
  OR
k < N.
```

When both physical payments are strictly below their thresholds, **the same
certified annulus** satisfies `k<N`, `H/2<annular dissipation at t`, and
`w*H/4≤D`. In contrast, the previous bare outer-number disjunct required no
physical property at `N`.

The cofinal theorem reconnects this to the original adverse physical signed
sixth-flux samples and the accepted removal of the Schwartz gamma parameter,
conditional on excluding the earlier tenth-power residual. It does not
assume that every gap carries an adverse sample, that the relative H3
dissipation vanishes, or that `(k+1)^12 D(k)→0`.

## Mathematical status

This repairs the logical loss of the physical annular witness. It proves a
necessary certified concentration/frequency alternative, **not** Navier--Stokes
continuation. The remaining possible branches are positive relative gap
dissipation, twelfth-power kinetic-rate payment, or genuine moving annular
dissipation with a positive peak and in-gap cost. Those alternatives need an
additional physical contradiction or rigidity theorem for continuation.

## Verification

Run the registrar in apply and check modes, generate the proof index, and run
both the targeted Lean file and project build. The generated ZIP has been
checked structurally; Lean elaboration must be verified in the target repo.
