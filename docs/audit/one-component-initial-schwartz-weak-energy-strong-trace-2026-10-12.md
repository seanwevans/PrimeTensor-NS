# Physical Schwartz weak initial data + kinetic energy ⇒ strong L² trace

Parent checkpoint: `50254588` — strong initial physical trace from kinetic ceiling and self pairing.

## New bridge

The previous self-pairing condition against the full Hilbert initial
vector is no longer independently required. Instead, use the ordinary
right-time distributional weak initial trace against each real vector
Schwartz test. The exact Schwartz-to-physical-L² density theorem,
`denseRange_h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert`, is already
in the repository.

For any fixed approximate probe ψ, the exact kinetic ceiling implies

    ‖F(t)-U₀‖² ≤
      2 (|⟪F(t),ψ⟫-⟪U₀,ψ⟫| + 2‖U₀‖‖U₀-ψ‖).

Choose a sufficiently close Schwartz probe depending only on epsilon;
its scalar weak pairing difference vanishes on the right filter, and
the energy bound controls the approximation error uniformly in time.
Thus F(t) → U₀ strongly in physical L².

The physical theorem combines this generic result with the exact
positive-time kinetic ceiling derived from the separately supplied
initial-anchored L¹ kinetic budget. It then obtains the same kinetic
energy right continuity as the previous self-pairing route WITHOUT
subcritical H³ energy rate or temporal-derivative joint continuity.

## Declarations

- `h3Audit_initialHilbert_approxProbeSquaredDefect_le`
- `h3Audit_initialHilbert_strong_of_denseWeak_energyCeiling`
- `H3AuditInitialSchwartzRightWeakTrace`
- `h3Audit_initialBudget_SchwartzWeak_implies_physicalAndKineticRightTrace`

## Remaining independent obligations

Both the initial-anchored L¹ kinetic budget and right-filter weak
Schwartz initial trace must be justified from the actual initial-value
formulation. Neither is entailed by the open-time H³ path alone.
The proof does not imply global smoothness or close any terminal
actual-vorticity H³ obstruction.

## Source index

Run `python3 proof/generate_index.py`, `--check`, and the prose
fragment validator AFTER registering the module, BEFORE invoking any
`lake build` or audit baseline. Commit the resulting `proof/order.txt`.
