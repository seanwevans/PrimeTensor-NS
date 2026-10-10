# PrimeTensor-NS: frontier-boundary audit (2026-10-10)

Base checkpoint: `d803cc86` (`master`). This note is intentionally a *theorem-boundary audit* and does not claim resolution of the unforced 3D Navier--Stokes problem. Companion source: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/FrontierBoundary.lean`.

## 1. Already closed, not remaining targets

The path-specific continuation bridge is proved in `Continuation/H3/Restart/Direct.lean`: `h3PathRealRestart_of_tailControl` constructs a physical velocity, pressure, later time `S>T`, preterminal agreement, PDE evolution and third-jet continuity. `h3PathH3ControlProducesExtension` converts uniform terminal H³ control into the project's `SmoothContinuationExtension` package. The H³ BKM criterion is separately closed in `Continuation/H3/BKM/Closure.lean`. `H3/Vorticity/Apriori/Frontier.lean` already defines `EveryH3PathPreterminalNavierStokesSolutionExtends` and names the outstanding a-priori vorticity input. `Continuation/Frontier.lean` already defines `EverySeededPreterminalNavierStokesSolutionExtends`.

The new Lean audit does **not** rename these old targets as new research. Instead it isolates the *unproved* universal terminal H³ estimate, the seeded-PDE-to-strong-H³-path eligibility bridge, and the one-component literature bridge. From the first it proves path continuation using the already closed restart. From the first two it proves seeded continuation. These are conditional implications, not proofs of their antecedents.

## 2. Endpoint theorem: serious possible redundancy

`H3TerminalActualVorticityStrongH3EndpointPath hH3 i` is an intersection of TWO `H3TerminalComplementGradientStrongH3EndpointPath` predicates for two *velocity* components transverse to the chosen physical curl component. Each predicate contains one spectral H³ terminal state and a pathwise norm-convergence modulus. The repository itself proves continuation from **two distinct** such physical vorticity predicates (`.../Physical/Two/Component/Strong/H3.lean`), but that does not resolve the stronger question whether just *one* predicate already invokes classical one-velocity-component regularity.

Liu--Zhang, *On the One Time-Varying Component Regularity Criteria for 3-D Navier-Stokes Equations*, SIAM J. Math. Anal. **56** (2024), 6213--6231, DOI 10.1137/23M1623124, prove a continuation criterion for a local strong solution given finite `L²_t dot H^(3/2)_x` of a selected (potentially time-varying) velocity component. Taking a constant coordinate direction is a special case. Pathwise strong H³ endpoint convergence should furnish a uniform H³ bound near finite T and hence the required one-component homogeneous `dot H^(3/2)` control, **once** the project spectral state/physical velocity and local-strong-solution classes are identified with those used by the theorem. The project does not presently prove those exact bridges. In particular, the existence of a pathwise endpoint state is *not itself* a Lean proof of the cited theorem's local-strong-solution applicability.

**Acceptance test:** prove the compatibility bridge and the one-component `L²_t dot H^(3/2)` estimate, then establish `H3AuditOnePhysicalEndpointLiteratureBridge` from a faithful formalization/import of the published theorem. If so, the noextension arm of `Terminal/Clock/Endpoint.lean` under `hPhysical` is impossible, and `hCauchy` is unnecessary for that conclusion. Until then, the bridge remains an explicitly *unproved* proposition.

## 3. Universal blowup obstruction and Tao's averaged model

Tao, *Finite time blowup for an averaged three-dimensional Navier--Stokes equation*, J. Amer. Math. Soc. **29** (2016), 601--674, arXiv:1402.0290, constructs finite-time blowup in an averaged equation conserving kinetic energy and retaining generic bilinear Fourier/harmonic-analysis bounds. Therefore, energy cancellation and such generic bounds **alone** cannot justify unconditional regularity. This does not rule out every future PrimeTensor-NS strategy: the true transport operator could admit decisive cancellations absent from the averaged operator.

**Acceptance test for a proposed closing estimate:** identify the exact true-NS signed identity, structural cancellation or geometric inequality on which it depends; explain why the averaged operator lacks it; derive a uniform terminal bound or integrable nonlinear-growth majorant instead of yet another necessary rate under hypothetical nonextension. Clock/width and dissipation concentration consequences can stay in the library but should not be conflated with that missing a-priori estimate.

## 4. Clay Form A is not the seeded continuation proposition

The official statement by C. Fefferman, *Existence and Smoothness of the Navier--Stokes Equation* (Clay Mathematics Institute), formulation (A), quantifies over **all** smooth rapidly decaying divergence-free initial velocities on `R³` with zero force, and asks for a global smooth velocity/pressure solution, correct initial trace and finite energy. The repository's preterminal-path types and `EverySeededPreterminalNavierStokesSolutionExtends` are not presently a formal representation of all those initial-data quantifiers and global-time existence requirements.

**Required bridges before a faithful `ClayFormA : Prop` reduction:** formalize the datum class and initial trace, local well-posedness from every datum, compatibility of the local classical solution with the existing logged/H³ interfaces, a maximal-time or continuation/iteration mechanism covering every finite horizon, global smoothness of the assembled velocity and pressure, and energy bounds. If viscosity normalization and rescaling are required, formalize them too. Do not define `ClayFormA` merely as an alias for seeded continuation or call a conditional implication a Clay proof.

## 5. Maintenance and immediate tests

`Continuation/Frontier.lean` currently says the universal seeded vorticity-to-H³-control proposition is not yet formalized. This is misleading without scope: the H³-**path** BKM criterion is closed, while the universal **seeded** proposition is distinct. The runner updates this comment with the distinction. The deeply nested historical modules remain reachable but should be given short conceptual entrypoints and stable compatibility imports. The foundational `.tex` index under `proof/` does not adequately document restart and BKM analysis. Add prose linked to exact theorem names before declaring new results independent.

`hCauchy` is a secondary frontier: weak L² convergence with nonincreasing energy does not, in general, imply strong L² Cauchy convergence at T without convergence of norms/no energy loss. Check the preterminal strong-solution energy equality, temporal weak continuity, and boundary flux/regularity assumptions before attempting to discharge it.

### Primary references

- Liu & Zhang (2024): https://doi.org/10.1137/23M1623124
- Tao (2016): https://arxiv.org/abs/1402.0290
- Fefferman/Clay problem statement: https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf
- Existing internal contract review: `docs/audit/contract-boundaries.md`
