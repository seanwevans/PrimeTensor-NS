#!/usr/bin/env python3
"""Apply the 2026-10-15 critical-half/theorem-boundary documentation correction.

Expects the public 92a8cdcd document contents and preserves all Lean files.
Safe to run twice; a mismatched baseline aborts before touching that document.
"""
from pathlib import Path

AUDIT = Path('docs/audit/critical-half-roadmap-correction-2026-10-15.md')


def amend(path: str, old: str, new: str) -> None:
    p = Path(path)
    if not p.is_file():
        raise SystemExit(f'Missing source document: {p}')
    content = p.read_text(encoding='utf-8')
    if new in content:
        print('Already patched:', path)
        return
    if content.count(old) != 1:
        raise SystemExit(f'Expected a single baseline anchor in {path}, found {content.count(old)}')
    p.write_text(content.replace(old, new), encoding='utf-8')
    print('Patched:', path)


def append_section(path: str, marker: str, section: str) -> None:
    p = Path(path)
    if not p.is_file():
        raise SystemExit(f'Missing source document: {p}')
    content = p.read_text(encoding='utf-8')
    if marker in content:
        print('Already patched:', path)
        return
    if not content.endswith('\n'):
        content += '\n'
    p.write_text(content + '\n' + section.rstrip() + '\n', encoding='utf-8')
    print('Patched:', path)


def main() -> None:
    if not AUDIT.is_file():
        raise SystemExit(f'Unzip patch before running: {AUDIT}')

    amend('README.md',
        'The current development studies **necessary terminal behavior under hypothetical failure of smooth H³ continuation** and turns the negation of those behaviors into explicit continuation criteria.',
        'The development formalizes **conditional terminal behavior and continuation criteria** for H³ paths, alongside exact physical Schwartz energy identities. These results are not an a-priori estimate for every Navier–Stokes solution.')

    amend('README.md',
        'These are retained hypotheses in the endpoint compactness theorems below. The conclusions should therefore be read conditionally on this setting.',
        '''These are retained hypotheses in the endpoint spectral-tail theorems below. The conclusions should therefore be read conditionally on this setting.

**Known-criterion warning:** despite its name, `H3TerminalActualVorticityStrongH3EndpointPath` supplies strong weighted spectral H³ terminal endpoints for **two physical velocity components**. A published one-component criterion of [Liu–Zhang (2024)](https://doi.org/10.1137/23M1623124) gives continuation for a compatible local strong Navier–Stokes solution from one velocity component in `L²_t Ḣ^{3/2}_x`. Our intrinsic positive-start time-`L²` bridge is largely formalized, but compatibility with that external theorem and its continuation conclusion is **not** proved in Lean. Consequently the retained-hypothesis nonextension branch is likely redundant for compatible strong solutions, not an independently established new regularity scenario.''')

    amend('README.md',
        '''## Current frontier

The project has reduced the surviving terminal obstruction to frequency-space compactness of the top-order H³ dissipation.

The remaining problem is to obtain a continuation-producing compactness statement from the Navier–Stokes dynamics themselves—for example, terminal uniform radial-tail control or a uniform bound for one coercive weighted top-dissipation moment—without assuming the desired continuation conclusion.

The current endpoint theorems also retain the actual-vorticity strong H³ endpoint-path and raw velocity Fourier `L²` Cauchy hypotheses described above.

Earlier energy-growth, BKM, transport, Landau, moment-cascade, and balance-channel results remain part of the formal development, but they are now intermediate infrastructure rather than the cleanest statement of the present endpoint criterion.''',
        '''## Current frontier: known analytic estimates versus new PDE control

The spectral-tail and coercive-weight results are **conditional continuation criteria and logical consequences of their failure**, not a derivation of terminal compactness from Navier–Stokes dynamics. Uniform high-frequency tail control is not itself equivalent to whole-trajectory spatial precompactness on `ℝ³` (translations matter). Cofinal cutoff escape does not supply a physical-time growth rate.

The *complete signed 243-slot first monomial* `M` has derivative orders `(3,2,2)`. The **existence** of a universal critical-half inequality is already known mathematically from Hölder, homogeneous Sobolev embedding `Ḣ^{3/4}(ℝ³) ⊂ L⁴`, and interpolation:

```text
|M(u)| <= C_* ||u||_{Ḣ^{1/2}} ||u||_{Ḣ^4}^2
       <= C_*' sqrt(1 + E0(u)+E1(u)+E2(u)+E3(u)) D(u).
```

The sharp five-order coefficient-one Schwartz interpolation and shape-orbit identities are **proved in Lean**; the displayed universal `L⁴` / fractional-Sobolev bound is **not yet proved in Lean for the exact project definitions**. Consequently the normalized shape quotient is mathematically bounded, and conditional strict-excess witnesses can refute only coefficients below a suitable finite threshold.

Even when formalized, the critical-half inequality does **not** establish arbitrary-data global regularity: the coefficient `C_* ||u||_{Ḣ^{1/2}}` cannot generally be absorbed into viscosity without smallness or a genuinely stronger dynamical estimate. Any new closing argument must exploit structure of the **true** Navier–Stokes nonlinearity not supplied by generic Hölder/Sobolev estimates; see [Tao's averaged-model obstruction](https://arxiv.org/abs/1402.0290).

Next priorities: formalize the known critical-half inequality with actual Schwartz derivatives and constants; complete the one-component literature-eligibility bridge on a positive-start interval; and look for a genuinely new PDE-specific a-priori control. See the [October 15 theorem-boundary correction](docs/audit/critical-half-roadmap-correction-2026-10-15.md).''')

    amend('docs/research/first-monomial-critical-half-uniform-shape-criterion.md',
        'Thus the solenoidal version is an\nexact characterization of the remaining user-facing mathematical frontier.',
        'Thus the solenoidal version is an\nexact **logical criterion for a proposed coefficient**, not an unresolved mathematical question about whether any finite coefficient exists.')

    amend('docs/research/first-monomial-critical-half-uniform-shape-criterion.md',
        '''**Open:** It is not proved that one universal C exists, that X_C(f)>0 occurs
for arbitrarily large C, or that the Navier--Stokes PDE continues or blows up.
The next mathematical task is a genuine uniform *shape* estimate or a
counterexample across varying Schwartz profiles, not another fixed dilation
identity.''',
        '''**Correction (2026-10-15):** Existence of **some finite universal C** is a standard analytical consequence of Hölder, `Ḣ^{3/4}(ℝ³) → L⁴`, interpolation between `Ḣ^{1/2}` and `Ḣ⁴`, and the energy bound on `Ḣ^{1/2}`. The exact project-specific inequality is **not yet a Lean theorem**. A positive `X_C` witness can disprove an individual too-small C, but not every finite C. The unresolved hard-mathematics issue is stronger structure or dynamical control sufficient for unconditional Navier--Stokes continuation; simply formalizing the standard critical-half estimate does not close that gap. See `docs/audit/critical-half-roadmap-correction-2026-10-15.md`.''')

    amend('docs/research/first-monomial-schwartz-five-order-interpolation.md',
        '''The results require no solenoidality or PDE evolution. They do **not**
control the signed first-monomial term `M`, establish a universal
critical-half constant, or imply finite-time Navier–Stokes regularity.
The next nontrivial input is a bound on the actual nonlinear product,
likely through physical Sobolev/L4 estimates and the signed monomial's
cancellations, not another scale transformation.''',
        '''The results require no solenoidality or PDE evolution. They do **not by themselves** control the signed first-monomial term `M` or imply finite-time Navier–Stokes regularity. A finite universal critical-half constant **does exist mathematically**, by standard physical homogeneous Sobolev `L⁴` embedding and fractional interpolation; a proof for the project's exact Schwartz definitions, normalization, and aggregate is still a **Lean formalization target**. That bound alone is insufficient to absorb the nonlinear dissipation term at arbitrary critical norm. See `docs/audit/critical-half-roadmap-correction-2026-10-15.md`.''')

    amend('docs/research/first-monomial-schwartz-sharp-balanced-obstruction.md',
        '''These theorems do **not** claim that a strict-excess witness exists, or that
 a uniform coefficient exists.'''.replace('\n ', '\n'),
        '''These theorems do **not** assert a strict-excess witness or formally prove a finite uniform coefficient in Lean. Standard Sobolev analysis nevertheless guarantees **some finite universal coefficient exists mathematically**, so a strict-excess witness can only refute a particular too-small proposed coefficient.''')

    append_section('docs/research/first-monomial-schwartz-unit-shape-reduction.md',
        '## Mathematical-status correction (2026-10-15)',
        '''## Mathematical-status correction (2026-10-15)

The exact ratio equivalence remains valid and useful as a formalization. Its **mathematical boundedness is already known**, however: physical Hölder `L²·L⁴·L⁴`, Sobolev `Ḣ^{3/4}→L⁴`, and `Ḣ^{1/2}`–`Ḣ⁴` interpolation give `|M| ≤ C ||u||_{Ḣ^{1/2}}D`. On `E0=E3=1`, `E1≤1`, hence `||u||_{Ḣ^{1/2}}` is uniformly bounded and so is `R`. This particular boundedness theorem is not yet present in Lean. The genuine PDE challenge remains absorption or improved structural control at large critical norm. See `docs/audit/critical-half-roadmap-correction-2026-10-15.md`.''')

    append_section('docs/research/first-monomial-schwartz-shape-orbit-normalization.md',
        '## Mathematical-status correction (2026-10-15)',
        '''## Mathematical-status correction (2026-10-15)

The orbit reduction does not leave mathematical existence of a finite shape-ratio bound open: that existence follows from standard homogeneous Sobolev `L⁴` and critical-half interpolation estimates for Schwartz profiles. Their exact project-specific Lean realization remains pending. A strict-excess witness may refute a *proposed* constant but cannot produce unbounded ratio in this class. See `docs/audit/critical-half-roadmap-correction-2026-10-15.md`.''')

    print('Documentation correction complete. No Lean files changed.')


if __name__ == '__main__':
    main()
