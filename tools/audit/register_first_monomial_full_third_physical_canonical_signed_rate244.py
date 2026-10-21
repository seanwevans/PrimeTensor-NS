#!/usr/bin/env python3
"""Register canonical H3 signed PDE rate and terminal obstruction; idempotent."""
from pathlib import Path
import re

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalCanonicalSignedRate244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3PathWeightedSpectralState_eq_actual244',
    'h3Path_weightedFullThird_eq_physical244',
    'h3Path_deriv_add_dissipation_le_weightedFullThird244',
    'h3Path_weightedSignedTopRate_eq_physical244',
    'h3Path_normalizedSlope_le_weightedSignedTopRate244',
    'h3Path_weightedSignedTopRemainder_eq_physical244',
    'h3Path_weightedSignedTopRemainder_integrable_iff244',
    'h3Path_extension_of_integrable_weightedSignedTopRemainder244',
    'h3Path_weightedSignedTopRemainder_nonintegrable_on_subtail244',
    'h3Path_weightedFullThird_adverse_witness_of_noExtension244',
    'h3Path_extension_of_weightedFullThird_dominance244',
)
DEFS = (
    'h3PathWeightedSpectralState244',
    'h3PathWeightedSignedTopRate244',
    'h3PathWeightedSignedTopRemainder244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing: {path}')
    src = SOURCE.read_text()
    if re.search(r'\b(sorry|admit|axiom)\b', src):
        raise SystemExit('Lean placeholder or axiom detected')
    for typ, names in [('theorem', THEOREMS), ('noncomputable def', DEFS)]:
        for name in names:
            if not re.search(r'^' + typ + r'\s+' + re.escape(name) + r'\b', src, flags=re.M):
                raise SystemExit(f'Missing {typ}: {name}')
    imp = 'import ' + MODULE
    oldroot = ROOT.read_text()
    if imp not in oldroot.splitlines():
        ROOT.write_text(oldroot.rstrip() + '\n' + imp + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([ln for ln in lines if ln.startswith('import ')] + [imp]))
    rest = [ln for ln in lines if not ln.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in (*THEOREMS, *DEFS):
        full = 'PrimeTensor.FirstMonomialTriad.' + name
        for line in ('#check ' + full, '#print axioms ' + full):
            if line not in rest:
                rest.append(line)
    revised = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if revised != old:
        AUDIT.write_text(revised)
    print('Registered weighted H3 canonical signed PDE rate and continuation obstruction')


if __name__ == '__main__':
    main()
