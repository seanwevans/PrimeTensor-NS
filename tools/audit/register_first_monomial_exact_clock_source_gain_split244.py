#!/usr/bin/env python3
"""Register the exact cubic physical source / cutoff-gain split."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDESourceGainSplit244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_finiteAnnulusPDERate_sourcePolynomial244',
    'h3Path_finiteAnnulusPDEGains_nonneg244',
    'h3Path_sixthRate_forces_sourceOrCutoffAmplification244',
    'h3Path_sixthSumRate_forces_componentBarrier244',
    'h3Path_noL2Trace_finiteDissipation_intermittentPDEComponents244',
)
DEFINITIONS = (
    'h3PathFiniteAnnulusPDELinearGain244',
    'h3PathFiniteAnnulusPDEQuadraticGain244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Unexpected unproven placeholder or axiom')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    for name in DEFINITIONS:
        if not re.search(r'^\s*noncomputable def\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing definition: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([ln for ln in lines if ln.startswith('import ')] + [imp]))
    rest = [ln for ln in lines if not ln.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in DEFINITIONS + THEOREMS:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + q, '#print axioms ' + q):
            if command not in rest:
                rest.append(command)
    new = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if new != old:
        AUDIT.write_text(new)
    print(f'Registered {len(THEOREMS)} theorems and {len(DEFINITIONS)} gains.')

if __name__ == '__main__':
    main()
