#!/usr/bin/env python3
"""Idempotently register exact two-profile 2-2-infinity Schwartz gradient modulus."""
from pathlib import Path
import re

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientPairModulus244"
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'schwartzTripleIntegral_pair_abs_le_L2L2Linf244',
    'fullGradientTriple_pair_abs_le_L2L2Linf244',
    'thirdFullSchwartz_matchedFirstJet_abs_le_H3_244',
    'thirdFullSchwartz_matchedFirstJet_pair_abs_le_H3_244',
    'fullGradientTriple_spectralMatchedPair_modulus244',
    'thirdFullSchwartz_physicalPairFirstJet_abs_le_sumErrors244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Proof placeholder in Lean source')
    defined = set(re.findall(r'^theorem\s+([A-Za-z][A-Za-z0-9_]*)', source, re.M))
    missing = set(NAMES) - defined
    if missing:
        raise SystemExit(f'Missing declarations: {sorted(missing)}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in NAMES:
        full = 'PrimeTensor.FirstMonomialTriad.' + name
        for line in (f'#check {full}', f'#print axioms {full}'):
            if line not in rest:
                rest.append(line)
    new = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if new != old:
        AUDIT.write_text(new)
    print(f'Registered {len(NAMES)} two-profile gradient modulus theorems')

if __name__ == '__main__':
    main()
