#!/usr/bin/env python3
"""Register conditional projected-source ceiling escape on exact PDE clocks."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDESourceCeilingEscape244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_sixthPDERate_boundedGain_forces_sourceEscape244',
    'h3Path_intermittentPDEGainCap_forces_sourceEscape244',
    'h3Path_intermittentBoundedSource_forces_cutoffGainGrowth244',
    'h3Path_noL2Trace_finiteDissipation_intermitSourceEscape_of_gainBound244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    contents = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', contents, re.M):
        raise SystemExit('Unexpected unproven placeholder or axiom')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', contents, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    oldroot = ROOT.read_text()
    lines = oldroot.splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    oldaudit = AUDIT.read_text()
    audit_lines = oldaudit.splitlines()
    imports = list(dict.fromkeys([ln for ln in audit_lines if ln.startswith('import ')] + [imp]))
    rest = [ln for ln in audit_lines if not ln.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in THEOREMS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != oldaudit:
        AUDIT.write_text(updated)
    print(f'Registered {len(THEOREMS)} source-ceiling escape theorems.')

if __name__ == '__main__':
    main()
