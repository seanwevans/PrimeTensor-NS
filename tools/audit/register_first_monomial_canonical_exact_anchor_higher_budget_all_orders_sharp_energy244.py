#!/usr/bin/env python3
"""Register all-order sharp critical physical H3 energy consequences."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetAllOrdersSharpEnergy244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3Path_higherBudget_anyMoment_linear_forces_sharpEnergyFourth244', 'h3Path_higherBudget_anyMoment_outerCap_excludesQuadratic244', 'h3Path_higherBudget_anyMoment_criticalBranches_force_sharpEnergyFourth244', 'h3Path_noL2Trace_exactAnchor_anyHigherBudget_criticalOuter_sharpEnergyFourth244')

def insert_import(path: Path, imp: str) -> None:
    lines = path.read_text().splitlines()
    if imp in lines:
        return
    positions = [i for i, line in enumerate(lines) if line.startswith('import ')]
    if not positions:
        raise SystemExit(f'No import block found in {path}')
    lines.insert(positions[-1] + 1, imp)
    path.write_text('\n'.join(lines).rstrip() + '\n')

def main() -> None:
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Unproved placeholder or axiom')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    insert_import(ROOT, imp)
    insert_import(AUDIT, imp)
    lines = AUDIT.read_text().splitlines()
    for name in THEOREMS:
        fullname = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + fullname, '#print axioms ' + fullname):
            if command not in lines:
                lines.append(command)
    updated = '\n'.join(lines).rstrip() + '\n'
    if updated != AUDIT.read_text():
        AUDIT.write_text(updated)
    print(f'Registered {len(THEOREMS)} all-order sharp-energy theorems')

if __name__ == '__main__':
    main()
