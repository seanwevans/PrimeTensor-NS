#!/usr/bin/env python3
"""Register the exact physical spectral anchor canonical PDE clock bridge."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorSource244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_exactAnchor_productSquare_le_physicalEnergySource244',
    'h3Path_actualSpectralAnchor_sq_le_physicalEnergy244',
    'h3Path_exactAnchor_PDELinearRate_sq_le_energySource244',
    'h3Path_cubicHighSnapshot_has_exactAnchorCanonicalClock244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', source, re.M):
        raise SystemExit('Prohibited proof placeholder or axiom')
    for theorem in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(theorem) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {theorem}')
    new_import = 'import ' + MODULE
    for path in (ROOT, AUDIT):
        data = path.read_text()
        lines = data.splitlines()
        if new_import not in lines:
            if path == ROOT:
                lines.append(new_import)
            else:
                idx = next((i for i, line in enumerate(lines) if not line.startswith('import ') and line.strip()), len(lines))
                lines.insert(idx, new_import)
        if path == AUDIT:
            for theorem in THEOREMS:
                name = 'PrimeTensor.FirstMonomialTriad.' + theorem
                for directive in ('#check ' + name, '#print axioms ' + name):
                    if directive not in lines:
                        lines.append(directive)
        new_data = '\n'.join(lines).rstrip() + '\n'
        if new_data != data:
            path.write_text(new_data)
    print(f'Registered {len(THEOREMS)} exact-anchor PDE bridge theorems.')

if __name__ == '__main__':
    main()
