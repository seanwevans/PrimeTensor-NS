#!/usr/bin/env python3
"""Register the canonical physical source-spectral amplification bound."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalCriticalSourceSpectralAmplification244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3Path_radialPDEMultiplier_le_fourFifth244', 'h3Path_finiteAnnulusPDEVariation_le_sourceSpectralFifth244', 'h3Path_scalarCriticalWidth_linearEscape_sourceSpectral244', 'h3Path_noExtension_canonicalWidth_forces_sourceSpectralAmplification244')

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Forbidden placeholder in source')
    for t in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(t) + r'\b', content, re.M):
            raise SystemExit(f'Missing theorem: {t}')
    new_import = 'import ' + MODULE
    for p in (ROOT,AUDIT):
        lines = p.read_text().splitlines()
        if new_import not in lines:
            idx = max((i for i,line in enumerate(lines) if line.startswith('import ')),default=-1)
            lines.insert(idx + 1, new_import)
        if p == AUDIT:
            for t in THEOREMS:
                for line in ('#check PrimeTensor.FirstMonomialTriad.'+t, '#print axioms PrimeTensor.FirstMonomialTriad.'+t):
                    if line not in lines:
                        lines.append(line)
        p.write_text('\n'.join(lines).rstrip() + '\n')
    print(f'Registered {len(THEOREMS)} source-spectral amplification theorems.')

if __name__ == '__main__':
    main()
