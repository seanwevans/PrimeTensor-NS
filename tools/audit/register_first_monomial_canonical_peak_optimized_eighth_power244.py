#!/usr/bin/env python3
"""Register sharp sixth-root physical H3 dissipation optimization at actual canonical source maxima."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakOptimizedEighthPower244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3Path_optimizedSixthRootRadius244', 'h3Path_sixthRootCoercivity_algebraicEighthPower244', 'h3Path_physicalSpectralPeak_optimizedEighthPower244', 'h3Path_physicalSpectralPeak_optimizedEighthPower_div244', 'h3Path_cofinalSpectralPeaks_eventualOptimizedEighthPower244', 'h3Path_noL2Trace_canonicalWidth_sourcePeakOptimizedEighthPower244')

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing file: {path}")
    text = SOURCE.read_text()
    if re.search(r"^\s*(?:sorry|admit|axiom)(?:\s|$)", text, re.M):
        raise SystemExit("Unproved placeholder or axiom")
    for name in THEOREMS:
        if not re.search(r"^\s*theorem\s+" + re.escape(name) + r"\b", text, re.M):
            raise SystemExit(f"Missing theorem: {name}")
    new_import = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if new_import not in root:
        ROOT.write_text('\n'.join(root + [new_import]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [new_import]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for theorem in THEOREMS:
        name = 'PrimeTensor.FirstMonomialTriad.' + theorem
        for stmt in ('#check ' + name, '#print axioms ' + name):
            if stmt not in rest:
                rest.append(stmt)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != old:
        AUDIT.write_text(updated)
    print(f'Registered {len(THEOREMS)} canonical optimized eighth-power theorems.')

if __name__ == '__main__':
    main()
