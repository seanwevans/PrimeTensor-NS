#!/usr/bin/env python3
"""Register physical order-four velocity convolution escape corridor."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopConvolutionCorridor244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3Path_thirdRadialForcing_le_orderFourConvolutionEnvelope244', 'h3_scalar_orderFourConvolutionBudget_forces_largePair244', 'h3PathOrderFourVelocityConvolutionPairNorm_eq244', 'h3Path_unboundedPhysicalTop_forces_orderFourVelocityConvolutionPairs244')

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing required file: {p}')
    src = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', src):
        raise SystemExit('Proof placeholder detected')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+'+re.escape(name)+r'\b', src, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import '+MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([l for l in lines if l.startswith('import ')] + [imp]))
    rest = [l for l in lines if not l.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for n in THEOREMS:
        fq='PrimeTensor.FirstMonomialTriad.'+n
        for cmd in ('#check '+fq, '#print axioms '+fq):
            if cmd not in rest:
                rest.append(cmd)
    content='\n'.join(imports+['']+rest).rstrip()+'\n'
    if content != original:
        AUDIT.write_text(content)
    print('Registered',len(THEOREMS),'physical convolution corridor theorems')

if __name__ == '__main__':
    main()
