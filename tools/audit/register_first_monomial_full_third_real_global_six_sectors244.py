#!/usr/bin/env python3
"""Register exact global six-sector full-third physical integral and axiom audit."""
from pathlib import Path
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealGlobalSixSectors244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = ('thirdFullHilbertCoherentSector_measurable244', 'thirdFullAxisImagKernel_integrable_global244', 'thirdFullFiniteDisjointIndicatorSum244', 'thirdFullAxisImagKernel_integral_eq_twelve_sectors244', 'thirdFullCoherentPairLabel_reflect244', 'thirdFullHilbertCoherentSector_reflect_mem244', 'thirdFullAxisImagKernel_reflected_sector_integral244', 'thirdFullAxisImagKernel_integral_eq_twice_six_sectors244', 'thirdFullAxisRealThirdCommutator_eq_global_six_sectors244', 'thirdFullAxisRealThirdCommutator_neg_iff_global_six244')

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    source = SOURCE.read_text()
    for name in NAMES:
        if f'theorem {name}' not in source:
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in (f'#check {qualified}', f'#print axioms {qualified}'):
            if command not in body:
                body.append(command)
    output = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if output != original:
        AUDIT.write_text(output)
    print('Registered exact global six-sector H3 imaginary-kernel integral')

if __name__ == '__main__':
    main()
