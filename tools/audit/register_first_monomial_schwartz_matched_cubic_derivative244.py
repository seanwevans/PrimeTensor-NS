#!/usr/bin/env python3
"""Idempotently register the matched actual cubic Schwartz derivatives."""
from pathlib import Path
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzMatchedCubicDerivative244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = [
    'h3ComplexSchwartzRealPart_lineDeriv244',
    'h3ComplexSchwartzRealPart_secondDerivative244',
    'h3ComplexSchwartzRealPart_thirdDerivative244',
    'h3RawSchwartzPhysicalRealInverse_thirdDerivative244',
    'h3Schwartz_fourier_axisDerivative_apply244',
    'h3Schwartz_fourier_secondDerivative_apply244',
    'h3Schwartz_fourier_thirdDerivative_apply244',
    'h3Schwartz_fourier_thirdOfInverse_apply244',
    'h3SpectralScalarRawThirdCoordinateFourierL2_schwartzDerivative244',
    'h3SpectralScalarRawThirdCoordinatePhysicalL2_realSchwartzDerivative244',
    'exists_h3SmoothCompactWeighted_realSchwartzExactThird244',
]

def main():
    for p in [SOURCE, ROOT, AUDIT]:
        if not p.exists():
            raise SystemExit(f'Missing: {p}')
    src=SOURCE.read_text()
    for name in DECLS:
        if f'theorem {name}' not in src:
            raise SystemExit(f'Missing theorem {name}')
    imp='import '+MODULE
    rootlines=ROOT.read_text().splitlines()
    if imp not in rootlines:
        ROOT.write_text('\n'.join(rootlines+[imp])+'\n')
    old=AUDIT.read_text().splitlines()
    header=list(dict.fromkeys([line for line in old if line.startswith('import ')]+[imp]))
    body=[line for line in old if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        qname='PrimeTensor.FirstMonomialTriad.'+name
        for cmd in ['#check '+qname, '#print axioms '+qname]:
            if cmd not in body: body.append(cmd)
    output='\n'.join(header+['']+body).rstrip()+'\n'
    if AUDIT.read_text()!=output: AUDIT.write_text(output)
    print('Registered matched Schwartz cubic derivatives:',len(DECLS),'proof declarations')
if __name__=='__main__': main()
