#!/usr/bin/env python3
"""Register actual 81 physical cubic jet spectral identification."""
from pathlib import Path
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzActualThirdJetIdentification244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'h3SpectralScalarRawThirdCoordinateFourierL2_actualJet244',
    'h3SpectralScalarRawThirdCoordinatePhysicalL2_actualJet244',
    'h3SpectralVelocityThirdPhysicalJetFamily_actualJet244',
    'exists_h3SchwartzSpectralApprox_actualZeroAndPhysicalThird244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing expected file: {p}')
    src = SOURCE.read_text()
    for name in DECLS:
        if f'theorem {name}' not in src:
            raise SystemExit(f'Missing theorem declaration: {name}')
    imp = 'import ' + MODULE
    imports = ROOT.read_text().splitlines()
    if imp not in imports:
        ROOT.write_text('\n'.join(imports + [imp]) + '\n')
    audit = AUDIT.read_text().splitlines()
    header = list(dict.fromkeys([line for line in audit if line.startswith('import ')] + [imp]))
    body = [line for line in audit if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        qname = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qname, '#print axioms ' + qname):
            if command not in body:
                body.append(command)
    out = '\n'.join(header + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != out:
        AUDIT.write_text(out)
    print('Registered actual third jet identification and convergence')

if __name__ == '__main__':
    main()
