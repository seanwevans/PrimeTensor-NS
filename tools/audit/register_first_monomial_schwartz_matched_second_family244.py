#!/usr/bin/env python3
"""Register the continuous quadratic physical jet family and matched H³ density."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzMatchedSecondFamily244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'norm_h3SpectralScalarRawSecondCoordinateFourierL2_le244',
    'h3SpectralScalarRawSecondCoordinateFourierL2_sub244',
    'norm_h3SpectralScalarRawSecondCoordinateFourierL2_sub_le244',
    'continuous_h3SpectralScalarRawSecondCoordinateFourierL2_244',
    'continuous_h3SpectralScalarRawSecondCoordinatePhysicalL2_244',
    'h3SpectralVelocitySecondPhysicalJetFamily244',
    'continuous_h3SpectralVelocitySecondPhysicalJetFamily244',
    'h3SpectralVelocitySecondPhysicalJetFamily_tendsto_of_weighted244',
    'h3SpectralScalarRawSecondCoordinateFourierL2_actualJet244',
    'h3SpectralScalarRawSecondCoordinatePhysicalL2_actualJet244',
    'h3SpectralVelocitySecondPhysicalJetFamily_actualJet244',
    'exists_h3SmoothCompactWeighted_realSchwartzAllSecondThirdSequence244',
    'exists_h3SmoothCompactWeighted_actualSecondThirdJetSequence244',
    'exists_h3SmoothCompactWeighted_realSchwartzSecondThirdL2Cauchy244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing expected file: {p}')
    source = SOURCE.read_text()
    for name in DECLS:
        if not any(f'{prefix} {name}' in source for prefix in ('theorem', 'def')):
            raise SystemExit(f'Missing Lean declaration: {name}')
    imp = 'import ' + MODULE
    imports = ROOT.read_text().splitlines()
    if imp not in imports:
        ROOT.write_text('\n'.join(imports + [imp]) + '\n')
    audit = AUDIT.read_text().splitlines()
    header = list(dict.fromkeys(
        [line for line in audit if line.startswith('import ')] + [imp]
    ))
    body = [line for line in audit if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + fq, '#print axioms ' + fq):
            if command not in body:
                body.append(command)
    updated = '\n'.join(header + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered matched 27-second / 81-third physical H³ jet family')

if __name__ == '__main__':
    main()
