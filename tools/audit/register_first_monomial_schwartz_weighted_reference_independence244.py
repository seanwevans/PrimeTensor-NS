#!/usr/bin/env python3
"""Register weighted H3 matched Schwartz transport reference-independence theorems."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzWeightedReferenceIndependence244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('def', 'matchedSpectralSecondFourierJets244'),
    ('def', 'matchedSpectralThirdFourierJets244'),
    ('theorem', 'continuous_matchedSpectralSecondFourierJets244'),
    ('theorem', 'continuous_matchedSpectralThirdFourierJets244'),
    ('theorem', 'finite_pi_L2_crossSquare_tendsto_zero244'),
    ('theorem', 'matchedSpectral_crossEnergy2_eq_squareSum244'),
    ('theorem', 'matchedSpectral_crossEnergy3_eq_squareSum244'),
    ('theorem', 'matchedSpectral_crossEnergy_vanishes_of_sameLimit244'),
    ('theorem', 'completedSchwartzH3FirstMonomial_eq_of_sameWeightedLimit244'),
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing expected file: {p}')
    code = SOURCE.read_text()
    for kind, name in DECLS:
        if f'{kind} {name}' not in code:
            raise SystemExit(f'Missing declaration: {kind} {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    old = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in old if line.startswith('import ')] + [imp]))
    body = [line for line in old if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for _, name in DECLS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in body:
                body.append(command)
    merged = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != merged:
        AUDIT.write_text(merged)
    print('Registered weighted H3 matched Schwartz reference independence')

if __name__ == '__main__':
    main()
