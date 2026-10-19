#!/usr/bin/env python3
"""Register the unguarded actual full-third physical Schwartz six-sector formulas."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalMassGateRemoval244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullPhysicalOrderedSymbol_zero_first244',
    'thirdFullPhysicalOrderedSymbol_zero_middle244',
    'thirdFullPhysicalOrderedSymbol_zero_last244',
    'thirdFullPositiveSectorPhysicalCore_zero_of_bareGerm244',
    'thirdFullActualSpectrum_zero_bareGerm_of_window244',
    'thirdFullActualTripleMass_zero_vector_alt244',
    'thirdFullPositiveSectorPhysicalPolynomial_zero_of_tripleMass244',
    'thirdFullPositiveSectorMassGated_eq_physicalPolynomial244',
    'thirdFullPositiveSectorActualImag_eq_physicalPolynomial244',
    'thirdFullPositiveSectorActualIntegral_eq_physicalPolynomial244',
    'thirdFullPositiveSixSectorIntegral_eq_physicalPolynomials244',
    'thirdFullAxisRealThirdCommutator_eq_physicalPolynomial_six244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    if 'sorry' in source or 'admit' in source:
        raise SystemExit('Forbidden proof placeholder')
    for name in NAMES:
        if f'theorem {name}' not in source and f'def {name}' not in source:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for item in (f'#check {q}', f'#print axioms {q}'):
            if item not in body:
                body.append(item)
    update = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if update != original:
        AUDIT.write_text(update)
    print('Registered unconditional full-third Schwartz physical mass-gate removal')

if __name__ == '__main__':
    main()
