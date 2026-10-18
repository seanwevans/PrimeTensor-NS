#!/usr/bin/env python3
"""Register exact single-window spectra and phase identities on all six positive sectors."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealPositiveSectorSpectra244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullPositiveMiddleLabel_unique244',
    'thirdFullPositiveLabels_primary244',
    'thirdFullPositiveSector_phase_product244',
    'thirdFullAxisRealSpectrum_isolated_primary_label244',
    'thirdFullActualTripleMass_nonzero_factors244',
    'thirdFullPositiveSector_three_center_labels244',
    'thirdFullPositiveSector_actual_triple_spectra244',
    'thirdFullPositiveSector_actual_triple_component244',
    'thirdFullPositiveSector_actual_gradient_slot244',
)


def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing required file: {p}')
    s = SOURCE.read_text()
    for name in NAMES:
        if f'theorem {name}' not in s:
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([l for l in lines if l.startswith('import ')] + [imp]))
    body = [l for l in lines if not l.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in (f'#check {q}', f'#print axioms {q}'):
            if check not in body:
                body.append(check)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print('Registered positive six-sector exact real Schwartz triple spectra and phases')


if __name__ == '__main__':
    main()
