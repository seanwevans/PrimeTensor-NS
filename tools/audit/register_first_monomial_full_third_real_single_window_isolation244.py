#!/usr/bin/env python3
"""Idempotently register actual full-third single-window Fourier isolation."""
from pathlib import Path
MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSingleWindowIsolation244"
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    "thirdFullAxisWindowBump_width_sep_of_nonresonance244",
    "thirdFullAxisWindowBump_zero_near_distinct_center244",
    "thirdFullAxisWindowBump_nonzero_labels_eq244",
    "thirdFullAxisComplexWindowPacket_zero_near_distinct_center244",
    "thirdFullAxisWindowBump_reflected_zero_near_distinct_center244",
    "thirdFullAxisPositiveThreePacket_zero_at_reflected_frequency244",
    "thirdFullAxisSixFourierPacket_isolated_zero244",
    "thirdFullAxisSixFourierPacket_isolated_one244",
    "thirdFullAxisSixFourierPacket_isolated_two244",
    "thirdFullAxisRealSchwartzSpectrum_isolated_zero244",
    "thirdFullAxisRealSchwartzSpectrum_isolated_one244",
    "thirdFullAxisRealSchwartzSpectrum_isolated_two244",
)

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
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([ln for ln in lines if ln.startswith('import ')] + [imp]))
    body = [ln for ln in lines if not ln.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in (f'#check {q}', f'#print axioms {q}'):
            if check not in body:
                body.append(check)
    result = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if result != old:
        AUDIT.write_text(result)
    print('Registered twelve exact full-third single-window isolation theorems')

if __name__ == '__main__':
    main()
