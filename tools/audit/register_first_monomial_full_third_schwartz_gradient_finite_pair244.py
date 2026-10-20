#!/usr/bin/env python3
"""Register all 243 signed gradient slots, pair modulus, and limit criterion."""
from pathlib import Path
import re
MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientFinitePair244"
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = ('fullGradientTripleSpectralPairEnvelope_nonneg244', 'fullSchwartzGradientAxis_spectralPair_modulus244', 'fullSchwartzGradientTransport_spectralPair_modulus244', 'exists_fullSchwartzGradientTransport_limit_of_spectralPairGauge244')

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f"Missing {p}")
    src = SOURCE.read_text()
    if re.search(r"\b(?:sorry|admit)\b", src):
        raise SystemExit("Lean proof placeholder")
    actual = set(re.findall(r"^theorem\s+(\w+)", src, re.M))
    if not set(NAMES) <= actual:
        raise SystemExit(f"Missing theorems: {set(NAMES) - actual}")
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip(): body.pop(0)
    for name in NAMES:
        full = 'PrimeTensor.FirstMonomialTriad.' + name
        for line in ('#check ' + full, '#print axioms ' + full):
            if line not in body: body.append(line)
    result = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if result != old: AUDIT.write_text(result)
    print(f'Registered {len(NAMES)} gradient pair / 243-axis theorems')

if __name__ == '__main__': main()
