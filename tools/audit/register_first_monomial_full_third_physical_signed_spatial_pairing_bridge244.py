#!/usr/bin/env python3
"""Register proof that the 243 real integrals equal the old spatial energy pairing.

Idempotently migrate misplaced Lean imports back to the header (including
imports accidentally inserted at the end of audit files by older registrars).
"""
from pathlib import Path
import re

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSignedSpatialPairingBridge244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'h3ActualPhysicalJetFourierCarrier_ae_eq_oldJetField244',
    'h3ActualSignedFirstMonomialDensity_ae_eq_oldPhysical244',
    'h3ActualSignedFirstMonomialSlotIntegral_eq_oldPhysicalIntegral244',
    'h3PathCanonicalInterpolationMonomialPairing_eq_actualSignedSlot244',
    'h3PathCanonicalFirstMonomialAggregate_eq_actualSigned244',
    'h3PathCanonicalFirstMonomialAggregate_eq_canonicalSecondL4Integral244',
)
DEFS = ('h3OldPhysicalSignedFirstMonomialDensity244',)


def header_import(lines, statement):
    # Preserve all existing lines and comments, but move every Lean import to
    # the header. The old audit registration pattern could append stray imports.
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [statement]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    return imports + [''] + body


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Proof placeholder in proposed module')
    for kw, names in [('theorem', DECLS), ('noncomputable def', DEFS)]:
        for declaration in names:
            if not re.search('^'+kw+r'\s+'+re.escape(declaration)+r'\b', source, re.M):
                raise SystemExit(f'Missing declaration: {kw} {declaration}')
    statement = 'import ' + MODULE
    for file in (ROOT, AUDIT):
        old = file.read_text()
        if file == ROOT and all(not line.strip() or line.startswith('import ')
                                for line in old.splitlines()):
            # PrimeTensor.lean is import-only: append without reformatting thousands of imports.
            if statement in old.splitlines():
                lines = old.splitlines()
            else:
                lines = old.splitlines() + [statement]
        else:
            lines = header_import(old.splitlines(), statement)
        if file == AUDIT:
            for declaration in (*DECLS, *DEFS):
                qualified = 'PrimeTensor.FirstMonomialTriad.' + declaration
                for command in ('#check ' + qualified, '#print axioms ' + qualified):
                    if command not in lines:
                        lines.append(command)
        new = '\n'.join(lines).rstrip() + '\n'
        if new != old:
            file.write_text(new)
    print('Registered exact old-physical 243-slot integral and energy-pairing identity')

if __name__ == '__main__':
    main()
