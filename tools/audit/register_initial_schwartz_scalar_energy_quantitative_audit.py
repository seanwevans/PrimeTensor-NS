#!/usr/bin/env python3
"""Idempotently register the Schwartz scalar/kinetic quantitative audit."""
from pathlib import Path

ROOT = Path('PrimeTensor.lean')
CONTRACTS = Path('tools/audit/Contracts.lean')
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.'
          'OneComponentInitialSchwartzScalarEnergyQuantitativeRate')
CHECKS = [
    'h3Audit_initialHilbert_approxProbeSquaredDefect_of_energyError',
    'h3Audit_initialSchwartzScalarFTC_quantitativePhysicalSquaredError',
    'h3Audit_initialSchwartzScalarFTC_quantitativePhysicalSquaredError_exactCeiling',
]

def main():
    if not ROOT.is_file() or not CONTRACTS.is_file():
        raise SystemExit('Run from PrimeTensor-NS repository root')
    stmt = 'import ' + MODULE
    if stmt not in ROOT.read_text().splitlines():
        with ROOT.open('a') as f:
            f.write('\n-- Quantitative initial Schwartz scalar FTC/kinetic physical L2 errors.\n')
            f.write(stmt + '\n')
    known = set(CONTRACTS.read_text().splitlines())
    missing = [d for d in CHECKS if '#check ' + d not in known]
    if missing:
        with CONTRACTS.open('a') as f:
            f.write('\n-- Quantitative initial Schwartz scalar source and kinetic budget.\n')
            for d in missing:
                f.write('#check ' + d + '\n')
                f.write('#print axioms ' + d + '\n')
    print(f'Quantitative initial trace audit: {len(missing)} new checks')

if __name__ == '__main__':
    main()
