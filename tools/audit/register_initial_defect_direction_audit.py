#!/usr/bin/env python3
"""Idempotently add the H³ initial defect-direction module and axioms audit.

This does not rewrite the large auto-maintained PrimeTensor.lean / Contracts
sources. It is safe to rerun; missing legacy audit imports should be restored
separately by the already-committed restore_initial_trace_audit.py script.
"""
from pathlib import Path

root = Path('PrimeTensor.lean')
contracts = Path('tools/audit/Contracts.lean')
module = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.'
          'OneComponentInitialDefectDirectionObstruction')
checks = [
    'h3Audit_initialPhysicalMismatch_normModulus_and_lower',
    'h3Audit_initialSubcriticalEnergyRate_physicalMismatchModulus',
    'h3Audit_initialStrongPhysicalLimit_eq_of_defectDirectionSequence',
    'H3AuditInitialDefectDirectionWeakSequence',
    'h3Audit_initialDefectDirectionWeakSequence_identifies_strongLimit',
    'h3Audit_initialSubcriticalDefectSequence_identifies_physicalAndKineticRate',
]


def main():
    if not root.is_file() or not contracts.is_file():
        raise SystemExit('Run from repository root (PrimeTensor.lean and tools/audit/Contracts.lean required)')
    lines = root.read_text().splitlines()
    decl = 'import ' + module
    if decl not in lines:
        with root.open('a') as f:
            f.write('\n-- H3 initial-time mismatch: audit-checked, included in default build.\n')
            f.write(decl + '\n')
        print('Added PrimeTensor root module import')
    else:
        print('PrimeTensor root module import already present')
    lines = contracts.read_text().splitlines()
    missing = [name for name in checks if '#check ' + name not in lines]
    if missing:
        with contracts.open('a') as f:
            f.write('\n-- Initial physical defect-direction obstruction and weak sequence bridge.\n')
            for name in missing:
                f.write('#check ' + name + '\n')
                if not name.startswith('H3Audit'):
                    f.write('#print axioms ' + name + '\n')
    print(f'Added {len(missing)} theorem/contract checks')


if __name__ == '__main__':
    main()
