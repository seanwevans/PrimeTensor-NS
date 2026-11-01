# Cleanup for accidental single-span registration before gap-spike root build

Base HEAD: `9416cc82` (accepted gradient transport budget).

The gradient-energy gap-spike module imports the accepted gradient transport budget directly. The earlier experimental `TerminalActualSourceExcessSingleSpanGradientBudget` module is NOT a dependency. However, running its registrar on the user's working tree leaves an import in `PrimeTensor.lean` and in `tools/audit/FirstMonomialTriad.lean`, and four `#check` / four `#print axioms` lines in the latter. The root compile then attempts to load an absent `.olean` for that optional experimental module.

Run `python3 tools/audit/cleanup_stale_single_span_for_gap_spike.py --apply` and then `--check`. The cleanup removes only the exact ten stale registration lines. If the three experimental files exist and are untracked, it relocates them under a unique `~/Downloads/primetensor-single-span-backup-*` directory rather than deleting them, preventing the generated proof index from referring to uncommitted source. It refuses to move tracked files. The gap-spike module source and its audit checks are unchanged. Regenerate `proof/order.txt`, compile the root, and run the repository audit before committing.

This is an import/build hygiene correction. It does not prove the single-span lemma or change any mathematical assumptions.
