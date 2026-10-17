# Reference-free completion of the signed 243-slot Schwartz monomial

**Base commit:** `7e1ff4de` (fix Schwartz L4 Minkowski measurability arguments).

This checkpoint avoids assuming a *fixed Schwartz target* for the signed first monomial. The existing quantitative 2–4–4 trilinear perturbation inequality bounds the difference of two signed 243-slot aggregates by twice the finite sum of their actual spatial error envelopes.

Define a sequence of Schwartz velocity triples to have Cauchy-small errors when, for each ordered physical slot `(i,k,l,r,j)` and each `epsilon > 0`, its integrated perturbation envelope is less than `epsilon` for every pair of sufficiently late sequence indices. The new theorem proves that the complete signed 243-slot aggregate is a real Cauchy sequence. Completeness of `ℝ` produces a finite limit. The proof combines an elementary finite-index diagonal argument with the exact previously established spatial error inequality; the physical factor **two** remains intact.

A second theorem proves canonicity: when two approximating sequences have signed monomial limits, and their cross-sequence integrated error envelope tends to zero, the numerical limits coincide. This is a necessary ingredient of defining the signed monomial on a Sobolev graph completion independently of the chosen approximating sequence.

**Unresolved analytical obligations:** construct these Cauchy approximants from actual `W^{4,2}` or appropriate Sobolev jet graphs; derive Cauchy-small integrated error from three per-slot derivative-difference norms and finite uniform root bounds; identify the resulting real limit with the physical trilinear pairing of an arbitrary non-Schwartz H3 velocity. These are not assumed or proved by this patch. Its conclusions do not establish Navier–Stokes global regularity.

**Local validation:** compile the new module, run its audit registration, refresh `proof/order.txt` using `python3 proof/generate_index.py`, then run the source-index check and full `lake build` / baseline audit. The patch has not been compiled by Lean in the artifact environment.
