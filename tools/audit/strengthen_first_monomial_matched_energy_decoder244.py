#!/usr/bin/env python3
"""Strengthen the existing synchronized E2/E3 construction without copying its proof.

The original public theorem retains its exact statement; it becomes a projection
of its stronger decoder-retaining version.  Safe to run more than once.
"""
from pathlib import Path

PATH = Path("PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3SchwartzMatchedEnergyCauchy244.lean")
OLD = "exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy_matched244"
NEW = "exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy_withDecoder244"
FOLLOWING = "/-- Retain the existing public existence API unchanged"
OLD_DOC = (
    "/-- The concrete matched compact-frequency real Schwartz sequence satisfies\n"
    "the project's original integrated E₂/E₃ difference-energy Cauchy criterion. -/\n"
)
NEW_DOC_START = "/-- One synchronized smooth-compact weighted spectral and real-Schwartz\n"


def repair_adjacent_docstrings(src: str) -> tuple[str, bool]:
    """Repair the already-applied prior patch, preserving all theorem bodies."""
    redundant = OLD_DOC + NEW_DOC_START
    if redundant in src:
        return src.replace(redundant, NEW_DOC_START, 1), True
    return src, False

def main():
    src = PATH.read_text()
    src, repaired = repair_adjacent_docstrings(src)
    if "theorem " + NEW in src:
        if repaired:
            PATH.write_text(src)
            print("Repaired adjacent documentation comments in existing matched-energy theorem")
        else:
            print("Matched E2/E3 decoder theorem already present (no changes)")
        return
    theorem_begin = src.index("theorem " + OLD + "\n")
    if not src[:theorem_begin].endswith(OLD_DOC):
        raise SystemExit("Unexpected original matched-energy documentation boundary")
    # Replace the old documentation along with its theorem, but extract the
    # actual theorem body WITHOUT including the old documentation text.
    begin = theorem_begin - len(OLD_DOC)
    end = src.index(FOLLOWING, theorem_begin)
    original = src[theorem_begin:end].rstrip()
    head, body = original.split(" := by\n", 1)
    needle = "      Tendsto V atTop (𝓝 U) ∧\n"
    assert head.count(needle) == 1
    new_head = head.replace("theorem " + OLD, "theorem " + NEW, 1).replace(
        needle, needle + "      (∀ n j, h3SpectralVelocityDecodeRealL2 (V n) j =\n        (Ψ n j).toLp 2 (volume : Measure V3)) ∧\n", 1)
    assert "hWeighted, _, hSecondExact" in body
    body = body.replace("hWeighted, _, hSecondExact", "hWeighted, hDecoderExact, hSecondExact", 1)
    marker = "refine ⟨V, Ψ, hWeighted, hEnergy, ?_, ?_⟩"
    assert body.count(marker) == 1
    body = body.replace(marker, "refine ⟨V, Ψ, hWeighted, hDecoderExact, hEnergy, ?_, ?_⟩", 1)
    stronger = new_head + " := by\n" + body
    wrapper = head + " := by\n" + (
        "  obtain ⟨V, Ψ, hWeighted, _hDecoder, hEnergy, hSecond, hThird⟩ :=\n"
        "    " + NEW + " U\n"
        "  exact ⟨V, Ψ, hWeighted, hEnergy, hSecond, hThird⟩\n")
    doc = "/-- One synchronized smooth-compact weighted spectral and real-Schwartz\n"
    doc += "sequence retains its exact zero-order real decoder alongside its\n"
    doc += "complete E₂/E₃ difference-energy Cauchy and matched physical jets.\n"
    doc += "In particular, it can be upgraded to pointwise C¹ realization. -/\n"
    new = doc + stronger.rstrip() + "\n\n/-- Backwards-compatible projection of the strengthened construction. -/\n" + wrapper + "\n"
    src = src[:begin] + new + src[end:]
    assert src.count("theorem " + OLD + "\n") == 1
    assert src.count("theorem " + NEW + "\n") == 1
    PATH.write_text(src)
    print("Strengthened matched E2/E3 construction; preserved original API")

if __name__ == "__main__":
    main()
