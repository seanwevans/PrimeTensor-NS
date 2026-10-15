# Actual Schwartz adjacent H³ slot Cauchy bounds

**Base:** `3899931c` (physical Schwartz adjacent-energy integration by parts).

This patch applies genuine signed Hölder/Cauchy–Schwarz to arbitrary real
Schwartz functions, then uses the exact integration-by-parts identities
from the previous checkpoint to show for each real velocity component `j`
and axis pair `i,k`:

- `(∫(∂ᵢ fⱼ)²)² ≤ (∫fⱼ²)(∫(∂ᵢ∂ᵢ fⱼ)²)`;
- `(∫(∂ᵢ∂ₖ fⱼ)²)² ≤ (∫(∂ₖ fⱼ)²)(∫(∂ᵢ∂ᵢ∂ₖ fⱼ)²)`.

Each slot has coefficient one and no extra analytical assumptions. **These
slotwise estimates do not by themselves imply the sharp joint inequalities
`E1² ≤ E0 E2` or `E2² ≤ E1 E3`.** The next step must assemble and identify
the complete mixed-derivative contractions, without introducing unwanted
dimension-dependent losses. No endpoint coefficient or continuation statement
is established by this patch.
