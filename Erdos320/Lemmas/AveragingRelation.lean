import Erdos320.Lemmas.AveragingUpper
import Erdos320.Lemmas.AveragingLower

/-!
# The asymptotic averaging relation (paper `prop:averaging-relation`)

Combining the two halves (`AveragingUpper.lean`, `AveragingLower.lean`):
```
𝓡(X) = F(e^X) − 𝓑(X)  satisfies  |𝓡(X)| ≤ 7·(log X)²/X   for X ≥ 10⁷.
```
This is the paper's `𝓡(X) ≪ (log X)²/X` (eq. `averaging-relation`) with the
implicit constant and threshold made explicit (7 and 10⁷).  The paper's
`O`-statement is recovered a fortiori.
-/

namespace Erdos320

/-- Paper `prop:averaging-relation` (eq. `averaging-relation`), explicit form:
`|𝓡(X)| ≤ 7 (log X)²/X` for `X ≥ 10⁷`. -/
theorem averaging_relation {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    |averagingError X| ≤ 7 * Real.log X ^ 2 / X := by
  have hup := averagingError_le hX
  have hlo := neg_le_averagingError hX
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by positivity) hX
  have h47 : 4 * Real.log X ^ 2 / X ≤ 7 * Real.log X ^ 2 / X := by
    apply div_le_div_of_nonneg_right _ hX0.le
    nlinarith [sq_nonneg (Real.log X)]
  rw [abs_le]
  constructor
  · linarith
  · exact hup

end Erdos320
