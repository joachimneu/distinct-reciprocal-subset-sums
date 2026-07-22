import Erdos320.Lemmas.PhaseEnclosure

/-!
# Phase-coordinate enclosures for the *high* certificate window

This is the high-window analogue of `Erdos320.Lemmas.PhaseEnclosure`, feeding the
high finite input (`comp:high`, §8 `sec:certificates`).  Where the
low file works at scales `ξ ≈ 10⁷` (breakpoint coordinate `log₃ ξ ≈ 1.02`), the
high window sits at `ξ ≈ 10²⁷–10²⁸` (breakpoint coordinate `log₃ ξ ≈ 1.42`).  The
construction is identical: reduce every `p ≤ log y` / `log y ≤ q` to an `exp`
comparison (`Real.le_log_iff_exp_le`, `Real.log_le_iff_le_exp`) and discharge
the resulting `exp`-of-rational bounds through the repo's digit-of-`e` /
Taylor-remainder
toolkit (`Real.exp_one_lt_d9`, `Real.exp_one_gt_d9`, `Real.exp_bound'`,
`Real.sum_le_exp_of_nonneg`).  The bridge identities `E1_iteratedLog3`,
`E2_iteratedLog3` and the endpoint identity `cert_E_three_iteratedLog` are reused
from the low file.

This file provides:

* **Explicit-rational enclosures** of `log ξ`, `log (log ξ)` and `log₃ ξ` on the
  full high window `WH = [8·10²⁶, 1.3·10²⁸]` (`phaseEnclosure_WH`) and the sharp
  window `H46 = [1.2004·10²⁸, 1.2009·10²⁸]` bracketing the right endpoint
  `1.001·x(46)` of the top high chord window (`f = 46`, `x(46) = N₁·46/log N₁`)
  (`phaseEnclosure_H46`), together with their `E`-form restatements
  (`phaseEnclosure_E_WH`, `phaseEnclosure_E_H46`).

All numeric targets are *verified outer bounds* (each interval genuinely
contains the true value).
-/

namespace Erdos320

/-! ## `exp`-of-rational anchors for the full high window `WH`

Every anchor reduces `exp t ≤ r` (resp. `r ≤ exp t`) by splitting `t = ti + f`
with `ti ∈ ℕ`, `f ∈ [0,1]`, bounding `exp 1 ^ ti` by a digit power of `e` and
`exp f` by a Taylor upper/lower bound. -/

set_option maxHeartbeats 800000 in
/-- `exp 61.94665 ≤ 8·10²⁶` (so `log ξ ≥ 61.94665` on `WH`). -/
theorem expWH_logξ_lo_anchor : Real.exp (61.94665 : ℝ) ≤ 8e26 := by
  have hsplit : Real.exp (61.94665 : ℝ)
      = Real.exp 1 ^ 61 * Real.exp (0.94665 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 61 ≤ (2.7182818286 : ℝ) ^ 61 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 61
  have hef : Real.exp (0.94665 : ℝ) ≤ (2.577065 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.94665 : ℝ) by norm_num)
      (by norm_num) (n := 14) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 61 * Real.exp (0.94665 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 61 * (2.577065 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 8e26 := by norm_num

set_option maxHeartbeats 800000 in
/-- `1.3·10²⁸ ≤ exp 64.73475` (so `log ξ ≤ 64.73475` on `WH`). -/
theorem expWH_logξ_hi_anchor : (1.3e28 : ℝ) ≤ Real.exp (64.73475 : ℝ) := by
  have hsplit : Real.exp (64.73475 : ℝ)
      = Real.exp 1 ^ 64 * Real.exp (0.73475 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 64 ≤ Real.exp 1 ^ 64 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 64
  have hef : (2.084957 : ℝ) ≤ Real.exp (0.73475 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.73475 : ℝ) by norm_num) 14)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (1.3e28 : ℝ) ≤ (2.7182818283 : ℝ) ^ 64 * (2.084957 : ℝ) := by
        norm_num
    _ ≤ Real.exp 1 ^ 64 * Real.exp (0.73475 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- `exp 4.12627 ≤ 61.94665` (log-log lower anchor on `WH`). -/
theorem expWH_loglog_lo_anchor : Real.exp (4.12627 : ℝ) ≤ 61.94665 := by
  have hsplit : Real.exp (4.12627 : ℝ)
      = Real.exp 1 ^ 4 * Real.exp (0.12627 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
  have hef : Real.exp (0.12627 : ℝ) ≤ (1.134590 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.12627 : ℝ) by norm_num)
      (by norm_num) (n := 8) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 4 * Real.exp (0.12627 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 4 * (1.134590 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 61.94665 := by norm_num

/-- `64.73475 ≤ exp 4.1703` (log-log upper anchor on `WH`). -/
theorem expWH_loglog_hi_anchor : (64.73475 : ℝ) ≤ Real.exp (4.1703 : ℝ) := by
  have hsplit : Real.exp (4.1703 : ℝ)
      = Real.exp 1 ^ 4 * Real.exp (0.1703 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 4
  have hef : (1.185659 : ℝ) ≤ Real.exp (0.1703 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.1703 : ℝ) by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (64.73475 : ℝ) ≤ (2.7182818283 : ℝ) ^ 4 * (1.185659 : ℝ) := by
        norm_num
    _ ≤ Real.exp 1 ^ 4 * Real.exp (0.1703 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- `exp 1.41737 ≤ 4.12627` (`WH` `log₃`-lower anchor). -/
theorem expWH_il3_lo_anchor : Real.exp (1.41737 : ℝ) ≤ 4.12627 := by
  have hsplit : Real.exp (1.41737 : ℝ)
      = Real.exp 1 ^ 1 * Real.exp (0.41737 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 1 ≤ (2.7182818286 : ℝ) ^ 1 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 1
  have hef : Real.exp (0.41737 : ℝ) ≤ (1.517967 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.41737 : ℝ) by norm_num)
      (by norm_num) (n := 9) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 1 * Real.exp (0.41737 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 1 * (1.517967 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 4.12627 := by norm_num

/-- `4.1703 ≤ exp 1.42799` (`WH` `log₃`-upper anchor). -/
theorem expWH_il3_hi_anchor : (4.1703 : ℝ) ≤ Real.exp (1.42799 : ℝ) := by
  have hsplit : Real.exp (1.42799 : ℝ)
      = Real.exp 1 ^ 1 * Real.exp (0.42799 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 1 ≤ Real.exp 1 ^ 1 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 1
  have hef : (1.534169 : ℝ) ≤ Real.exp (0.42799 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.42799 : ℝ) by norm_num) 9)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (4.1703 : ℝ) ≤ (2.7182818283 : ℝ) ^ 1 * (1.534169 : ℝ) := by
        norm_num
    _ ≤ Real.exp 1 ^ 1 * Real.exp (0.42799 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-! ## Bundled explicit-rational enclosures -/

/-- **Full high-window enclosure** `WH = [8·10²⁶, 1.3·10²⁸]`:
`log ξ ∈ [61.94665, 64.73475]`, `log (log ξ) ∈ [4.12627, 4.1703]`, and
`log₃ ξ ∈ [1.41737, 1.42799]`.  All bounds are verified outer bounds. -/
theorem phaseEnclosure_WH {ξ : ℝ} (h1 : (8e26 : ℝ) ≤ ξ) (h2 : ξ ≤ 1.3e28) :
    (61.94665 : ℝ) ≤ Real.log ξ ∧ Real.log ξ ≤ 64.73475
      ∧ (4.12627 : ℝ) ≤ Real.log (Real.log ξ)
        ∧ Real.log (Real.log ξ) ≤ 4.1703
      ∧ (1.41737 : ℝ) ≤ iteratedLog 3 ξ ∧ iteratedLog 3 ξ ≤ 1.42799 := by
  have hξpos : (0 : ℝ) < ξ := by linarith
  have hL_lo : (61.94665 : ℝ) ≤ Real.log ξ := by
    rw [Real.le_log_iff_exp_le hξpos]; linarith [expWH_logξ_lo_anchor]
  have hL_hi : Real.log ξ ≤ 64.73475 := by
    rw [Real.log_le_iff_le_exp hξpos]; linarith [expWH_logξ_hi_anchor]
  have hlogpos : (0 : ℝ) < Real.log ξ := by linarith
  have hLL_lo : (4.12627 : ℝ) ≤ Real.log (Real.log ξ) := by
    rw [Real.le_log_iff_exp_le hlogpos]; linarith [expWH_loglog_lo_anchor]
  have hLL_hi : Real.log (Real.log ξ) ≤ 4.1703 := by
    rw [Real.log_le_iff_le_exp hlogpos]; linarith [expWH_loglog_hi_anchor]
  have hLLpos : (0 : ℝ) < Real.log (Real.log ξ) := by linarith
  have hil3_lo : (1.41737 : ℝ) ≤ iteratedLog 3 ξ := by
    rw [cert_iteratedLog_three_eq, Real.le_log_iff_exp_le hLLpos]
    linarith [expWH_il3_lo_anchor]
  have hil3_hi : iteratedLog 3 ξ ≤ 1.42799 := by
    rw [cert_iteratedLog_three_eq, Real.log_le_iff_le_exp hLLpos]
    linarith [expWH_il3_hi_anchor]
  exact ⟨hL_lo, hL_hi, hLL_lo, hLL_hi, hil3_lo, hil3_hi⟩

/-! ## `E`-form corollaries

`E 1 (log₃ ξ) = log (log ξ)`, `E 2 (log₃ ξ) = log ξ`, `E 3 (log₃ ξ) = ξ` (all
for `ξ ≥ 15`, via `E1_iteratedLog3` / `E2_iteratedLog3` / `cert_E_three_iteratedLog`
reused from the low file), so the bundled enclosures restate directly in terms of
`E k (iteratedLog 3 ξ)`. -/

/-- `E`-form of `phaseEnclosure_WH`: `E 1 (log₃ ξ) ∈ [4.12627, 4.1703]`,
`E 2 (log₃ ξ) ∈ [61.94665, 64.73475]`, `E 3 (log₃ ξ) = ξ`. -/
theorem phaseEnclosure_E_WH {ξ : ℝ} (h1 : (8e26 : ℝ) ≤ ξ) (h2 : ξ ≤ 1.3e28) :
    (4.12627 : ℝ) ≤ E 1 (iteratedLog 3 ξ)
        ∧ E 1 (iteratedLog 3 ξ) ≤ 4.1703
      ∧ (61.94665 : ℝ) ≤ E 2 (iteratedLog 3 ξ)
        ∧ E 2 (iteratedLog 3 ξ) ≤ 64.73475
      ∧ E 3 (iteratedLog 3 ξ) = ξ := by
  obtain ⟨hL_lo, hL_hi, hLL_lo, hLL_hi, _, _⟩ := phaseEnclosure_WH h1 h2
  exact phaseEnclosure_E_of_log (by linarith) hLL_lo hLL_hi hL_lo hL_hi

/-! ## `exp`-of-rational anchors for the sharp window `H46`

The tight window bracketing the right endpoint `1.001·x(46)` of the top high
chord window (`f = 46`, `x(46) = N₁·46/log N₁`), where the normalized slope of
the core profile attains its minimum; consumed by the slope/curvature
certificate `highDataCert`.  Same anchor pattern as above. -/

set_option maxHeartbeats 800000 in
/-- `exp 64.6549 ≤ 1.2004·10²⁸` (so `log ξ ≥ 64.6549` on `H46`). -/
theorem expH46_logξ_lo_anchor : Real.exp (64.6549 : ℝ) ≤ 1.2004e28 := by
  have hsplit : Real.exp (64.6549 : ℝ)
      = Real.exp 1 ^ 64 * Real.exp (0.6549 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 64 ≤ (2.7182818286 : ℝ) ^ 64 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 64
  have hef : Real.exp (0.6549 : ℝ) ≤ (1.925100 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.6549 : ℝ) by norm_num)
      (by norm_num) (n := 14) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 64 * Real.exp (0.6549 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 64 * (1.925100 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 1.2004e28 := by norm_num

set_option maxHeartbeats 800000 in
/-- `1.2009·10²⁸ ≤ exp 64.6555` (so `log ξ ≤ 64.6555` on `H46`). -/
theorem expH46_logξ_hi_anchor : (1.2009e28 : ℝ) ≤ Real.exp (64.6555 : ℝ) := by
  have hsplit : Real.exp (64.6555 : ℝ)
      = Real.exp 1 ^ 64 * Real.exp (0.6555 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 64 ≤ Real.exp 1 ^ 64 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 64
  have hef : (1.926050 : ℝ) ≤ Real.exp (0.6555 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.6555 : ℝ) by norm_num) 14)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (1.2009e28 : ℝ) ≤ (2.7182818283 : ℝ) ^ 64 * (1.926050 : ℝ) := by
        norm_num
    _ ≤ Real.exp 1 ^ 64 * Real.exp (0.6555 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- `exp 4.169063 ≤ 64.6549` (log-log lower anchor on `H46`). -/
theorem expH46_loglog_lo_anchor : Real.exp (4.169063 : ℝ) ≤ 64.6549 := by
  have hsplit : Real.exp (4.169063 : ℝ)
      = Real.exp 1 ^ 4 * Real.exp (0.169063 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
  have hef : Real.exp (0.169063 : ℝ) ≤ (1.1841953 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.169063 : ℝ) by norm_num)
      (by norm_num) (n := 8) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 4 * Real.exp (0.169063 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 4 * (1.1841953 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 64.6549 := by norm_num

/-- `64.6555 ≤ exp 4.169074` (log-log upper anchor on `H46`). -/
theorem expH46_loglog_hi_anchor : (64.6555 : ℝ) ≤ Real.exp (4.169074 : ℝ) := by
  have hsplit : Real.exp (4.169074 : ℝ)
      = Real.exp 1 ^ 4 * Real.exp (0.169074 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 4
  have hef : (1.1842073 : ℝ) ≤ Real.exp (0.169074 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.169074 : ℝ) by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (64.6555 : ℝ) ≤ (2.7182818283 : ℝ) ^ 4 * (1.1842073 : ℝ) := by
        norm_num
    _ ≤ Real.exp 1 ^ 4 * Real.exp (0.169074 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- `exp 1.427689 ≤ 4.169063` (`H46` `log₃`-lower anchor). -/
theorem expH46_il3_lo_anchor : Real.exp (1.427689 : ℝ) ≤ 4.169063 := by
  have hsplit : Real.exp (1.427689 : ℝ)
      = Real.exp 1 ^ 1 * Real.exp (0.427689 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 1 ≤ (2.7182818286 : ℝ) ^ 1 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 1
  have hef : Real.exp (0.427689 : ℝ) ≤ (1.533710 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.427689 : ℝ) by norm_num)
      (by norm_num) (n := 9) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 1 * Real.exp (0.427689 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 1 * (1.533710 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 4.169063 := by norm_num

/-- `4.169074 ≤ exp 1.427696` (`H46` `log₃`-upper anchor). -/
theorem expH46_il3_hi_anchor : (4.169074 : ℝ) ≤ Real.exp (1.427696 : ℝ) := by
  have hsplit : Real.exp (1.427696 : ℝ)
      = Real.exp 1 ^ 1 * Real.exp (0.427696 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 1 ≤ Real.exp 1 ^ 1 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 1
  have hef : (1.533718 : ℝ) ≤ Real.exp (0.427696 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.427696 : ℝ) by norm_num) 9)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (4.169074 : ℝ) ≤ (2.7182818283 : ℝ) ^ 1 * (1.533718 : ℝ) := by
        norm_num
    _ ≤ Real.exp 1 ^ 1 * Real.exp (0.427696 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- **Sharp-window enclosure** `H46 = [1.2004·10²⁸, 1.2009·10²⁸]` bracketing the
right endpoint `1.001·x(46)` of the top high chord window
(`f = 46`, `x(46) = N₁·46/log N₁`):
`log ξ ∈ [64.6549, 64.6555]`, `log (log ξ) ∈ [4.169063, 4.169074]`, and
`log₃ ξ ∈ [1.427689, 1.427696]`.  All bounds are verified outer bounds. -/
theorem phaseEnclosure_H46 {ξ : ℝ} (h1 : (1.2004e28 : ℝ) ≤ ξ)
    (h2 : ξ ≤ 1.2009e28) :
    (64.6549 : ℝ) ≤ Real.log ξ ∧ Real.log ξ ≤ 64.6555
      ∧ (4.169063 : ℝ) ≤ Real.log (Real.log ξ)
        ∧ Real.log (Real.log ξ) ≤ 4.169074
      ∧ (1.427689 : ℝ) ≤ iteratedLog 3 ξ ∧ iteratedLog 3 ξ ≤ 1.427696 := by
  have hξpos : (0 : ℝ) < ξ := by linarith
  have hL_lo : (64.6549 : ℝ) ≤ Real.log ξ := by
    rw [Real.le_log_iff_exp_le hξpos]; linarith [expH46_logξ_lo_anchor]
  have hL_hi : Real.log ξ ≤ 64.6555 := by
    rw [Real.log_le_iff_le_exp hξpos]; linarith [expH46_logξ_hi_anchor]
  have hlogpos : (0 : ℝ) < Real.log ξ := by linarith
  have hLL_lo : (4.169063 : ℝ) ≤ Real.log (Real.log ξ) := by
    rw [Real.le_log_iff_exp_le hlogpos]; linarith [expH46_loglog_lo_anchor]
  have hLL_hi : Real.log (Real.log ξ) ≤ 4.169074 := by
    rw [Real.log_le_iff_le_exp hlogpos]; linarith [expH46_loglog_hi_anchor]
  have hLLpos : (0 : ℝ) < Real.log (Real.log ξ) := by linarith
  have hil3_lo : (1.427689 : ℝ) ≤ iteratedLog 3 ξ := by
    rw [cert_iteratedLog_three_eq, Real.le_log_iff_exp_le hLLpos]
    linarith [expH46_il3_lo_anchor]
  have hil3_hi : iteratedLog 3 ξ ≤ 1.427696 := by
    rw [cert_iteratedLog_three_eq, Real.log_le_iff_le_exp hLLpos]
    linarith [expH46_il3_hi_anchor]
  exact ⟨hL_lo, hL_hi, hLL_lo, hLL_hi, hil3_lo, hil3_hi⟩

/-- `E`-form of `phaseEnclosure_H46`: `E 1 (log₃ ξ) ∈ [4.169063, 4.169074]`,
`E 2 (log₃ ξ) ∈ [64.6549, 64.6555]`, `E 3 (log₃ ξ) = ξ`. -/
theorem phaseEnclosure_E_H46 {ξ : ℝ} (h1 : (1.2004e28 : ℝ) ≤ ξ)
    (h2 : ξ ≤ 1.2009e28) :
    (4.169063 : ℝ) ≤ E 1 (iteratedLog 3 ξ)
        ∧ E 1 (iteratedLog 3 ξ) ≤ 4.169074
      ∧ (64.6549 : ℝ) ≤ E 2 (iteratedLog 3 ξ)
        ∧ E 2 (iteratedLog 3 ξ) ≤ 64.6555
      ∧ E 3 (iteratedLog 3 ξ) = ξ := by
  obtain ⟨hL_lo, hL_hi, hLL_lo, hLL_hi, _, _⟩ := phaseEnclosure_H46 h1 h2
  exact phaseEnclosure_E_of_log (by linarith) hLL_lo hLL_hi hL_lo hL_hi

end Erdos320
