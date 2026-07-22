import Erdos320.Lemmas.CertificateTransfer

/-!
# Phase-coordinate enclosures for the certificate windows

The nonconstancy certificates (§8 `sec:certificates`, the low finite input
`comp:low`) work at a scale `ξ` (the number `N` of the paper, regarded as a
positive real) and reason about the breakpoint coordinate
`u = log₃ ξ = iteratedLog 3 ξ` — the data-transform coordinate
`u(f) = log₃ x(f)` of `eq:data-transform` — together with the reconstructed
scale `E k u` for `k = 1, 2, 3`.  On the working range `E 3 (log₃ ξ) = ξ` and, one
exponential down at a time,

```
E 1 (log₃ ξ) = log (log ξ),   E 2 (log₃ ξ) = log ξ,   E 3 (log₃ ξ) = ξ.
```

This file provides:

* **Bridge identities** (`E1_iteratedLog3`, `E2_iteratedLog3`) turning
  `E k (iteratedLog 3 ξ)` into iterated logarithms of `ξ`, complementing the
  already-proved `cert_E_three_iteratedLog` (`E 3 (log₃ ξ) = ξ`).
* **Explicit-rational enclosures** of `log ξ`, `log (log ξ)` and `log₃ ξ` on
  the enlarged low window `W = [9 725 449, 10 632 947]`
  (`phaseEnclosure_W`) and the sharp low window `S = [10 140 000, 10 214 000]`
  (`phaseEnclosure_S`), together with their `E`-form restatements
  (`phaseEnclosure_E_W`, `phaseEnclosure_E_S`).

All numeric targets are *verified outer bounds* (each interval genuinely
contains the true value).  The enclosures are obtained by reducing every
`p ≤ log y` / `log y ≤ q` to an `exp` comparison
(`Real.le_log_iff_exp_le`, `Real.log_le_iff_le_exp`) and discharging the
resulting `exp`-of-rational bounds through the repo's digit-of-`e` /
Taylor-remainder toolkit (`Real.exp_one_lt_d9`, `Real.exp_one_gt_d9`,
`Real.exp_bound'`, `Real.sum_le_exp_of_nonneg`), mirroring
`cert_exp_16_18_gt`.

To thread the tightest level (the `log₃`-target) through cleanly the log-log
level is proved at slightly sharper *internal* constants than the stated
bundle exposes; the exposed bundle bounds follow by `linarith`.  The internal
sharpening is genuinely needed at the low-window `log₃ ξ` lower bound: the
chain `exp 1.021808 ≤ 2.778213` is numerically false
(`exp 1.021808 = 2.7782132… > 2.778213`), so the proof runs the log-log lower
bound at the sharper internal value `2.7782135`, which delivers the stated
`log₃ ξ ≥ 1.021808`.
-/

namespace Erdos320

/-! ## Bridge identities: `E k (log₃ ξ)` as iterated logarithms -/

/-- `E 1 (log₃ ξ) = log (log ξ)` for `ξ ≥ 15` (peeling the outermost
`exp`/`log` inverse pair; `log₃ ξ = log (log (log ξ))`). -/
theorem E1_iteratedLog3 {ξ : ℝ} (hξ : (15 : ℝ) ≤ ξ) :
    E 1 (iteratedLog 3 ξ) = Real.log (Real.log ξ) := by
  have hy1 : (1 : ℝ) < Real.log ξ := by
    have he : Real.exp 1 < ξ := by have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log ξ := Real.log_lt_log (Real.exp_pos 1) he
  have hz0 : (0 : ℝ) < Real.log (Real.log ξ) := Real.log_pos hy1
  rw [show (1 : ℕ) = 0 + 1 from rfl, E_succ, E_zero, cert_iteratedLog_three_eq,
    Real.exp_log hz0]

/-- `E 2 (log₃ ξ) = log ξ` for `ξ ≥ 15` (peeling two `exp`/`log` inverse
pairs). -/
theorem E2_iteratedLog3 {ξ : ℝ} (hξ : (15 : ℝ) ≤ ξ) :
    E 2 (iteratedLog 3 ξ) = Real.log ξ := by
  have hy1 : (1 : ℝ) < Real.log ξ := by
    have he : Real.exp 1 < ξ := by have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log ξ := Real.log_lt_log (Real.exp_pos 1) he
  have hy0 : (0 : ℝ) < Real.log ξ := by linarith
  have hz0 : (0 : ℝ) < Real.log (Real.log ξ) := Real.log_pos hy1
  rw [show (2 : ℕ) = 1 + 1 from rfl, E_succ, show (1 : ℕ) = 0 + 1 from rfl,
    E_succ, E_zero, cert_iteratedLog_three_eq, Real.exp_log hz0,
    Real.exp_log hy0]

/-! ## `exp`-of-rational anchors for the low window `W`

Every anchor reduces `exp t ≤ r` (resp. `r ≤ exp t`) by splitting
`t = ti + f` with `ti ∈ ℕ`, `f ∈ [0,1]`, bounding `exp 1 ^ ti` by a digit
power of `e` and `exp f` by a Taylor upper/lower bound. -/

set_option maxHeartbeats 400000 in
/-- `exp 16.090256 ≤ 9 725 449` (so `log ξ ≥ 16.090256` on `W`). -/
theorem expW_logξ_lo_anchor : Real.exp (16.090256 : ℝ) ≤ 9725449 := by
  have hsplit : Real.exp (16.090256 : ℝ)
      = Real.exp 1 ^ 16 * Real.exp (0.090256 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 16 ≤ (2.7182818286 : ℝ) ^ 16 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 16
  have hef : Real.exp (0.090256 : ℝ) ≤ (1.094454429 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.090256 : ℝ) by norm_num)
      (by norm_num) (n := 6) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 16 * Real.exp (0.090256 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 16 * (1.094454429 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 9725449 := by norm_num

set_option maxHeartbeats 400000 in
/-- `10 632 947 ≤ exp 16.179468` (so `log ξ ≤ 16.179468` on `W`). -/
theorem expW_logξ_hi_anchor : (10632947 : ℝ) ≤ Real.exp (16.179468 : ℝ) := by
  have hsplit : Real.exp (16.179468 : ℝ)
      = Real.exp 1 ^ 16 * Real.exp (0.179468 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 16 ≤ Real.exp 1 ^ 16 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 16
  have hef : (1.196580611 : ℝ) ≤ Real.exp (0.179468 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.179468 : ℝ) by norm_num) 7)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (10632947 : ℝ) ≤ (2.7182818283 : ℝ) ^ 16 * (1.196580611 : ℝ) := by
        norm_num
    _ ≤ Real.exp 1 ^ 16 * Real.exp (0.179468 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- `exp 2.7782135 ≤ 16.090256` (internal log-log lower anchor on `W`). -/
theorem expW_loglog_lo_anchor : Real.exp (2.7782135 : ℝ) ≤ 16.090256 := by
  have hsplit : Real.exp (2.7782135 : ℝ)
      = Real.exp 1 ^ 2 * Real.exp (0.7782135 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
  have hef : Real.exp (0.7782135 : ℝ) ≤ (2.177578545 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.7782135 : ℝ) by norm_num)
      (by norm_num) (n := 10) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 2 * Real.exp (0.7782135 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 2 * (2.177578545 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 16.090256 := by norm_num

/-- `16.179468 ≤ exp 2.7837431` (internal log-log upper anchor on `W`). -/
theorem expW_loglog_hi_anchor : (16.179468 : ℝ) ≤ Real.exp (2.7837431 : ℝ) := by
  have hsplit : Real.exp (2.7837431 : ℝ)
      = Real.exp 1 ^ 2 * Real.exp (0.7837431 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 2
  have hef : (2.189653033 : ℝ) ≤ Real.exp (0.7837431 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.7837431 : ℝ) by norm_num) 11)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (16.179468 : ℝ) ≤ (2.7182818283 : ℝ) ^ 2 * (2.189653033 : ℝ) := by
        norm_num
    _ ≤ Real.exp 1 ^ 2 * Real.exp (0.7837431 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- `exp 1.021808 ≤ 2.7782135` (`W` `log₃`-lower anchor, matching the internal
log-log lower bound). -/
theorem expW_il3_lo_anchor : Real.exp (1.021808 : ℝ) ≤ 2.7782135 := by
  have hsplit : Real.exp (1.021808 : ℝ)
      = Real.exp 1 ^ 1 * Real.exp (0.021808 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 1 ≤ (2.7182818286 : ℝ) ^ 1 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 1
  have hef : Real.exp (0.021808 : ℝ) ≤ (1.022047533 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.021808 : ℝ) by norm_num)
      (by norm_num) (n := 6) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 1 * Real.exp (0.021808 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 1 * (1.022047533 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 2.7782135 := by norm_num

/-- `2.7837431 ≤ exp 1.023797` (`W` `log₃`-upper anchor, matching the internal
log-log upper bound). -/
theorem expW_il3_hi_anchor : (2.7837431 : ℝ) ≤ Real.exp (1.023797 : ℝ) := by
  have hsplit : Real.exp (1.023797 : ℝ)
      = Real.exp 1 ^ 1 * Real.exp (0.023797 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 1 ≤ Real.exp 1 ^ 1 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 1
  have hef : (1.024082408 : ℝ) ≤ Real.exp (0.023797 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.023797 : ℝ) by norm_num) 6)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (2.7837431 : ℝ) ≤ (2.7182818283 : ℝ) ^ 1 * (1.024082408 : ℝ) := by
        norm_num
    _ ≤ Real.exp 1 ^ 1 * Real.exp (0.023797 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-! ## `exp`-of-rational anchors for the sharp window `S` -/

set_option maxHeartbeats 400000 in
/-- `exp 16.131998 ≤ 10 140 000` (so `log ξ ≥ 16.131998` on `S`). -/
theorem expS_logξ_lo_anchor : Real.exp (16.131998 : ℝ) ≤ 10140000 := by
  have hsplit : Real.exp (16.131998 : ℝ)
      = Real.exp 1 ^ 16 * Real.exp (0.131998 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 16 ≤ (2.7182818286 : ℝ) ^ 16 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 16
  have hef : Real.exp (0.131998 : ℝ) ≤ (1.141106039 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.131998 : ℝ) by norm_num)
      (by norm_num) (n := 6) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 16 * Real.exp (0.131998 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 16 * (1.141106039 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 10140000 := by norm_num

set_option maxHeartbeats 400000 in
/-- `10 214 000 ≤ exp 16.13927` (so `log ξ ≤ 16.13927` on `S`). -/
theorem expS_logξ_hi_anchor : (10214000 : ℝ) ≤ Real.exp (16.13927 : ℝ) := by
  have hsplit : Real.exp (16.13927 : ℝ)
      = Real.exp 1 ^ 16 * Real.exp (0.13927 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 16 ≤ Real.exp 1 ^ 16 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 16
  have hef : (1.149434405 : ℝ) ≤ Real.exp (0.13927 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.13927 : ℝ) by norm_num) 7)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (10214000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 16 * (1.149434405 : ℝ) := by
        norm_num
    _ ≤ Real.exp 1 ^ 16 * Real.exp (0.13927 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- `exp 2.7808047 ≤ 16.131998` (internal log-log lower anchor on `S`). -/
theorem expS_loglog_lo_anchor : Real.exp (2.7808047 : ℝ) ≤ 16.131998 := by
  have hsplit : Real.exp (2.7808047 : ℝ)
      = Real.exp 1 ^ 2 * Real.exp (0.7808047 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
  have hef : Real.exp (0.7808047 : ℝ) ≤ (2.183228404 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.7808047 : ℝ) by norm_num)
      (by norm_num) (n := 10) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 2 * Real.exp (0.7808047 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 2 * (2.183228404 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 16.131998 := by norm_num

/-- `16.13927 ≤ exp 2.781256` (internal log-log upper anchor on `S`). -/
theorem expS_loglog_hi_anchor : (16.13927 : ℝ) ≤ Real.exp (2.781256 : ℝ) := by
  have hsplit : Real.exp (2.781256 : ℝ)
      = Real.exp 1 ^ 2 * Real.exp (0.781256 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 2
  have hef : (2.184213890 : ℝ) ≤ Real.exp (0.781256 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.781256 : ℝ) by norm_num) 10)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (16.13927 : ℝ) ≤ (2.7182818283 : ℝ) ^ 2 * (2.184213890 : ℝ) := by
        norm_num
    _ ≤ Real.exp 1 ^ 2 * Real.exp (0.781256 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- `exp 1.02274 ≤ 2.7808047` (`S` `log₃`-lower anchor, matching the internal
log-log lower bound). -/
theorem expS_il3_lo_anchor : Real.exp (1.02274 : ℝ) ≤ 2.7808047 := by
  have hsplit : Real.exp (1.02274 : ℝ)
      = Real.exp 1 ^ 1 * Real.exp (0.02274 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 1 ≤ (2.7182818286 : ℝ) ^ 1 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 1
  have hef : Real.exp (0.02274 : ℝ) ≤ (1.023000525 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.02274 : ℝ) by norm_num)
      (by norm_num) (n := 6) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 1 * Real.exp (0.02274 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 1 * (1.023000525 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 2.7808047 := by norm_num

/-- `2.781256 ≤ exp 1.022903` (`S` `log₃`-upper anchor, matching the internal
log-log upper bound). -/
theorem expS_il3_hi_anchor : (2.781256 : ℝ) ≤ Real.exp (1.022903 : ℝ) := by
  have hsplit : Real.exp (1.022903 : ℝ)
      = Real.exp 1 ^ 1 * Real.exp (0.022903 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 1 ≤ Real.exp 1 ^ 1 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 1
  have hef : (1.023167287 : ℝ) ≤ Real.exp (0.022903 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.022903 : ℝ) by norm_num) 6)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (2.781256 : ℝ) ≤ (2.7182818283 : ℝ) ^ 1 * (1.023167287 : ℝ) := by
        norm_num
    _ ≤ Real.exp 1 ^ 1 * Real.exp (0.022903 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-! ## Bundled explicit-rational enclosures -/

/-- **Low-window enclosure** `W = [9 725 449, 10 632 947]`:
`log ξ ∈ [16.090256, 16.179468]`, `log (log ξ) ∈ [2.778213, 2.783744]`, and
`log₃ ξ ∈ [1.021808, 1.023797]`. -/
theorem phaseEnclosure_W {ξ : ℝ} (h1 : (9725449 : ℝ) ≤ ξ)
    (h2 : ξ ≤ 10632947) :
    (16.090256 : ℝ) ≤ Real.log ξ ∧ Real.log ξ ≤ 16.179468
      ∧ (2.778213 : ℝ) ≤ Real.log (Real.log ξ)
        ∧ Real.log (Real.log ξ) ≤ 2.783744
      ∧ (1.021808 : ℝ) ≤ iteratedLog 3 ξ ∧ iteratedLog 3 ξ ≤ 1.023797 := by
  have hξpos : (0 : ℝ) < ξ := by linarith
  have hL_lo : (16.090256 : ℝ) ≤ Real.log ξ := by
    rw [Real.le_log_iff_exp_le hξpos]; linarith [expW_logξ_lo_anchor]
  have hL_hi : Real.log ξ ≤ 16.179468 := by
    rw [Real.log_le_iff_le_exp hξpos]; linarith [expW_logξ_hi_anchor]
  have hlogpos : (0 : ℝ) < Real.log ξ := by linarith
  have hLL_lo : (2.7782135 : ℝ) ≤ Real.log (Real.log ξ) := by
    rw [Real.le_log_iff_exp_le hlogpos]; linarith [expW_loglog_lo_anchor]
  have hLL_hi : Real.log (Real.log ξ) ≤ 2.7837431 := by
    rw [Real.log_le_iff_le_exp hlogpos]; linarith [expW_loglog_hi_anchor]
  have hLLpos : (0 : ℝ) < Real.log (Real.log ξ) := by linarith
  have hil3_lo : (1.021808 : ℝ) ≤ iteratedLog 3 ξ := by
    rw [cert_iteratedLog_three_eq, Real.le_log_iff_exp_le hLLpos]
    linarith [expW_il3_lo_anchor]
  have hil3_hi : iteratedLog 3 ξ ≤ 1.023797 := by
    rw [cert_iteratedLog_three_eq, Real.log_le_iff_le_exp hLLpos]
    linarith [expW_il3_hi_anchor]
  exact ⟨hL_lo, hL_hi, by linarith, by linarith, hil3_lo, hil3_hi⟩

/-- **Sharp-window enclosure** `S = [10 140 000, 10 214 000]`:
`log ξ ∈ [16.131998, 16.13927]`, `log (log ξ) ∈ [2.780804, 2.781256]`, and
`log₃ ξ ∈ [1.02274, 1.022903]`. -/
theorem phaseEnclosure_S {ξ : ℝ} (h1 : (10140000 : ℝ) ≤ ξ)
    (h2 : ξ ≤ 10214000) :
    (16.131998 : ℝ) ≤ Real.log ξ ∧ Real.log ξ ≤ 16.13927
      ∧ (2.780804 : ℝ) ≤ Real.log (Real.log ξ)
        ∧ Real.log (Real.log ξ) ≤ 2.781256
      ∧ (1.02274 : ℝ) ≤ iteratedLog 3 ξ ∧ iteratedLog 3 ξ ≤ 1.022903 := by
  have hξpos : (0 : ℝ) < ξ := by linarith
  have hL_lo : (16.131998 : ℝ) ≤ Real.log ξ := by
    rw [Real.le_log_iff_exp_le hξpos]; linarith [expS_logξ_lo_anchor]
  have hL_hi : Real.log ξ ≤ 16.13927 := by
    rw [Real.log_le_iff_le_exp hξpos]; linarith [expS_logξ_hi_anchor]
  have hlogpos : (0 : ℝ) < Real.log ξ := by linarith
  have hLL_lo : (2.7808047 : ℝ) ≤ Real.log (Real.log ξ) := by
    rw [Real.le_log_iff_exp_le hlogpos]; linarith [expS_loglog_lo_anchor]
  have hLL_hi : Real.log (Real.log ξ) ≤ 2.781256 := by
    rw [Real.log_le_iff_le_exp hlogpos]; linarith [expS_loglog_hi_anchor]
  have hLLpos : (0 : ℝ) < Real.log (Real.log ξ) := by linarith
  have hil3_lo : (1.02274 : ℝ) ≤ iteratedLog 3 ξ := by
    rw [cert_iteratedLog_three_eq, Real.le_log_iff_exp_le hLLpos]
    linarith [expS_il3_lo_anchor]
  have hil3_hi : iteratedLog 3 ξ ≤ 1.022903 := by
    rw [cert_iteratedLog_three_eq, Real.log_le_iff_le_exp hLLpos]
    linarith [expS_il3_hi_anchor]
  exact ⟨hL_lo, hL_hi, by linarith, hLL_hi, hil3_lo, hil3_hi⟩

/-! ## `E`-form corollaries

`E 1 (log₃ ξ) = log (log ξ)`, `E 2 (log₃ ξ) = log ξ`, `E 3 (log₃ ξ) = ξ`, so
the bundled enclosures restate directly in terms of `E k (iteratedLog 3 ξ)`. -/

/-- Shared `E`-form repackaging (`ξ ≥ 15`): given `log (log ξ) ∈ [a, b]` and
`log ξ ∈ [c, d]`, restate these as bounds on `E 1 (log₃ ξ)` and `E 2 (log₃ ξ)`,
adding `E 3 (log₃ ξ) = ξ`, via the bridge identities `E1_iteratedLog3`,
`E2_iteratedLog3`, `cert_E_three_iteratedLog`.  Every `E`-form corollary of a
bundled enclosure (low `W`/`S`, high `WH`/`H46`) is a two-line application. -/
theorem phaseEnclosure_E_of_log {ξ a b c d : ℝ} (h15 : (15 : ℝ) ≤ ξ)
    (hLL_lo : a ≤ Real.log (Real.log ξ)) (hLL_hi : Real.log (Real.log ξ) ≤ b)
    (hL_lo : c ≤ Real.log ξ) (hL_hi : Real.log ξ ≤ d) :
    a ≤ E 1 (iteratedLog 3 ξ) ∧ E 1 (iteratedLog 3 ξ) ≤ b
      ∧ c ≤ E 2 (iteratedLog 3 ξ) ∧ E 2 (iteratedLog 3 ξ) ≤ d
      ∧ E 3 (iteratedLog 3 ξ) = ξ := by
  rw [E1_iteratedLog3 h15, E2_iteratedLog3 h15]
  exact ⟨hLL_lo, hLL_hi, hL_lo, hL_hi, cert_E_three_iteratedLog h15⟩

/-- `E`-form of `phaseEnclosure_W`: `E 1 (log₃ ξ) ∈ [2.778213, 2.783744]`,
`E 2 (log₃ ξ) ∈ [16.090256, 16.179468]`, `E 3 (log₃ ξ) = ξ`. -/
theorem phaseEnclosure_E_W {ξ : ℝ} (h1 : (9725449 : ℝ) ≤ ξ)
    (h2 : ξ ≤ 10632947) :
    (2.778213 : ℝ) ≤ E 1 (iteratedLog 3 ξ)
        ∧ E 1 (iteratedLog 3 ξ) ≤ 2.783744
      ∧ (16.090256 : ℝ) ≤ E 2 (iteratedLog 3 ξ)
        ∧ E 2 (iteratedLog 3 ξ) ≤ 16.179468
      ∧ E 3 (iteratedLog 3 ξ) = ξ := by
  obtain ⟨hL_lo, hL_hi, hLL_lo, hLL_hi, _, _⟩ := phaseEnclosure_W h1 h2
  exact phaseEnclosure_E_of_log (by linarith) hLL_lo hLL_hi hL_lo hL_hi

/-- `E`-form of `phaseEnclosure_S`: `E 1 (log₃ ξ) ∈ [2.780804, 2.781256]`,
`E 2 (log₃ ξ) ∈ [16.131998, 16.13927]`, `E 3 (log₃ ξ) = ξ`. -/
theorem phaseEnclosure_E_S {ξ : ℝ} (h1 : (10140000 : ℝ) ≤ ξ)
    (h2 : ξ ≤ 10214000) :
    (2.780804 : ℝ) ≤ E 1 (iteratedLog 3 ξ)
        ∧ E 1 (iteratedLog 3 ξ) ≤ 2.781256
      ∧ (16.131998 : ℝ) ≤ E 2 (iteratedLog 3 ξ)
        ∧ E 2 (iteratedLog 3 ξ) ≤ 16.13927
      ∧ E 3 (iteratedLog 3 ξ) = ξ := by
  obtain ⟨hL_lo, hL_hi, hLL_lo, hLL_hi, _, _⟩ := phaseEnclosure_S h1 h2
  exact phaseEnclosure_E_of_log (by linarith) hLL_lo hLL_hi hL_lo hL_hi

end Erdos320
