import Erdos320.Lemmas.AveragingRelation
import Erdos320.Lemmas.ElementaryThreshold
import Erdos320.Lemmas.BSlopes
import Erdos320.Lemmas.ExpFloor
import Erdos320.Lemmas.IteratedExpBounds

/-!
# The threshold estimate (paper `lem:threshold`) and the recurrence-error
# bound (paper eq. `rho-small` of `lem:exact-recurrence`)

The paper's `lem:threshold` (eqs. `threshold`, `threshold-additive`) locates
the threshold index `m_*(X)` at `X·log X/F(X)` up to relative error
`O((log₂X)²/(F(X)·log X))`; the additive form is
```
X·log X/m_*(X) = F(X) + O((log₂X)²/log X).
```
This file proves the additive form with explicit constant and threshold
(`threshold_additive`): error at most `100·(log₂X)²/log X` for
`X ≥ exp(exp 20)`.  The paper states the lemma "as `X → ∞`"; making the
argument explicit forces a concrete starting point, and `exp(exp 20)`
(≈ `10^(2.1·10⁸)`) is chosen so that `log X ≥ e²⁰ > 10⁷` (the averaging
relation `averaging_relation` applies at both scales `log X` and `log m`)
and `log₂X ≥ 20` (so `(log₂X)²/log X ≤ e⁻¹⁰ ≤ 1/20000`, which keeps every
constant absorption below elementary).  Every numerical use of the lemma in
the manuscript is at iterated-exponential scales far above this threshold.

Along the way we prove the paper's intermediate estimates with explicit
constants:

* `1 ≪ F(X) ≪ log₂X` (proof of `lem:threshold`):
  `thr_FReal_lower` (`0.34 ≤ F(X)`, from the `m = 1` summand of `𝓑`) and
  `thr_FReal_upper` (`F(X) ≤ log₂X + 3`, from the dyadic bound
  `thr_B_le : 𝓑(Y) ≤ log Y + 2`).
* eq. `slow-variation`: `threshold_slow_variation`
  (`|F(m) − F(X)| ≤ 15·(log₂X)²/log X` on the window
  `log X ≤ log m ≤ log X + 2·log₂X`, which contains `[m₀/2, 2m₀]`).

Finally, `rhoDepth_abs_le` combines `threshold_additive` at `X = E_r(u)`
with `averaging_relation` at `E_{r-1}(u)` to obtain the paper's
eq. `rho-small` (`lem:exact-recurrence`) with explicit constant:
```
|ρ_r(u)| ≤ 107·E_{r-2}(u)²/E_{r-1}(u)   for r ≥ 5, u ∈ [1, e].
```
The depth threshold `r ≥ 5` makes `E_{r-1}(u) ≥ E₄(1) = e^{E₃(1)} > e^{3.8·10⁶}`,
comfortably above both `10⁷` and `e^{e²⁰}` after one more exponentiation.
-/

namespace Erdos320

/-! ## Elementary numeric estimates -/

/-- `10⁷ ≤ e²⁰` (via the Taylor term `20¹³/13!`). -/
theorem thr_ten_pow_seven_le_exp_twenty : (10 : ℝ) ^ 7 ≤ Real.exp 20 := by
  have hfac : ((Nat.factorial 13 : ℕ) : ℝ) = 6227020800 := by
    norm_num [Nat.factorial]
  have h := pow_div_factorial_le_exp (by norm_num : (0:ℝ) ≤ 20) 13
  rw [hfac] at h
  calc (10 : ℝ) ^ 7 ≤ (20 : ℝ) ^ 13 / 6227020800 := by norm_num
    _ ≤ Real.exp 20 := h

/-- `20000 ≤ e¹⁰` (from the digit bound `Real.exp_one_gt_d9`). -/
theorem thr_twenty_thousand_le_exp_ten : (20000 : ℝ) ≤ Real.exp 10 := by
  have h9 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have hpow : (20000 : ℝ) ≤ 2.7182818283 ^ (10 : ℕ) := by norm_num
  calc (20000 : ℝ) ≤ 2.7182818283 ^ (10 : ℕ) := hpow
    _ ≤ Real.exp 1 ^ (10 : ℕ) := pow_le_pow_left₀ (by norm_num) h9 10
    _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num

/-- `log t ≤ t/2` for `t ≥ 8` (from `t ≤ t²/8 = (t/2)²/2! ≤ e^{t/2}`). -/
theorem thr_log_le_half {t : ℝ} (ht : 8 ≤ t) : Real.log t ≤ t / 2 := by
  have ht0 : (0:ℝ) < t := by linarith
  rw [Real.log_le_iff_le_exp ht0]
  have h := pow_div_factorial_le_exp (x := t / 2) (by linarith) 2
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hfac] at h
  nlinarith [h]

/-! ## The scale bookkeeping for `X ≥ exp(exp 20)` -/

/-- For `X ≥ exp(exp 20)`, the averaging scale satisfies `log X ≥ e²⁰`. -/
theorem thr_exp20_le_log {X : ℝ} (hX : Real.exp (Real.exp 20) ≤ X) :
    Real.exp 20 ≤ Real.log X := by
  have hX0 : (0:ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
  rw [Real.le_log_iff_exp_le hX0]
  exact hX

/-- For `X ≥ exp(exp 20)`, the double logarithm satisfies `log₂X ≥ 20`. -/
theorem thr_twenty_le_loglog {X : ℝ} (hX : Real.exp (Real.exp 20) ≤ X) :
    (20 : ℝ) ≤ Real.log (Real.log X) := by
  have h := thr_exp20_le_log hX
  have hL0 : (0:ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 20) h
  rw [Real.le_log_iff_exp_le hL0]
  exact h

/-- For `X ≥ exp(exp 20)`, the paper's error scale `A_X = (log₂X)²/log X`
is at most `e⁻¹⁰ ≤ 1/20000`: `(log₂X)² ≤ e^{log₂X/2} = √(log X)`. -/
theorem thr_A_le {X : ℝ} (hX : Real.exp (Real.exp 20) ≤ X) :
    Real.log (Real.log X) ^ 2 / Real.log X ≤ 1 / 20000 := by
  have hL := thr_exp20_le_log hX
  have hLL := thr_twenty_le_loglog hX
  have hL0 : (0:ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 20) hL
  have h1 : Real.log (Real.log X) ^ 2 ≤ Real.exp (Real.log (Real.log X) / 2) :=
    sq_le_exp_half hLL
  have h2 : Real.exp (Real.log (Real.log X)) = Real.log X := Real.exp_log hL0
  have h3 : Real.log (Real.log X) ^ 2 / Real.log X
      ≤ Real.exp (Real.log (Real.log X) / 2) / Real.log X :=
    div_le_div_of_nonneg_right h1 hL0.le
  have h4 : Real.exp (Real.log (Real.log X) / 2) / Real.log X
      = Real.exp (Real.log (Real.log X) / 2 - Real.log (Real.log X)) := by
    rw [Real.exp_sub, h2]
  have h5 : Real.exp (Real.log (Real.log X) / 2 - Real.log (Real.log X))
      ≤ Real.exp (-10 : ℝ) := Real.exp_le_exp.mpr (by linarith)
  have h6 : Real.exp (-10 : ℝ) ≤ 1 / 20000 := by
    rw [Real.exp_neg, show (1:ℝ)/20000 = ((20000:ℝ))⁻¹ by norm_num,
      inv_le_comm₀ (Real.exp_pos 10) (by norm_num), inv_inv]
    exact thr_twenty_thousand_le_exp_ten
  linarith

/-! ## The lower bound `1 ≪ F(X)`: the `m = 1` summand of `𝓑`

The paper's proof of `lem:threshold`: "The `m = 1` summand of `𝓑(log X)`
gives the constant lower bound."  That summand is `min(g(1), log X)/2 =
(log 2)/2`, since `g(1) = log S(1) = log 2`. -/

/-- `S(1) = 2`: the two reciprocal subset sums of `{1}` are `0` and `1`. -/
theorem thr_S_one : S 1 = 2 :=
  le_antisymm (by simpa using S_le_two_pow 1) (by simpa using add_one_le_S 1)

/-- `g(1) = log 2`. -/
theorem thr_g_one : g 1 = Real.log 2 := by
  rw [g, thr_S_one]
  norm_num

/-- `𝓑(0) = 0` (every summand is clamped to `min(g(m), 0) = 0`). -/
theorem thr_B_zero : B 0 = 0 := by
  have h : ∀ m : ℕ, BTerm 0 m = 0 := fun m => by
    rw [BTerm, min_eq_right (g_nonneg (m + 1)), zero_div]
  calc B 0 = ∑' _m : ℕ, (0:ℝ) := tsum_congr h
    _ = 0 := tsum_zero

/-- `𝓑(1) ≤ 1` (chord from `0` with slope `1/m_*(0) ≤ 1`). -/
theorem thr_B_le_one : B 1 ≤ 1 := by
  have h := B_sub_le_div_mStar (X := (0:ℝ)) (Y := 1) le_rfl zero_le_one
  rw [thr_B_zero, sub_zero, sub_zero] at h
  have hpos : 0 < mStar (0:ℝ) := mStar_pos le_rfl
  have h1 : (1:ℝ) ≤ (mStar (0:ℝ) : ℝ) := by exact_mod_cast hpos
  have h2 : (1:ℝ) / (mStar (0:ℝ) : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hpos)]
    exact h1
  linarith

/-! ## The upper bound `F(X) ≪ log₂X`: dyadic growth of `𝓑`

The paper splits the sum defining `𝓑(log X)` at `m = ⌊log X/log 2⌋`.  We
realize the same `log`-growth by iterating the chord bound
`𝓑(Y) − 𝓑(Y/2) ≤ (Y/2)/m_*(Y/2) ≤ log 2` (using `m_*(t) > t/log 2`,
`lem:elementary-threshold`) down a dyadic cascade. -/

/-- Dyadic cascade: `𝓑(Y) ≤ 1 + n·log 2` whenever `0 ≤ Y ≤ 2ⁿ`. -/
theorem thr_B_le_of_le_two_pow :
    ∀ (n : ℕ) {Y : ℝ}, 0 ≤ Y → Y ≤ 2 ^ n → B Y ≤ 1 + n * Real.log 2 := by
  intro n
  induction n with
  | zero =>
    intro Y _hY0 hY
    rw [pow_zero] at hY
    have h1 : B Y ≤ B 1 := B_mono hY
    have h2 := thr_B_le_one
    push_cast
    linarith
  | succ n ih =>
    intro Y hY0 hY
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos one_lt_two
    rcases le_or_gt Y (2 ^ n) with h | h
    · have hn := ih hY0 h
      push_cast at hn ⊢
      linarith
    · have h2n : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hY2' : Y / 2 ≤ 2 ^ n := by
        rw [pow_succ] at hY
        linarith
      have hstep := B_sub_le_div_mStar (X := Y / 2) (Y := Y)
        (by linarith) (by linarith)
      have hms := mStar_lower (Y / 2)
      have hmspos : (0:ℝ) < (mStar (Y / 2) : ℝ) := by
        have h0 : (0:ℝ) < Y / 2 / Real.log 2 := div_pos (by linarith) hlog2
        linarith
      have hdiv : (Y - Y / 2) / (mStar (Y / 2) : ℝ) ≤ Real.log 2 := by
        rw [div_le_iff₀ hmspos]
        have := (div_lt_iff₀ hlog2).mp hms
        linarith
      have hih := ih (by linarith : (0:ℝ) ≤ Y / 2) hY2'
      push_cast at hih ⊢
      linarith

/-- `𝓑(Y) ≤ log Y + 2` for `Y ≥ 1` (choose `n = ⌈log Y/log 2⌉` in the
dyadic cascade; this is the paper's `𝓑(log X) ≪ log₂X`). -/
theorem thr_B_le {Y : ℝ} (hY : 1 ≤ Y) : B Y ≤ Real.log Y + 2 := by
  have hY0 : (0:ℝ) < Y := lt_of_lt_of_le one_pos hY
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos one_lt_two
  set n : ℕ := ⌈Real.log Y / Real.log 2⌉₊ with hn
  have h1 : Real.log Y ≤ n * Real.log 2 := by
    have hceil := Nat.le_ceil (Real.log Y / Real.log 2)
    calc Real.log Y = Real.log Y / Real.log 2 * Real.log 2 :=
          (div_mul_cancel₀ _ hlog2.ne').symm
      _ ≤ n * Real.log 2 := mul_le_mul_of_nonneg_right hceil hlog2.le
  have hY2 : Y ≤ 2 ^ n := by
    calc Y = Real.exp (Real.log Y) := (Real.exp_log hY0).symm
      _ ≤ Real.exp (n * Real.log 2) := Real.exp_le_exp.mpr h1
      _ = Real.exp (Real.log 2) ^ n := Real.exp_nat_mul _ n
      _ = 2 ^ n := by rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have h2 := thr_B_le_of_le_two_pow n hY0.le hY2
  have h3 : (n:ℝ) < Real.log Y / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h4 : (n:ℝ) * Real.log 2 ≤ Real.log Y + Real.log 2 := by
    have h5 := mul_le_mul_of_nonneg_right h3.le hlog2.le
    rwa [add_mul, one_mul, div_mul_cancel₀ _ hlog2.ne'] at h5
  have hlog2_lt : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  linarith

/-! ## The explicit two-sided `F` bounds (`1 ≪ F(X) ≪ log₂X`) -/

/-- Explicit form of the paper's `1 ≪ F(X)` (proof of `lem:threshold`):
`F(X) ≥ 0.34` for `X ≥ exp(exp 20)`, from `𝓑(log X) ≥ (log 2)/2` (the
`m = 1` summand) minus the averaging error. -/
theorem thr_FReal_lower {X : ℝ} (hX : Real.exp (Real.exp 20) ≤ X) :
    (0.34 : ℝ) ≤ FReal X := by
  have hX0 : (0:ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hL := thr_exp20_le_log hX
  have hL7 : (10:ℝ) ^ 7 ≤ Real.log X :=
    le_trans thr_ten_pow_seven_le_exp_twenty hL
  have hL7' : (10000000 : ℝ) ≤ Real.log X := by
    have h10 : (10:ℝ) ^ 7 = 10000000 := by norm_num
    linarith [h10 ▸ hL7]
  have hL0 : (0:ℝ) < Real.log X := by linarith
  have havg := averaging_relation (X := Real.log X) hL7
  simp only [averagingError] at havg
  rw [Real.exp_log hX0] at havg
  have hterm : BTerm (Real.log X) 0 ≤ B (Real.log X) :=
    (summable_BTerm _).le_tsum 0 fun j _ =>
      div_nonneg (le_min (g_nonneg _) hL0.le) (by positivity)
  have hB0 : BTerm (Real.log X) 0 = Real.log 2 / 2 := by
    have hle : Real.log 2 ≤ Real.log X := by
      linarith [Real.log_two_lt_d9]
    have e1 : BTerm (Real.log X) 0 = min (g 1) (Real.log X) / 2 := by
      norm_num [BTerm]
    rw [e1, thr_g_one, min_eq_left hle]
  rw [mul_div_assoc] at havg
  have habs := abs_le.mp havg
  have hterm' : Real.log 2 / 2 ≤ B (Real.log X) := hB0 ▸ hterm
  have hAle := thr_A_le hX
  have hlog2 := Real.log_two_gt_d9
  -- `F ≥ 𝓑(log X) − 7·A ≥ 0.6931/2 − 7/20000 ≥ 0.34`
  linarith [habs.1, hterm']

/-- Explicit form of the paper's `F(X) ≪ log₂X` (proof of `lem:threshold`):
`F(X) ≤ log₂X + 3` for `X ≥ exp(exp 20)`. -/
theorem thr_FReal_upper {X : ℝ} (hX : Real.exp (Real.exp 20) ≤ X) :
    FReal X ≤ Real.log (Real.log X) + 3 := by
  have hX0 : (0:ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hL := thr_exp20_le_log hX
  have hL7 : (10:ℝ) ^ 7 ≤ Real.log X :=
    le_trans thr_ten_pow_seven_le_exp_twenty hL
  have hL7' : (10000000 : ℝ) ≤ Real.log X := by
    have h10 : (10:ℝ) ^ 7 = 10000000 := by norm_num
    linarith [h10 ▸ hL7]
  have havg := averaging_relation (X := Real.log X) hL7
  simp only [averagingError] at havg
  rw [Real.exp_log hX0] at havg
  rw [mul_div_assoc] at havg
  have habs := abs_le.mp havg
  have hB := thr_B_le (Y := Real.log X) (by linarith)
  have hAle := thr_A_le hX
  -- `F ≤ 𝓑(log X) + 7·A ≤ (log₂X + 2) + 7/20000 ≤ log₂X + 3`
  linarith [habs.2]

/-! ## Slow variation of `F` across the threshold window (eq. `slow-variation`) -/

/-- The paper's eq. `slow-variation` with explicit constant: if the integer
`m` lies in the logarithmic window `log X ≤ log m ≤ log X + 2·log₂X` (which
contains the paper's `[m₀/2, 2m₀]`), then
`|F(m) − F(X)| ≤ 15·(log₂X)²/log X`.  Proof as in the paper: two
applications of the averaging relation (`prop:averaging-relation`) at the
scales `log m` and `log X`, plus the `𝓑`-increment bound from
`𝓑'(t) = 1/m_*(t) < (log 2)/t` (`lem:B-slopes`, `lem:elementary-threshold`). -/
theorem threshold_slow_variation {X : ℝ} (hX : Real.exp (Real.exp 20) ≤ X)
    {m : ℕ} (hm1 : Real.log X ≤ Real.log m)
    (hm2 : Real.log m ≤ Real.log X + 2 * Real.log (Real.log X)) :
    |FReal m - FReal X| ≤ 15 * (Real.log (Real.log X) ^ 2 / Real.log X) := by
  have hX0 : (0:ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hL := thr_exp20_le_log hX
  have hLL := thr_twenty_le_loglog hX
  have hL0 : (0:ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 20) hL
  have hLL0 : (0:ℝ) < Real.log (Real.log X) := by linarith
  have hL7 : (10:ℝ) ^ 7 ≤ Real.log X :=
    le_trans thr_ten_pow_seven_le_exp_twenty hL
  have hL7' : (10000000 : ℝ) ≤ Real.log X := by
    have h10 : (10:ℝ) ^ 7 = 10000000 := by norm_num
    linarith [h10 ▸ hL7]
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos one_lt_two
  -- `m > 1`, so `exp (log m) = m`
  have hm0' : (0:ℝ) < (m:ℝ) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exfalso
      rw [hm, Nat.cast_zero, Real.log_zero] at hm1
      linarith
    · exact_mod_cast hm
  -- averaging relation at scale `log m`
  have h1 := averaging_relation (X := Real.log m) (le_trans hL7 hm1)
  simp only [averagingError] at h1
  rw [Real.exp_log hm0'] at h1
  -- averaging relation at scale `log X`
  have h2 := averaging_relation (X := Real.log X) hL7
  simp only [averagingError] at h2
  rw [Real.exp_log hX0, mul_div_assoc] at h2
  -- the `𝓑`-increment across the window
  have hBmono : 0 ≤ B (Real.log m) - B (Real.log X) :=
    sub_nonneg.mpr (B_mono hm1)
  have hLhalf : Real.log (Real.log X) ≤ Real.log X / 2 :=
    thr_log_le_half (by linarith)
  have hBstep : B (Real.log m) - B (Real.log X)
      ≤ 0.07 * (Real.log (Real.log X) ^ 2 / Real.log X) := by
    have hdiv_pos : (0:ℝ) < Real.log X / Real.log 2 := div_pos hL0 hlog2
    have c1 : B (Real.log m) - B (Real.log X)
        ≤ (Real.log m - Real.log X) / (mStar (Real.log X) : ℝ) :=
      B_sub_le_div_mStar hL0.le hm1
    have c2 : (Real.log m - Real.log X) / (mStar (Real.log X) : ℝ)
        ≤ (Real.log m - Real.log X) / (Real.log X / Real.log 2) :=
      div_le_div_of_nonneg_left (by linarith) hdiv_pos (mStar_lower _).le
    have c3 : (Real.log m - Real.log X) / (Real.log X / Real.log 2)
        = (Real.log m - Real.log X) * Real.log 2 / Real.log X :=
      div_div_eq_mul_div _ _ _
    have c4 : (Real.log m - Real.log X) * Real.log 2 / Real.log X
        ≤ 2 * Real.log (Real.log X) * 0.7 / Real.log X := by
      apply div_le_div_of_nonneg_right ?_ hL0.le
      exact mul_le_mul (by linarith) (by linarith [Real.log_two_lt_d9])
        hlog2.le (by linarith)
    have c5 : 2 * Real.log (Real.log X) * 0.7 / Real.log X
        ≤ 0.07 * (Real.log (Real.log X) ^ 2 / Real.log X) := by
      have h5 : 2 * Real.log (Real.log X) * 0.7
          ≤ 0.07 * Real.log (Real.log X) ^ 2 := by nlinarith
      calc 2 * Real.log (Real.log X) * 0.7 / Real.log X
          ≤ 0.07 * Real.log (Real.log X) ^ 2 / Real.log X :=
            div_le_div_of_nonneg_right h5 hL0.le
        _ = 0.07 * (Real.log (Real.log X) ^ 2 / Real.log X) := by ring
    linarith
  -- the double logarithm across the window
  have hloglogm_ub : Real.log (Real.log m) ≤ 1.04 * Real.log (Real.log X) := by
    have h2L : Real.log m ≤ 2 * Real.log X := by linarith
    calc Real.log (Real.log m) ≤ Real.log (2 * Real.log X) :=
          Real.log_le_log (lt_of_lt_of_le hL0 hm1) h2L
      _ = Real.log 2 + Real.log (Real.log X) :=
          Real.log_mul (by norm_num) hL0.ne'
      _ ≤ 1.04 * Real.log (Real.log X) := by
          linarith [Real.log_two_lt_d9]
  have hloglogm_lb : 0 ≤ Real.log (Real.log m) :=
    Real.log_nonneg (by linarith)
  have hsq : Real.log (Real.log m) ^ 2
      ≤ 1.0816 * Real.log (Real.log X) ^ 2 := by
    calc Real.log (Real.log m) ^ 2 ≤ (1.04 * Real.log (Real.log X)) ^ 2 :=
          pow_le_pow_left₀ hloglogm_lb hloglogm_ub 2
      _ = 1.0816 * Real.log (Real.log X) ^ 2 := by ring
  have hb1 : 7 * Real.log (Real.log m) ^ 2 / Real.log m
      ≤ 7.5712 * (Real.log (Real.log X) ^ 2 / Real.log X) := by
    have hnum : 7 * Real.log (Real.log m) ^ 2
        ≤ 7 * (1.0816 * Real.log (Real.log X) ^ 2) := by linarith
    calc 7 * Real.log (Real.log m) ^ 2 / Real.log m
        ≤ 7 * (1.0816 * Real.log (Real.log X) ^ 2) / Real.log m :=
          div_le_div_of_nonneg_right hnum (by linarith)
      _ ≤ 7 * (1.0816 * Real.log (Real.log X) ^ 2) / Real.log X :=
          div_le_div_of_nonneg_left (by positivity) hL0 hm1
      _ = 7.5712 * (Real.log (Real.log X) ^ 2 / Real.log X) := by ring
  -- combine via the triangle inequality
  have htri1 := abs_sub_le (FReal m) (B (Real.log m)) (FReal X)
  have htri2 := abs_sub_le (B (Real.log m)) (B (Real.log X)) (FReal X)
  have habs1 := le_trans h1 hb1
  have hBabs : |B (Real.log m) - B (Real.log X)|
      ≤ 0.07 * (Real.log (Real.log X) ^ 2 / Real.log X) := by
    rw [abs_of_nonneg hBmono]
    exact hBstep
  have h2' : |B (Real.log X) - FReal X|
      ≤ 7 * (Real.log (Real.log X) ^ 2 / Real.log X) := by
    rw [abs_sub_comm]
    exact h2
  have hApos : (0:ℝ) ≤ Real.log (Real.log X) ^ 2 / Real.log X := by positivity
  linarith

/-! ## Bookkeeping: `g` versus `F` on integer arguments -/

/-- On a positive integer argument, `m·F(m) = log m · g(m)` (unfolding
`F(m) = (log m/m)·g(m)`). -/
theorem thr_natCast_mul_FReal {m : ℕ} (hm : 0 < m) :
    (m:ℝ) * FReal m = Real.log m * g m := by
  have hm0 : ((m:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [FReal, Nat.floor_natCast]
  field_simp

/-! ## The threshold estimate, additive form (paper eq. `threshold-additive`) -/

set_option maxHeartbeats 1600000 in
/-- Paper `lem:threshold`, eq. `threshold-additive`, explicit form: for
`X ≥ exp(exp 20)`,
```
|X·log X/m_*(X) − F(X)| ≤ 100·(log₂X)²/log X.
```
(The paper's statement is asymptotic; the explicit threshold `exp(exp 20)`
and constant `100` are what the argument yields with the explicit inputs
`averaging_relation` (constant 7, threshold `10⁷`) and
`m_*(t) > t/log 2`.)

Proof as in the paper: with `m₀ = X·log X/F(X)` and `ε = 45·A_X/F(X)`
(where `A_X = (log₂X)²/log X`), the slow-variation estimate shows
`g(⌊m₀(1−ε)⌋) ≤ X < g(⌈m₀(1+ε)⌉)`, so `m_*(X)` is bracketed between these
two integers, and the relative bracket converts into the additive bound.
(The proof is one long chain of explicit estimates; it needs a raised
heartbeat budget, which affects elaboration effort only, not soundness.) -/
theorem threshold_additive {X : ℝ} (hX : Real.exp (Real.exp 20) ≤ X) :
    |X * Real.log X / (mStar X : ℝ) - FReal X|
      ≤ 100 * (Real.log (Real.log X) ^ 2 / Real.log X) := by
  have hX0 : (0:ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hL := thr_exp20_le_log hX
  have hLL := thr_twenty_le_loglog hX
  have hL0 : (0:ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 20) hL
  have hLL0 : (0:ℝ) < Real.log (Real.log X) := by linarith
  have hL7 : (10:ℝ) ^ 7 ≤ Real.log X :=
    le_trans thr_ten_pow_seven_le_exp_twenty hL
  have hL7' : (10000000 : ℝ) ≤ Real.log X := by
    have h10 : (10:ℝ) ^ 7 = 10000000 := by norm_num
    linarith [h10 ▸ hL7]
  have hX2 : (2:ℝ) ≤ X := by
    have h1 := Real.add_one_le_exp (Real.exp 20)
    have h2 := thr_ten_pow_seven_le_exp_twenty
    have h10 : (10:ℝ) ^ 7 = 10000000 := by norm_num
    linarith [h10 ▸ h2]
  have hA0 : (0:ℝ) < Real.log (Real.log X) ^ 2 / Real.log X :=
    div_pos (pow_pos hLL0 2) hL0
  have hAle := thr_A_le hX
  have hFlo := thr_FReal_lower hX
  have hFhi := thr_FReal_upper hX
  have hF0 : (0:ℝ) < FReal X := by linarith
  have hlog2_lt : Real.log 2 < 0.7 := by linarith [Real.log_two_lt_d9]
  -- bounds on `log F(X)`
  have hlogF_lb : (-2 : ℝ) ≤ Real.log (FReal X) := by
    have h13 : Real.log ((3:ℝ)⁻¹) ≤ Real.log (FReal X) :=
      Real.log_le_log (by norm_num) (by linarith)
    have h3 : Real.log 3 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      linarith [two_mul_le_exp (by norm_num : (0:ℝ) ≤ 2)]
    rw [Real.log_inv] at h13
    linarith
  have hlogF_ub : Real.log (FReal X) ≤ Real.log (Real.log X) - 0.7 := by
    have hup : Real.log (FReal X) ≤ Real.log (2 * Real.log (Real.log X)) :=
      Real.log_le_log hF0 (by linarith)
    rw [Real.log_mul (by norm_num) hLL0.ne'] at hup
    have hhalf : Real.log (Real.log (Real.log X)) ≤ Real.log (Real.log X) / 2 :=
      thr_log_le_half (by linarith)
    linarith
  -- the center `m₀ = X·log X/F(X)`
  set m0 : ℝ := X * Real.log X / FReal X with hm0def
  have hm0F : m0 * FReal X = X * Real.log X := by
    rw [hm0def]
    exact div_mul_cancel₀ _ hF0.ne'
  have hm0_pos : (0:ℝ) < m0 := by
    rw [hm0def]
    exact div_pos (mul_pos hX0 hL0) hF0
  have hXm0 : X ≤ m0 := by
    rw [hm0def, le_div_iff₀ hF0]
    have hLhalf : Real.log (Real.log X) ≤ Real.log X / 2 :=
      thr_log_le_half (by linarith)
    have hFL : FReal X ≤ Real.log X := by linarith
    exact mul_le_mul_of_nonneg_left hFL hX0.le
  have hlogm0 : Real.log m0
      = Real.log X + Real.log (Real.log X) - Real.log (FReal X) := by
    rw [hm0def, Real.log_div (mul_pos hX0 hL0).ne' hF0.ne',
      Real.log_mul hX0.ne' hL0.ne']
  have hm0A : m0 * (Real.log (Real.log X) ^ 2 / Real.log X)
      = X * Real.log (Real.log X) ^ 2 / FReal X := by
    have hF0' : FReal X ≠ 0 := hF0.ne'
    have hL0' : Real.log X ≠ 0 := hL0.ne'
    rw [hm0def]
    field_simp
  -- the relative half-width `ε = 45·A/F`
  set ε : ℝ := 45 * (Real.log (Real.log X) ^ 2 / Real.log X) / FReal X
    with hεdef
  have hεF : ε * FReal X = 45 * (Real.log (Real.log X) ^ 2 / Real.log X) := by
    rw [hεdef]
    exact div_mul_cancel₀ _ hF0.ne'
  have hε0 : (0:ℝ) < ε := by
    rw [hεdef]
    exact div_pos (mul_pos (by norm_num) hA0) hF0
  have hε_ub : ε ≤ 0.01 := by
    rw [hεdef, div_le_iff₀ hF0]
    linarith
  have hεA : ε * (Real.log (Real.log X) ^ 2 / Real.log X)
      ≤ 0.01 * (Real.log (Real.log X) ^ 2 / Real.log X) :=
    mul_le_mul_of_nonneg_right hε_ub hA0.le
  -- absorb integer rounding: `m₀·ε ≥ 1`
  have hF2 : FReal X ^ 2 ≤ 4 * Real.log (Real.log X) ^ 2 := by
    nlinarith [mul_nonneg
      (by linarith : (0:ℝ) ≤ 2 * Real.log (Real.log X) - FReal X)
      (by linarith : (0:ℝ) ≤ 2 * Real.log (Real.log X) + FReal X)]
  have hm0ε_nn : (0:ℝ) ≤ m0 * ε := mul_nonneg hm0_pos.le hε0.le
  have hm0ε_ub : m0 * ε ≤ m0 * 0.01 :=
    mul_le_mul_of_nonneg_left hε_ub hm0_pos.le
  have hm0A_nn : (0:ℝ)
      ≤ m0 * (Real.log (Real.log X) ^ 2 / Real.log X) :=
    mul_nonneg hm0_pos.le hA0.le
  have hm0εA : m0 * (ε * (Real.log (Real.log X) ^ 2 / Real.log X))
      ≤ m0 * (0.01 * (Real.log (Real.log X) ^ 2 / Real.log X)) :=
    mul_le_mul_of_nonneg_left hεA hm0_pos.le
  have hm0εA_nn : (0:ℝ)
      ≤ m0 * (ε * (Real.log (Real.log X) ^ 2 / Real.log X)) :=
    mul_nonneg hm0_pos.le (mul_nonneg hε0.le hA0.le)
  have hm0εF : m0 * (ε * FReal X)
      = m0 * (45 * (Real.log (Real.log X) ^ 2 / Real.log X)) := by
    rw [hεF]
  have h_one_le : (1:ℝ) ≤ m0 * ε := by
    have hF0' : FReal X ≠ 0 := hF0.ne'
    have hL0' : Real.log X ≠ 0 := hL0.ne'
    have h1 : m0 * ε
        = 45 * (X * Real.log (Real.log X) ^ 2) / FReal X ^ 2 := by
      rw [hm0def, hεdef]
      field_simp
    rw [h1, le_div_iff₀ (pow_pos hF0 2), one_mul]
    linarith [hF2, mul_nonneg (by linarith : (0:ℝ) ≤ 45 * X - 4)
      (sq_nonneg (Real.log (Real.log X)))]
  -- the upper bracket integer `⌈m₀(1+ε)⌉`
  set mPlus : ℕ := ⌈m0 * (1 + ε)⌉₊ with hmPdef
  have hP_lb : m0 * (1 + ε) ≤ (mPlus : ℝ) := Nat.le_ceil _
  have hP_ub : (mPlus : ℝ) ≤ m0 * (1 + 2 * ε) := by
    have h := Nat.ceil_lt_add_one
      (mul_nonneg hm0_pos.le (by linarith : (0:ℝ) ≤ 1 + ε))
    rw [← hmPdef] at h
    linarith [h_one_le]
  have hP_pos : (0:ℝ) < (mPlus : ℝ) :=
    lt_of_lt_of_le (mul_pos hm0_pos (by linarith : (0:ℝ) < 1 + ε)) hP_lb
  have hmPlus_pos : 0 < mPlus := by exact_mod_cast hP_pos
  have hXP : X ≤ (mPlus : ℝ) :=
    le_trans hXm0 (le_trans (by linarith : m0 ≤ m0 * (1 + ε)) hP_lb)
  have hlogP_lb : Real.log X ≤ Real.log mPlus := Real.log_le_log hX0 hXP
  have hlogP_ub : Real.log mPlus
      ≤ Real.log X + 2 * Real.log (Real.log X) := by
    have h2m0 : (mPlus : ℝ) ≤ 2 * m0 := by linarith [hm0ε_ub, hP_ub]
    have h := Real.log_le_log hP_pos h2m0
    rw [Real.log_mul (by norm_num) hm0_pos.ne', hlogm0] at h
    linarith
  have hSVP := abs_le.mp (threshold_slow_variation hX hlogP_lb hlogP_ub)
  have hgP : (mPlus:ℝ) * FReal mPlus = Real.log mPlus * g mPlus :=
    thr_natCast_mul_FReal hmPlus_pos
  have hF15 : (0:ℝ)
      ≤ FReal X - 15 * (Real.log (Real.log X) ^ 2 / Real.log X) := by
    linarith
  -- `X < g(mPlus)`
  have hU1 : X < g mPlus := by
    have hlogP0 : (0:ℝ) < Real.log mPlus := lt_of_lt_of_le hL0 hlogP_lb
    have s1 : X * Real.log mPlus
        ≤ X * (Real.log X + 2 * Real.log (Real.log X)) :=
      mul_le_mul_of_nonneg_left hlogP_ub hX0.le
    have t1 : 2 * (X * Real.log (Real.log X)) * FReal X
        ≤ 2.3 * (X * Real.log (Real.log X) ^ 2) := by
      have hfac : (0:ℝ) ≤ 2.3 * Real.log (Real.log X) - 2 * FReal X := by
        linarith
      linarith [mul_nonneg (mul_nonneg hX0.le hLL0.le) hfac]
    have t2 : 2 * (X * Real.log (Real.log X))
        ≤ 2.3 * (m0 * (Real.log (Real.log X) ^ 2 / Real.log X)) := by
      rw [hm0A]
      rw [show 2.3 * (X * Real.log (Real.log X) ^ 2 / FReal X)
          = 2.3 * (X * Real.log (Real.log X) ^ 2) / FReal X by ring,
        le_div_iff₀ hF0]
      exact t1
    have s2 : X * (Real.log X + 2 * Real.log (Real.log X))
        ≤ m0 * FReal X
          + 2.3 * (m0 * (Real.log (Real.log X) ^ 2 / Real.log X)) := by
      linarith [hm0F, t2]
    have score : FReal X + 2.3 * (Real.log (Real.log X) ^ 2 / Real.log X)
        < (1 + ε) * (FReal X
            - 15 * (Real.log (Real.log X) ^ 2 / Real.log X)) := by
      linarith [hεF, hεA, hA0]
    have lift := mul_lt_mul_of_pos_left score hm0_pos
    have hmul : m0 * ((1 + ε) * (FReal X
          - 15 * (Real.log (Real.log X) ^ 2 / Real.log X)))
        ≤ (mPlus:ℝ) * FReal mPlus := by
      rw [show m0 * ((1 + ε) * (FReal X
          - 15 * (Real.log (Real.log X) ^ 2 / Real.log X)))
          = (m0 * (1 + ε)) * (FReal X
              - 15 * (Real.log (Real.log X) ^ 2 / Real.log X)) by ring]
      exact mul_le_mul hP_lb (by linarith [hSVP.1]) hF15 hP_pos.le
    have s4 : X * Real.log mPlus < (mPlus:ℝ) * FReal mPlus := by
      linarith [s1, s2, lift, hmul]
    rw [hgP] at s4
    rw [mul_comm X (Real.log (mPlus:ℝ))] at s4
    exact lt_of_mul_lt_mul_left s4 hlogP0.le
  -- the lower bracket integer `⌊m₀(1−ε)⌋`
  set mMinus : ℕ := ⌊m0 * (1 - ε)⌋₊ with hmMdef
  have hM_ub : (mMinus : ℝ) ≤ m0 * (1 - ε) :=
    Nat.floor_le (mul_nonneg hm0_pos.le (by linarith : (0:ℝ) ≤ 1 - ε))
  have hM_lb : m0 * (1 - 2 * ε) ≤ (mMinus : ℝ) := by
    have h := Nat.lt_floor_add_one (m0 * (1 - ε))
    rw [← hmMdef] at h
    linarith [h_one_le]
  have hM_pos : (0:ℝ) < (mMinus : ℝ) := by
    linarith [hM_lb, hm0ε_ub, hm0_pos]
  have hmMinus_pos : 0 < mMinus := by exact_mod_cast hM_pos
  have hM_half : m0 / 2 ≤ (mMinus : ℝ) := by
    linarith [hM_lb, hm0ε_ub, hm0_pos]
  have hlogM_lb : Real.log X ≤ Real.log mMinus := by
    have h1 : Real.log (m0 / 2) ≤ Real.log mMinus :=
      Real.log_le_log (by positivity) hM_half
    rw [Real.log_div hm0_pos.ne' (by norm_num), hlogm0] at h1
    linarith
  have hlogM_ub : Real.log mMinus
      ≤ Real.log X + 2 * Real.log (Real.log X) := by
    have h1 : Real.log mMinus ≤ Real.log m0 :=
      Real.log_le_log hM_pos (le_trans hM_ub (by linarith))
    rw [hlogm0] at h1
    linarith
  have hSVM := abs_le.mp (threshold_slow_variation hX hlogM_lb hlogM_ub)
  have hgM : (mMinus:ℝ) * FReal mMinus = Real.log mMinus * g mMinus :=
    thr_natCast_mul_FReal hmMinus_pos
  -- `g(mMinus) ≤ X`
  have hL1 : g mMinus ≤ X := by
    have hlogM0 : (0:ℝ) < Real.log mMinus := lt_of_lt_of_le hL0 hlogM_lb
    have c1 : (mMinus:ℝ) * FReal mMinus
        ≤ (m0 * (1 - ε)) * (FReal X
            + 15 * (Real.log (Real.log X) ^ 2 / Real.log X)) :=
      mul_le_mul hM_ub (by linarith [hSVM.2]) (by linarith [hSVM.1])
        (mul_nonneg hm0_pos.le (by linarith : (0:ℝ) ≤ 1 - ε))
    have c2 : (m0 * (1 - ε)) * (FReal X
          + 15 * (Real.log (Real.log X) ^ 2 / Real.log X))
        ≤ m0 * FReal X := by
      linarith [hm0εF, hm0εA_nn, hm0A_nn]
    have c3 : m0 * FReal X ≤ Real.log mMinus * X := by
      rw [hm0F]
      linarith [mul_nonneg (sub_nonneg.mpr hlogM_lb) hX0.le]
    have key : Real.log mMinus * g mMinus ≤ Real.log mMinus * X := by
      rw [← hgM]
      linarith
    exact le_of_mul_le_mul_left key hlogM0
  -- bracket `m_*(X)` between the two integers
  have hml : mMinus < mStar X := lt_mStar_iff.mpr hL1
  have hmh : mStar X ≤ mPlus := mStar_le_of_lt_g hU1
  have hs_lb : m0 * (1 - ε) ≤ (mStar X : ℝ) := by
    have h1 : m0 * (1 - ε) < (mMinus:ℝ) + 1 := by
      have h := Nat.lt_floor_add_one (m0 * (1 - ε))
      rw [← hmMdef] at h
      exact_mod_cast h
    have h2 : (mMinus:ℝ) + 1 ≤ (mStar X : ℝ) := by exact_mod_cast hml
    linarith
  have hs_ub : (mStar X : ℝ) ≤ m0 * (1 + 2 * ε) :=
    le_trans (by exact_mod_cast hmh) hP_ub
  have hs0 : (0:ℝ) < (mStar X : ℝ) :=
    lt_of_lt_of_le
      (mul_pos hm0_pos (by linarith : (0:ℝ) < 1 - ε)) hs_lb
  -- convert the bracket into the additive bound
  have hup : X * Real.log X / (mStar X : ℝ)
      ≤ FReal X + 100 * (Real.log (Real.log X) ^ 2 / Real.log X) := by
    rw [div_le_iff₀ hs0]
    have h1 : m0 * FReal X
        ≤ (FReal X + 100 * (Real.log (Real.log X) ^ 2 / Real.log X))
            * (m0 * (1 - ε)) := by
      linarith [hm0εF, hm0εA, hm0A_nn]
    have h2 : (FReal X + 100 * (Real.log (Real.log X) ^ 2 / Real.log X))
          * (m0 * (1 - ε))
        ≤ (FReal X + 100 * (Real.log (Real.log X) ^ 2 / Real.log X))
            * (mStar X : ℝ) :=
      mul_le_mul_of_nonneg_left hs_lb (by linarith)
    linarith [hm0F]
  have hdown : FReal X - 100 * (Real.log (Real.log X) ^ 2 / Real.log X)
      ≤ X * Real.log X / (mStar X : ℝ) := by
    rw [le_div_iff₀ hs0]
    have hcase : (FReal X
          - 100 * (Real.log (Real.log X) ^ 2 / Real.log X))
          * (mStar X : ℝ) ≤ m0 * FReal X := by
      rcases le_or_gt
        (FReal X - 100 * (Real.log (Real.log X) ^ 2 / Real.log X)) 0
        with hneg | hpos'
      · linarith [mul_pos hm0_pos hF0,
          mul_nonneg (neg_nonneg.mpr hneg) hs0.le]
      · have c1 : (FReal X
              - 100 * (Real.log (Real.log X) ^ 2 / Real.log X))
              * (mStar X : ℝ)
            ≤ (FReal X
                - 100 * (Real.log (Real.log X) ^ 2 / Real.log X))
                * (m0 * (1 + 2 * ε)) :=
          mul_le_mul_of_nonneg_left hs_ub hpos'.le
        have c2 : (FReal X
              - 100 * (Real.log (Real.log X) ^ 2 / Real.log X))
              * (m0 * (1 + 2 * ε)) ≤ m0 * FReal X := by
          linarith [hm0εF, hm0A_nn, hm0εA_nn]
        linarith
    linarith [hm0F]
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-! ## The recurrence-error bound (paper eq. `rho-small`, `lem:exact-recurrence`) -/

/-- Paper eq. `rho-small` of `lem:exact-recurrence`, explicit form: for
depth `r ≥ 5` and phase `u ∈ [1, e]`,
```
|ρ_r(u)| ≤ 107·E_{r-2}(u)²/E_{r-1}(u).
```
Proof as in the paper: apply `lem:threshold` (`threshold_additive`) at
`X = E_r(u)` (so `log X = E_{r-1}(u)`, `log₂X = E_{r-2}(u)`) and
`prop:averaging-relation` (`averaging_relation`) at the averaging variable
`E_{r-1}(u)`; the two errors add to `(100 + 7)·E_{r-2}²/E_{r-1}`.
The paper asserts the bound "as `r → ∞`"; here `r ≥ 5` suffices because
`E_{r-2}(u) ≥ E₃(1) > 3.8·10⁶` puts both applications far above their
explicit thresholds. -/
theorem rhoDepth_abs_le {r : ℕ} (hr : 5 ≤ r) {u : ℝ}
    (hu : u ∈ Set.Icc (1:ℝ) (Real.exp 1)) :
    |rhoDepth r u| ≤ 107 * (E (r - 2) u ^ 2 / E (r - 1) u) := by
  have hu1 : (1:ℝ) ≤ u := hu.1
  -- tower size facts
  have hE2 : (3.8e6 : ℝ) < E (r - 2) u := by
    have h1 : E 3 1 ≤ E (r - 2) 1 :=
      E_mono_depth le_rfl (by omega : 3 ≤ r - 2)
    have h2 : E (r - 2) 1 ≤ E (r - 2) u := E_mono (r - 2) hu1
    linarith [E_three_one_gt]
  have hEr1 : E (r - 1) u = Real.exp (E (r - 2) u) := by
    have h := E_succ (r - 2) u
    rwa [show r - 2 + 1 = r - 1 by omega] at h
  have hEr : E r u = Real.exp (E (r - 1) u) := by
    have h := E_succ (r - 1) u
    rwa [show r - 1 + 1 = r by omega] at h
  have hlogEr1 : Real.log (E (r - 1) u) = E (r - 2) u := by
    rw [hEr1, Real.log_exp]
  have hlogEr : Real.log (E r u) = E (r - 1) u := by
    rw [hEr, Real.log_exp]
  -- `E_r(u)` is above the threshold of `threshold_additive`
  have hXbig : Real.exp (Real.exp 20) ≤ E r u := by
    rw [hEr]
    apply Real.exp_le_exp.mpr
    rw [hEr1]
    exact Real.exp_le_exp.mpr (by linarith)
  have h1 := threshold_additive hXbig
  rw [hlogEr, hlogEr1] at h1
  -- `E_{r-1}(u)` is above the threshold of `averaging_relation`
  have hbig2 : (10:ℝ) ^ 7 ≤ E (r - 1) u := by
    rw [hEr1]
    have h := pow_div_factorial_le_exp (x := E (r - 2) u) (by linarith) 2
    have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [hfac] at h
    nlinarith [hE2, sq_nonneg (E (r - 2) u - 3.8e6)]
  have h2 := averaging_relation hbig2
  simp only [averagingError] at h2
  rw [← hEr, hlogEr1, mul_div_assoc] at h2
  -- combine
  rw [rhoDepth_eq (by omega : 1 ≤ r)]
  have htri := abs_sub_le (E r u * E (r - 1) u / (mStar (E r u) : ℝ))
    (FReal (E r u)) (B (E (r - 1) u))
  linarith [h1, h2, htri]

end Erdos320
