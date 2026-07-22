import Erdos320.Lemmas.ShellDecomposition
import Erdos320.Lemmas.CollisionLower
import Erdos320.Lemmas.LogSumBounds
import Erdos320.Lemmas.ExpFloor
import Erdos320.Lemmas.BSlopes
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Explicit low-interval averaging error (`lem:explicit-low-averaging`)

The manuscript's Lemma "Explicit low-interval averaging error": for
`9 700 000 ≤ X ≤ 10 700 000`,
```
-1.03·10⁻⁵ < 𝓡(X) < 1.19·10⁻⁵,     |𝓡(X)| < 1.20·10⁻⁵     (eq. explicit-low-averaging)
```
where `𝓡(X) = F(e^X) − 𝓑(X)` is the averaging-relation error
(`Erdos320.averagingError`).  Main results:

* `explicit_low_averaging_upper` : `𝓡(X) < 1.19·10⁻⁵`;
* `explicit_low_averaging_lower` : `-1.03·10⁻⁵ < 𝓡(X)`;
* `explicit_low_averaging` : `|𝓡(X)| < 1.2·10⁻⁵` (the form the certificate
  ledger consumes).

The proof tracks the paper's (proof of `lem:explicit-low-averaging`,
`sec:certificates`): with `N = ⌊e^X⌋`, `M = ⌊X^2.05⌋`, `Q = ⌊N/(M+1)⌋`, the
shell decomposition (`g_shell_decomposition`) writes `g(N)` as the sum over
shells `1 ≤ m ≤ M` of `∑_{p ∈ shell m} log σ_p(m)` up to the fibre cost
(eq. `explicit-core`, `< 10⁻⁷` after normalization).  Per shell, the FKS
prime-interval count (eq. `explicit-shell-count`, via `primeInterval_upper` /
`primeInterval_lower` with the astronomically small error
`fksError_le_tiny`) and the cap comparison between `min(g(m), log(N/m))` and
`min(g(m), X)` give the upper side, split at `T = ⌊(X−36)/log 2⌋` into the
`a_m ≤ m log 2` head (paper's `< 1.042·10⁻⁵`; here `≤ 1.041·10⁻⁵`) and the
`a_m ≤ X` tail (paper's `< 1.287·10⁻⁶`; here `≤ 1.30·10⁻⁶`).  The lower side
uses the shellwise collision bound (`shell_collision_lower`) with the
multiplicity `b_m` of eq. `explicit-bm`, the `a*_m = min(m log 2, X)` deficit
transfer of eq. `explicit-collision`, and the split at `A = ⌊X/(2 log 2)⌋`
(the paper's `T₊/2`): below `A` the deficit carries `e^{a*_m−X} ≤ e^{−X/2}`
and is beyond negligible; above `A` an integral comparison bounds the total
deficit by `7.7·10⁻⁶`.

**Deviations from the paper's displayed constants (all on the
safe side).**  (a) The paper's transition-range bookkeeping (`k = T₊ − m`,
geometric estimate `< 3·10⁻¹⁰`) is merged here into the above-`A` regime,
giving the single amply-budgeted total `7.7·10⁻⁶` in place of the
paper's `1.018·10⁻⁵ + 3·10⁻¹⁰ + 10⁻¹⁰⁰⁰`-style sum; the final enclosure
`(−1.03·10⁻⁵, 1.19·10⁻⁵)` is unchanged.  (b) All `10⁻¹⁰⁰⁰`-scale allowances
of the paper are realized as `10⁻⁸`-scale allowances (still with dozens of
orders of magnitude of slack), backed by `fksError_le_tiny` (`𝓔(t) ≤
t/10¹⁰⁰`).  (c) The head split uses `T = ⌊(X−36)/log 2⌋` (paper: `⌊X/log 2⌋`)
so that `m ≤ T` forces the clamped case outright; the head constant is
unaffected (`log(T+1) < 17` either way).

This file is deliberately self-contained on its window `X ∈ [9.7·10⁶,
1.07·10⁷]`; all auxiliary declarations are prefixed `low`/`low_` to keep them
from clashing with the asymptotic averaging development (which works with
`M = ⌊X³⌋` at a different scale).
-/

namespace Erdos320

/-! ## The window's derived parameters

Paper notation (proof of `lem:explicit-low-averaging`): `N = ⌊e^X⌋`,
`M = ⌊X^2.05⌋`, and the two split indices: `T` for the upper estimate
(paper: `T = ⌊X/log 2⌋`; here shifted to `⌊(X−36)/log 2⌋`, see the module
docstring) and `A` for the lower estimate (the paper's `T₊/2`). -/

/-- `N = ⌊e^X⌋` (proof of `lem:explicit-low-averaging`). -/
noncomputable def lowN (X : ℝ) : ℕ := ⌊Real.exp X⌋₊

/-- `M = ⌊X^2.05⌋`, the shell cutoff of `lem:explicit-low-averaging`. -/
noncomputable def lowM (X : ℝ) : ℕ := ⌊X ^ (2.05 : ℝ)⌋₊

/-- The upper-estimate split index, `T = ⌊(X−36)/log 2⌋`: for `m ≤ T` the
shell is clamped (`g(m) ≤ m log 2 ≤ X − 36 ≤ log(N/(m+1))`). -/
noncomputable def lowT (X : ℝ) : ℕ := ⌊(X - 36) / Real.log 2⌋₊

/-- The lower-estimate split index, `A = ⌊X/(2 log 2)⌋` (the paper's
`T₊/2`): for `m ≤ A` the collision deficit carries `e^{a*_m − X} ≤ e^{−X/2}`. -/
noncomputable def lowA (X : ℝ) : ℕ := ⌊X / (2 * Real.log 2)⌋₊

/-- The collision multiplicity `b_m` of eq. `explicit-bm`: any integer at
least `log(L_m·H_m)/log(N/(m+1))`; we take the explicit ceiling of the
available bound `log(L_m H_m) ≤ (log 4)m + √m·log m + log(1+log m)`
(`log_lcm_mul_harmonicSum_le`) over the denominator bound `X − 36`. -/
noncomputable def lowCollisionMult (X : ℝ) (m : ℕ) : ℕ :=
  ⌊(Real.log 4 * m + Real.sqrt m * Real.log m + Real.log (1 + Real.log m))
      / (X - 36)⌋₊ + 1

/-! ## Generic elementary helpers -/

/-- `e^x ≤ 1/(1−x)` for `x < 1` (from `1 − x ≤ e^{−x}`). -/
theorem low_exp_le_inv_one_sub {x : ℝ} (hx : x < 1) :
    Real.exp x ≤ 1 / (1 - x) := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : 0 < 1 - x := by linarith
  rw [le_div_iff₀ h2]
  calc Real.exp x * (1 - x) ≤ Real.exp x * Real.exp (-x) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos x).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- Tangent-line bound for `log` at `c`: `log y ≤ log c + (y−c)/c`. -/
theorem low_log_le_add_div {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    Real.log y ≤ Real.log c + (y - c) / c := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < y / c by positivity)
  rw [Real.log_div hy.ne' hc.ne'] at h
  have hrw : y / c - 1 = (y - c) / c := by field_simp
  rw [hrw] at h
  linarith

/-- `(2.7182818283)^n ≤ e^n`, the workhorse for explicit lower bounds on
integer powers of `e`. -/
theorem low_exp_nat_lb (n : ℕ) : (2.7182818283 : ℝ) ^ n ≤ Real.exp n :=
  calc (2.7182818283 : ℝ) ^ n ≤ Real.exp 1 ^ n :=
        pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n
    _ = Real.exp n := Real.exp_one_pow n

/-- `e^n ≤ (2.7182818286)^n`, the matching explicit upper bound. -/
theorem low_exp_nat_ub (n : ℕ) : Real.exp n ≤ (2.7182818286 : ℝ) ^ n :=
  calc Real.exp n = Real.exp 1 ^ n := (Real.exp_one_pow n).symm
    _ ≤ (2.7182818286 : ℝ) ^ n :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n

/-- `√y · log y ≤ 0.01·y` once `y ≥ 4·10⁶` (i.e. `√y ≥ 2000`); used to absorb
the `√m log m` layer of `log L_m` into the `(log 4)m` term in the collision
multiplicity bound (eq. `explicit-bm`). -/
theorem low_sqrt_mul_log_le {y : ℝ} (hy : (4 * 10 ^ 6 : ℝ) ≤ y) :
    Real.sqrt y * Real.log y ≤ 0.01 * y := by
  have hy0 : (0:ℝ) < y := by linarith
  have hs2000 : (2000:ℝ) ≤ Real.sqrt y := by
    have h : (2000:ℝ) = Real.sqrt (2000 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    rw [h]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs0 : (0:ℝ) < Real.sqrt y := by linarith
  have hlog2000 : Real.log 2000 ≤ 7.7 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h7 : (2.7182818283:ℝ) ^ (7:ℕ) ≤ Real.exp 7 := by
      have := low_exp_nat_lb 7
      norm_num at this ⊢
      linarith
    have h07 : (1.945:ℝ) ≤ Real.exp 0.7 := by
      nlinarith [Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.7 by norm_num)]
    calc (2000:ℝ) ≤ 2.7182818283 ^ (7:ℕ) * 1.945 := by norm_num
      _ ≤ Real.exp 7 * Real.exp 0.7 :=
          mul_le_mul h7 h07 (by norm_num) (Real.exp_pos 7).le
      _ = Real.exp 7.7 := by rw [← Real.exp_add]; norm_num
  have hlogs : Real.log (Real.sqrt y) ≤ 0.005 * Real.sqrt y := by
    have h := low_log_le_add_div (show (0:ℝ) < 2000 by norm_num) hs0
    nlinarith [hs2000]
  have hlogy : Real.log y = 2 * Real.log (Real.sqrt y) := by
    rw [Real.log_sqrt hy0.le]; ring
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  nlinarith [mul_le_mul_of_nonneg_left hlogs (by positivity : (0:ℝ) ≤ 2 * Real.sqrt y)]

/-- Free cap transport downward: for `0 < Y ≤ X` and `c ≥ 0`,
`min(c, X) ≤ (X/Y)·min(c, Y)` — the "the positive term dominates … since
`(λ/Y_m⁺)c_m ≥ min(g_m, λ)`" step of the paper's lower estimate. -/
theorem low_cap_transport_free {c Xv Y : ℝ} (hY : 0 < Y) (hYX : Y ≤ Xv)
    (hc : 0 ≤ c) : min c Xv ≤ Xv / Y * min c Y := by
  have hXv : 0 < Xv := lt_of_lt_of_le hY hYX
  rcases le_or_gt c Y with h | h
  · rw [min_eq_left h, min_eq_left (h.trans hYX)]
    have h1 : 1 ≤ Xv / Y := (one_le_div hY).mpr hYX
    nlinarith
  · rw [min_eq_right h.le, div_mul_cancel₀ _ hY.ne']
    exact min_le_right c Xv

/-- The `a*_m = min(m log 2, X)` deficit transfer of eq. `explicit-collision`:
for `log S ≤ c₁` and `Y ≤ c₂`, the capped collision bound
`min(log S, Y) − log(1 + b·e^{min c₁ c₂}/P)` is at most the exact one
`log S − log(1 + b(S−1)/P)`, so capping `log S` at `Y` and replacing `S − 1`
by `e^{min c₁ c₂}` only lowers the lower estimate.  (Paper: "For `g(m) ≤ X`
this is immediate.  If `g(m) > X`, then … which gives the claim because
`e^{X−g(m)} < 1`.") -/
theorem low_deficit_transfer {P bR S Y c₁ c₂ : ℝ} (hP : 0 < P) (hS : 1 ≤ S)
    (hb : 0 ≤ bR) (hgc : Real.log S ≤ c₁) (hYc : Y ≤ c₂) :
    min (Real.log S) Y - Real.log (1 + bR * Real.exp (min c₁ c₂) / P)
      ≤ Real.log S - Real.log (1 + bR * (S - 1) / P) := by
  have hS0 : (0:ℝ) < S := by linarith
  have hu0 : (0:ℝ) < 1 + bR * (S - 1) / P := by
    have : 0 ≤ bR * (S - 1) / P := by positivity
    linarith
  have hv0 : (0:ℝ) < 1 + bR * Real.exp (min c₁ c₂) / P := by
    have : 0 ≤ bR * Real.exp (min c₁ c₂) / P := by positivity
    linarith
  rcases le_or_gt (Real.log S) Y with h | h
  · rw [min_eq_left h]
    have hga : Real.log S ≤ min c₁ c₂ := le_min hgc (h.trans hYc)
    have hSe : S ≤ Real.exp (min c₁ c₂) := by
      calc S = Real.exp (Real.log S) := (Real.exp_log hS0).symm
        _ ≤ Real.exp (min c₁ c₂) := Real.exp_le_exp.mpr hga
    have hlog : Real.log (1 + bR * (S - 1) / P)
        ≤ Real.log (1 + bR * Real.exp (min c₁ c₂) / P) := by
      apply Real.log_le_log hu0
      have h1 : bR * (S - 1) ≤ bR * Real.exp (min c₁ c₂) :=
        mul_le_mul_of_nonneg_left (by linarith) hb
      have h2 : bR * (S - 1) / P ≤ bR * Real.exp (min c₁ c₂) / P :=
        div_le_div_of_nonneg_right h1 hP.le
      linarith
    linarith
  · rw [min_eq_right h.le]
    have hYa : Y ≤ min c₁ c₂ := le_min (h.le.trans hgc) hYc
    -- goal ⟺ log u ≤ log(v · S · e^{−Y}) with u, v the two collision factors
    have hkey : 1 + bR * (S - 1) / P
        ≤ (1 + bR * Real.exp (min c₁ c₂) / P) * S * Real.exp (-Y) := by
      have hSY : (1:ℝ) ≤ S * Real.exp (-Y) := by
        calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
          _ ≤ Real.exp (Real.log S - Y) := Real.exp_le_exp.mpr (by linarith)
          _ = Real.exp (Real.log S) * Real.exp (-Y) := by
              rw [← Real.exp_add]; ring_nf
          _ = S * Real.exp (-Y) := by rw [Real.exp_log hS0]
      have heaY : (1:ℝ) ≤ Real.exp (min c₁ c₂) * Real.exp (-Y) := by
        calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
          _ ≤ Real.exp (min c₁ c₂ - Y) := Real.exp_le_exp.mpr (by linarith)
          _ = Real.exp (min c₁ c₂) * Real.exp (-Y) := by
              rw [← Real.exp_add]; ring_nf
      have hexpand : (1 + bR * Real.exp (min c₁ c₂) / P) * S * Real.exp (-Y)
          = S * Real.exp (-Y)
            + bR / P * (Real.exp (min c₁ c₂) * Real.exp (-Y)) * S := by
        ring
      rw [hexpand]
      have h1 : bR * (S - 1) / P ≤ bR / P * S := by
        have : bR * (S - 1) ≤ bR * S := mul_le_mul_of_nonneg_left (by linarith) hb
        calc bR * (S - 1) / P ≤ bR * S / P := div_le_div_of_nonneg_right this hP.le
          _ = bR / P * S := by ring
      have h2 : bR / P * S ≤ bR / P * (Real.exp (min c₁ c₂) * Real.exp (-Y)) * S := by
        have hbP : (0:ℝ) ≤ bR / P := by positivity
        nlinarith [mul_nonneg hbP hS0.le]
      linarith
    have hlog := Real.log_le_log hu0 hkey
    rw [Real.log_mul (by positivity) (Real.exp_pos (-Y)).ne',
      Real.log_mul hv0.ne' hS0.ne', Real.log_exp] at hlog
    linarith

/-! ## Explicit numeric exponential facts for the window -/

/-- `10²¹⁰ ≤ e⁷⁰⁰` (via `10³ ≤ 2¹⁰` and `2 ≤ e`). -/
theorem low_ten_pow_le_exp_700 : (10:ℝ) ^ (210:ℕ) ≤ Real.exp 700 := by
  have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc (10:ℝ) ^ (210:ℕ) = ((10:ℝ) ^ (3:ℕ)) ^ (70:ℕ) := by rw [← pow_mul]
    _ ≤ ((2:ℝ) ^ (10:ℕ)) ^ (70:ℕ) := by
        apply pow_le_pow_left₀ (by positivity) (by norm_num) 70
    _ = (2:ℝ) ^ (700:ℕ) := by rw [← pow_mul]
    _ ≤ Real.exp 1 ^ (700:ℕ) := pow_le_pow_left₀ (by norm_num) h2 700
    _ = Real.exp 700 := Real.exp_one_pow 700

/-- `10¹⁰⁵ ≤ e³⁵⁰`. -/
theorem low_ten_pow_le_exp_350 : (10:ℝ) ^ (105:ℕ) ≤ Real.exp 350 := by
  have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc (10:ℝ) ^ (105:ℕ) = ((10:ℝ) ^ (3:ℕ)) ^ (35:ℕ) := by rw [← pow_mul]
    _ ≤ ((2:ℝ) ^ (10:ℕ)) ^ (35:ℕ) := by
        apply pow_le_pow_left₀ (by positivity) (by norm_num) 35
    _ = (2:ℝ) ^ (350:ℕ) := by rw [← pow_mul]
    _ ≤ Real.exp 1 ^ (350:ℕ) := pow_le_pow_left₀ (by norm_num) h2 350
    _ = Real.exp 350 := Real.exp_one_pow 350

/-- `e^16.05 ≤ 9.36·10⁶` — behind `log X ≥ 16.05` on the window. -/
theorem low_exp_16_05_ub : Real.exp 16.05 ≤ 9.36e6 := by
  have hsplit : (16.05:ℝ) = ((16:ℕ):ℝ) + 0.05 := by norm_num
  rw [hsplit, Real.exp_add]
  have h16 : Real.exp ((16:ℕ):ℝ) ≤ (2.7182818286:ℝ) ^ (16:ℕ) := low_exp_nat_ub 16
  have h005 : Real.exp 0.05 ≤ 1 / (1 - 0.05) :=
    low_exp_le_inv_one_sub (by norm_num)
  calc Real.exp ((16:ℕ):ℝ) * Real.exp 0.05
      ≤ (2.7182818286:ℝ) ^ (16:ℕ) * (1 / (1 - 0.05)) :=
        mul_le_mul h16 h005 (Real.exp_pos _).le (by positivity)
    _ ≤ 9.36e6 := by norm_num

/-- `2.41·10⁷ ≤ e¹⁷` — behind `log X ≤ 17` and `log(T+1) ≤ 17` on the
window. -/
theorem low_exp_17_lb : (2.41e7:ℝ) ≤ Real.exp 17 := by
  have h17 := low_exp_nat_lb 17
  have : (2.41e7:ℝ) ≤ (2.7182818283:ℝ) ^ (17:ℕ) := by norm_num
  calc (2.41e7:ℝ) ≤ (2.7182818283:ℝ) ^ (17:ℕ) := this
    _ ≤ Real.exp ((17:ℕ):ℝ) := h17
    _ = Real.exp 17 := by norm_num

/-- `1.85·10¹⁴ ≤ e^32.9` — behind `M + 1 ≥ X^2.05 ≥ 1.85·10¹⁴`. -/
theorem low_exp_32_9_lb : (1.85e14:ℝ) ≤ Real.exp 32.9 := by
  have h32 := low_exp_nat_lb 32
  have h03 : (1.345:ℝ) ≤ Real.exp 0.3 := by
    nlinarith [Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.3 by norm_num)]
  have h09 : (1.345:ℝ) ^ (3:ℕ) ≤ Real.exp 0.9 := by
    have hpow : ((1.345:ℝ)) ^ (3:ℕ) ≤ Real.exp 0.3 ^ (3:ℕ) :=
      pow_le_pow_left₀ (by norm_num) h03 3
    have hexp : Real.exp 0.3 ^ (3:ℕ) = Real.exp 0.9 := by
      rw [← Real.exp_nat_mul]; norm_num
    linarith
  have hsplit : (32.9:ℝ) = ((32:ℕ):ℝ) + 0.9 := by norm_num
  rw [hsplit, Real.exp_add]
  calc (1.85e14:ℝ) ≤ (2.7182818283:ℝ) ^ (32:ℕ) * (1.345:ℝ) ^ (3:ℕ) := by norm_num
    _ ≤ Real.exp ((32:ℕ):ℝ) * Real.exp 0.9 :=
        mul_le_mul h32 h09 (by positivity) (Real.exp_pos _).le

/-- `e³⁵ ≤ 1.59·10¹⁵` — behind `M ≤ 1.59·10¹⁵`. -/
theorem low_exp_35_ub : Real.exp 35 ≤ 1.59e15 := by
  have h := low_exp_nat_ub 35
  have : ((35:ℕ):ℝ) = 35 := by norm_num
  rw [this] at h
  calc Real.exp 35 ≤ (2.7182818286:ℝ) ^ (35:ℕ) := h
    _ ≤ 1.59e15 := by norm_num

/-- `8 886 110 ≤ e¹⁶` — behind `log(A+1) ≤ 16`. -/
theorem low_exp_16_lb : (8886110:ℝ) ≤ Real.exp 16 := by
  have h := low_exp_nat_lb 16
  have hc : ((16:ℕ):ℝ) = 16 := by norm_num
  rw [hc] at h
  calc (8886110:ℝ) ≤ (2.7182818283:ℝ) ^ (16:ℕ) := by norm_num
    _ ≤ Real.exp 16 := h

/-- `36 ≤ e^3.7` — behind `log(1 + log m) ≤ 3.7` for `m ≤ M`. -/
theorem low_exp_3_7_lb : (36:ℝ) ≤ Real.exp 3.7 := by
  have h3 := low_exp_nat_lb 3
  have h07 : (1.945:ℝ) ≤ Real.exp 0.7 := by
    nlinarith [Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.7 by norm_num)]
  have hsplit : (3.7:ℝ) = ((3:ℕ):ℝ) + 0.7 := by norm_num
  rw [hsplit, Real.exp_add]
  calc (36:ℝ) ≤ (2.7182818283:ℝ) ^ (3:ℕ) * 1.945 := by norm_num
    _ ≤ Real.exp ((3:ℕ):ℝ) * Real.exp 0.7 :=
        mul_le_mul h3 h07 (by norm_num) (Real.exp_pos _).le

/-- `log 12 ≤ 2.7725888` (via `12 ≤ 16 = 2⁴`). -/
theorem low_log_12_ub : Real.log 12 ≤ 2.7725888 := by
  have h1 : Real.log 12 ≤ Real.log 16 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2 ^ (4:ℕ) by norm_num, Real.log_pow]
    norm_num
  have h3 := Real.log_two_lt_d9
  rw [h2] at h1
  linarith

/-! ## Window facts (`9.7·10⁶ ≤ X ≤ 1.07·10⁷`) -/

section Window

variable {X : ℝ}

theorem low_logX_lb (h1 : (9.7e6:ℝ) ≤ X) : (16.05:ℝ) ≤ Real.log X := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [low_exp_16_05_ub]

theorem low_logX_ub (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    Real.log X ≤ 17 := by
  rw [Real.log_le_iff_le_exp (by linarith)]
  linarith [low_exp_17_lb]

theorem low_exp_X_lb (h1 : (9.7e6:ℝ) ≤ X) : (10:ℝ) ^ (210:ℕ) ≤ Real.exp X :=
  low_ten_pow_le_exp_700.trans (Real.exp_le_exp.mpr (by linarith))

theorem low_exp_half_X_lb (h1 : (9.7e6:ℝ) ≤ X) :
    (10:ℝ) ^ (105:ℕ) ≤ Real.exp (X / 2) :=
  low_ten_pow_le_exp_350.trans (Real.exp_le_exp.mpr (by linarith))

theorem low_N_lb (h1 : (9.7e6:ℝ) ≤ X) : (10:ℝ) ^ (209:ℕ) ≤ (lowN X : ℝ) := by
  have hfloor := exp_div_two_le_expFloor (show (1:ℝ) ≤ X by linarith)
  have hexp := low_exp_X_lb h1
  have : (10:ℝ) ^ (209:ℕ) ≤ (10:ℝ) ^ (210:ℕ) / 2 := by norm_num
  calc (10:ℝ) ^ (209:ℕ) ≤ (10:ℝ) ^ (210:ℕ) / 2 := this
    _ ≤ Real.exp X / 2 := by linarith
    _ ≤ (lowN X : ℝ) := hfloor

theorem low_N_pos (h1 : (9.7e6:ℝ) ≤ X) : (0:ℝ) < (lowN X : ℝ) := by
  have h := low_N_lb h1
  have : (0:ℝ) < (10:ℝ) ^ (209:ℕ) := by positivity
  linarith

theorem low_logN_ub (h1 : (9.7e6:ℝ) ≤ X) : Real.log (lowN X) ≤ X :=
  log_expFloor_le (by linarith)

theorem low_logN_lb (h1 : (9.7e6:ℝ) ≤ X) : X - 1e-9 ≤ Real.log (lowN X) := by
  have h : X - 1 / (lowN X : ℝ) ≤ Real.log (lowN X) :=
    log_expFloor_ge (show (1:ℝ) ≤ X by linarith)
  have hN := low_N_lb h1
  have hNpos := low_N_pos h1
  have hsmall : 1 / (lowN X : ℝ) ≤ 1e-9 := by
    rw [div_le_iff₀ hNpos]
    nlinarith [hN]
  linarith

theorem low_log2_pos : (0:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]

/-! ### The shell cutoff `M = ⌊X^2.05⌋` -/

theorem low_M_add_one_lb (h1 : (9.7e6:ℝ) ≤ X) :
    (1.85e14:ℝ) ≤ (lowM X : ℝ) + 1 := by
  have hX0 : (0:ℝ) < X := by linarith
  have hfloor : X ^ (2.05:ℝ) < (lowM X : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (X ^ (2.05:ℝ))
  have hrpow : Real.exp 32.9 ≤ X ^ (2.05:ℝ) := by
    rw [Real.rpow_def_of_pos hX0]
    apply Real.exp_le_exp.mpr
    nlinarith [low_logX_lb h1]
  linarith [low_exp_32_9_lb]

theorem low_M_ub (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    (lowM X : ℝ) ≤ 1.59e15 := by
  have hX0 : (0:ℝ) < X := by linarith
  have hfl : (lowM X : ℝ) ≤ X ^ (2.05:ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hX0.le _)
  have h35 : X ^ (2.05:ℝ) ≤ Real.exp 35 := by
    rw [Real.rpow_def_of_pos hX0]
    apply Real.exp_le_exp.mpr
    nlinarith [low_logX_ub h1 h2]
  linarith [low_exp_35_ub]

theorem low_M_add_one_le_exp_35 (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    (lowM X : ℝ) + 1 ≤ Real.exp 35 := by
  have hX0 : (0:ℝ) < X := by linarith
  have hfl : (lowM X : ℝ) ≤ X ^ (2.05:ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hX0.le _)
  have h3485 : X ^ (2.05:ℝ) ≤ Real.exp 34.85 := by
    rw [Real.rpow_def_of_pos hX0]
    apply Real.exp_le_exp.mpr
    nlinarith [low_logX_ub h1 h2]
  have hgap : Real.exp 34.85 + 1 ≤ Real.exp 35 := by
    have hsplit : Real.exp 35 = Real.exp 34.85 * Real.exp 0.15 := by
      rw [← Real.exp_add]; norm_num
    have h015 : (1.15:ℝ) ≤ Real.exp 0.15 := by
      linarith [Real.add_one_le_exp (0.15:ℝ)]
    have hbig : (35.85:ℝ) ≤ Real.exp 34.85 := by
      linarith [Real.add_one_le_exp (34.85:ℝ)]
    nlinarith
  linarith

/-- `log(m+1) ≤ 35` for every shell index `m ≤ M` — the window's version of
the paper's `log(M+1) < 34`. -/
theorem low_log_add_one_le_35 (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm : m ≤ lowM X) : Real.log ((m:ℝ) + 1) ≤ 35 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hcast : (m:ℝ) ≤ (lowM X : ℝ) := Nat.cast_le.mpr hm
  linarith [low_M_add_one_le_exp_35 h1 h2]

theorem low_one_le_M (h1 : (9.7e6:ℝ) ≤ X) : 1 ≤ lowM X := by
  have h := low_M_add_one_lb h1
  by_contra hc
  have hM : lowM X = 0 := by omega
  rw [hM] at h
  norm_num at h

/-! ### The quotient scale `Q = ⌊N/(M+1)⌋` -/

theorem low_MM_le_N (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    lowM X * (lowM X + 1) ≤ lowN X := by
  have hM := low_M_ub h1 h2
  have hN := low_N_lb h1
  have hM0 : (0:ℝ) ≤ (lowM X : ℝ) := Nat.cast_nonneg _
  have hbig : (2.6e30:ℝ) ≤ (10:ℝ) ^ (209:ℕ) := by norm_num
  have hcast : ((lowM X * (lowM X + 1) : ℕ) : ℝ) ≤ (lowN X : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hcast

theorem low_M_le_Q (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    lowM X ≤ lowN X / (lowM X + 1) :=
  (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (low_MM_le_N h1 h2)

theorem low_two_le_M (h1 : (9.7e6:ℝ) ≤ X) : 2 ≤ lowM X := by
  have h := low_M_add_one_lb h1
  have : (2:ℝ) ≤ (lowM X : ℝ) := by linarith
  exact_mod_cast this

theorem low_two_le_Q (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    2 ≤ lowN X / (lowM X + 1) :=
  le_trans (low_two_le_M h1) (low_M_le_Q h1 h2)

theorem low_N_pos_nat (h1 : (9.7e6:ℝ) ≤ X) : 0 < lowN X := by
  have h := low_N_pos h1
  exact_mod_cast h

theorem low_hQN (h1 : (9.7e6:ℝ) ≤ X) :
    lowN X / (lowM X + 1) < lowN X := by
  have hM := low_one_le_M h1
  exact Nat.div_lt_self (low_N_pos_nat h1) (by omega)

/-- Real-valued lower bound on a `ℕ`-division: `a/b − 1 < ⌊a/b⌋`. -/
theorem low_nat_div_cast_lb {a b : ℕ} (hb : 0 < b) :
    (a:ℝ) / (b:ℝ) - 1 < ((a / b : ℕ) : ℝ) := by
  have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have h1 : a < (a / b + 1) * b := by
    have h2 := Nat.div_add_mod a b
    have h3 := Nat.mod_lt a hb
    calc a = b * (a / b) + a % b := h2.symm
      _ < b * (a / b) + b := by omega
      _ = (a / b + 1) * b := by ring
  have h4 : (a:ℝ) / (b:ℝ) < ((a / b : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hbR]
    exact_mod_cast h1
  linarith

theorem low_hQ2 (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    lowN X < lowN X / (lowM X + 1) * (lowN X / (lowM X + 1)) := by
  have hN := low_N_lb h1
  have hqR : (lowN X:ℝ) / ((lowM X:ℝ) + 1) - 1
      < ((lowN X / (lowM X + 1) : ℕ) : ℝ) := by
    have h := low_nat_div_cast_lb (a := lowN X) (b := lowM X + 1) (Nat.succ_pos _)
    push_cast at h
    linarith
  have hM1 : (lowM X:ℝ) + 1 ≤ 1.6e15 := by linarith [low_M_ub h1 h2]
  have hMpos : (0:ℝ) < (lowM X:ℝ) + 1 := by positivity
  have hdiv : (lowN X:ℝ) / 1.6e15 ≤ (lowN X:ℝ) / ((lowM X:ℝ) + 1) :=
    div_le_div_of_nonneg_left (low_N_pos h1).le hMpos hM1
  have hbig : (4.1e30:ℝ) ≤ (10:ℝ) ^ (209:ℕ) := by norm_num
  have hgap : (lowN X:ℝ) / 2e15 ≤ (lowN X:ℝ) / 1.6e15 - 1 := by
    have h8 : (8e15:ℝ) ≤ (lowN X:ℝ) := le_trans (by norm_num) hN
    linarith
  set Q := lowN X / (lowM X + 1) with hQdef
  have hQlb : (lowN X:ℝ) / 2e15 ≤ (Q:ℝ) := by linarith
  have hNQ : (lowN X:ℝ) ≤ 2e15 * (Q:ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2e15)] at hQlb
    linarith
  have hQ0 : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg _
  have hN0 : (0:ℝ) ≤ (lowN X:ℝ) := (low_N_pos h1).le
  have hsq : (lowN X:ℝ) * (lowN X:ℝ) ≤ (2e15 * (Q:ℝ)) * (2e15 * (Q:ℝ)) :=
    mul_le_mul hNQ hNQ hN0 (by positivity)
  have hgoal : (lowN X:ℝ) < (Q:ℝ) * (Q:ℝ) := by nlinarith
  exact_mod_cast hgoal

/-! ### The upper-estimate split index `T = ⌊(X−36)/log 2⌋` -/

theorem low_T_lb (h1 : (9.7e6:ℝ) ≤ X) : 13994000 ≤ lowT X := by
  apply Nat.le_floor
  rw [le_div_iff₀ low_log2_pos]
  push_cast
  nlinarith [Real.log_two_lt_d9]

theorem low_T_cast_ub (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    (lowT X : ℝ) ≤ 1.6e7 := by
  have hfl : (lowT X:ℝ) ≤ (X - 36) / Real.log 2 :=
    Nat.floor_le (div_nonneg (by linarith) low_log2_pos.le)
  have hub : (X - 36) / Real.log 2 ≤ 1.6e7 := by
    rw [div_le_iff₀ low_log2_pos]
    nlinarith [Real.log_two_gt_d9]
  linarith

theorem low_T_le_M (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    lowT X ≤ lowM X := by
  have hT := low_T_cast_ub h1 h2
  have hM := low_M_add_one_lb h1
  have : (lowT X:ℝ) ≤ (lowM X:ℝ) := by linarith
  exact_mod_cast this

theorem low_one_le_T (h1 : (9.7e6:ℝ) ≤ X) : 1 ≤ lowT X :=
  le_trans (by norm_num) (low_T_lb h1)

theorem low_log_T_add_one_ub (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    Real.log ((lowT X:ℝ) + 1) ≤ 17 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  linarith [low_T_cast_ub h1 h2, low_exp_17_lb]

theorem low_log_T_ub (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    Real.log (lowT X : ℝ) ≤ 17 := by
  have hpos : (0:ℝ) < (lowT X : ℝ) := by
    exact_mod_cast low_one_le_T h1
  rw [Real.log_le_iff_le_exp hpos]
  linarith [low_T_cast_ub h1 h2, low_exp_17_lb]

theorem low_T_mul_log2_le (h1 : (9.7e6:ℝ) ≤ X) {m : ℕ} (hm : m ≤ lowT X) :
    (m:ℝ) * Real.log 2 ≤ X - 36 := by
  have hfl : (lowT X:ℝ) ≤ (X - 36) / Real.log 2 :=
    Nat.floor_le (div_nonneg (by linarith) low_log2_pos.le)
  have hm' : (m:ℝ) ≤ (lowT X:ℝ) := Nat.cast_le.mpr hm
  calc (m:ℝ) * Real.log 2 ≤ (X - 36) / Real.log 2 * Real.log 2 := by
        apply mul_le_mul_of_nonneg_right _ low_log2_pos.le
        linarith
    _ = X - 36 := div_mul_cancel₀ _ low_log2_pos.ne'

/-! ### The lower-estimate split index `A = ⌊X/(2 log 2)⌋` -/

theorem low_A_lb (h1 : (9.7e6:ℝ) ≤ X) : 6997000 ≤ lowA X := by
  apply Nat.le_floor
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.log 2)]
  push_cast
  nlinarith [Real.log_two_lt_d9]

theorem low_A_cast_ub (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    (lowA X : ℝ) ≤ 7.8e6 := by
  have hfl : (lowA X:ℝ) ≤ X / (2 * Real.log 2) :=
    Nat.floor_le (div_nonneg (by linarith) (by positivity))
  have hub : X / (2 * Real.log 2) ≤ 7.8e6 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.log 2)]
    nlinarith [Real.log_two_gt_d9]
  linarith

theorem low_A_le_M (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    lowA X ≤ lowM X := by
  have hA := low_A_cast_ub h1 h2
  have hM := low_M_add_one_lb h1
  have : (lowA X:ℝ) ≤ (lowM X:ℝ) := by linarith
  exact_mod_cast this

theorem low_log_A_add_one_ub (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    Real.log ((lowA X:ℝ) + 1) ≤ 16 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  linarith [low_A_cast_ub h1 h2, low_exp_16_lb]

theorem low_A_mul_log2_le (h1 : (9.7e6:ℝ) ≤ X) {m : ℕ} (hm : m ≤ lowA X) :
    (m:ℝ) * Real.log 2 ≤ X / 2 := by
  have hfl : (lowA X:ℝ) ≤ X / (2 * Real.log 2) :=
    Nat.floor_le (div_nonneg (by linarith) (by positivity))
  have hm' : (m:ℝ) ≤ (lowA X:ℝ) := Nat.cast_le.mpr hm
  have hcalc : (m:ℝ) * Real.log 2 ≤ X / (2 * Real.log 2) * Real.log 2 := by
    apply mul_le_mul_of_nonneg_right _ low_log2_pos.le
    linarith
  have hid : X / (2 * Real.log 2) * Real.log 2 = X / 2 := by
    field_simp
  linarith [hid ▸ hcalc]

theorem low_gt_A_cast {m : ℕ} (hm : lowA X < m) :
    X < 2 * Real.log 2 * (m:ℝ) := by
  have hfloor : X / (2 * Real.log 2) < (lowA X : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hm' : (lowA X:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have hpos : (0:ℝ) < 2 * Real.log 2 := by positivity
  have := (div_lt_iff₀ hpos).mp (lt_of_lt_of_le hfloor hm')
  linarith

/-- The window's uniform bound `X/(X−36) ≤ 1.0000038`. -/
theorem low_X_div_X36_ub (h1 : (9.7e6:ℝ) ≤ X) :
    X / (X - 36) ≤ 1.0000038 := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end Window

/-! ## Shell counts at the real endpoints

The shell count `P_m = |shellPrimes N m|` equals `π(N/m) − π(N/(m+1))` with
`π` at the *real* points `N/m` and `N/(m+1)` (`primePi` floors its argument,
and `⌊N/k⌋` is exactly `ℕ`-division), so eq. `explicit-shell-count` needs no
integer-part slop at all.  (An analogous lemma exists in the asymptotic
averaging development; this file keeps its own copy to stay self-contained,
see the module docstring.) -/

theorem low_card_shellPrimes {N m : ℕ} (hm : 1 ≤ m) :
    ((shellPrimes N m).card : ℝ)
      = (primePi ((N:ℝ) / (m:ℝ)) : ℝ) - (primePi ((N:ℝ) / ((m:ℝ) + 1)) : ℝ) := by
  have hfloor1 : primePi ((N:ℝ) / (m:ℝ))
      = ((Finset.range (N / m + 1)).filter Nat.Prime).card := by
    rw [primePi, Nat.floor_div_natCast, Nat.floor_natCast, Nat.primeCounting,
      Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hfloor2 : primePi ((N:ℝ) / ((m:ℝ) + 1))
      = ((Finset.range (N / (m + 1) + 1)).filter Nat.Prime).card := by
    have hcast : (m:ℝ) + 1 = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, primePi, Nat.floor_div_natCast, Nat.floor_natCast,
      Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hsplit : (Finset.range (N / m + 1)).filter Nat.Prime
      = ((Finset.range (N / (m + 1) + 1)).filter Nat.Prime) ∪ shellPrimes N m := by
    have hdivle : N / (m + 1) ≤ N / m := Nat.div_le_div_left (by omega) (by omega)
    ext k
    simp only [shellPrimes, Finset.mem_filter, Finset.mem_union, Finset.mem_range,
      Finset.mem_Ioc]
    constructor
    · rintro ⟨hk, hkp⟩
      rcases le_or_gt k (N / (m + 1)) with h | h
      · exact Or.inl ⟨by omega, hkp⟩
      · exact Or.inr ⟨⟨h, by omega⟩, hkp⟩
    · rintro (⟨hk, hkp⟩ | ⟨⟨hk1, hk2⟩, hkp⟩)
      · exact ⟨by omega, hkp⟩
      · exact ⟨by omega, hkp⟩
  have hdisj : Disjoint ((Finset.range (N / (m + 1) + 1)).filter Nat.Prime)
      (shellPrimes N m) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [shellPrimes, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Ioc] at hk1 hk2
    omega
  have hcard : ((Finset.range (N / m + 1)).filter Nat.Prime).card
      = ((Finset.range (N / (m + 1) + 1)).filter Nat.Prime).card
        + (shellPrimes N m).card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
  rw [hfloor1, hfloor2, hcard]
  push_cast
  ring

section ShellEstimates

variable {X : ℝ}

/-! ### Shell endpoint estimates -/

theorem low_shell_a_ge_two (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hmM : m ≤ lowM X) : (2:ℝ) ≤ (lowN X:ℝ) / ((m:ℝ) + 1) := by
  have hN := low_N_lb h1
  have hm' : (m:ℝ) + 1 ≤ 1.6e15 := by
    have hcast : (m:ℝ) ≤ (lowM X : ℝ) := Nat.cast_le.mpr hmM
    linarith [low_M_ub h1 h2]
  have hbig : (3.2e15:ℝ) ≤ (10:ℝ) ^ (209:ℕ) := by norm_num
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

theorem low_shell_a_le_b (h1 : (9.7e6:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m) :
    (lowN X:ℝ) / ((m:ℝ) + 1) ≤ (lowN X:ℝ) / (m:ℝ) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  exact div_le_div_of_nonneg_left (low_N_pos h1).le hm0 (by linarith)

theorem low_loga_lb (h1 : (9.7e6:ℝ) ≤ X) {m : ℕ} :
    X - Real.log ((m:ℝ) + 1) - 1e-9 ≤ Real.log ((lowN X:ℝ) / ((m:ℝ) + 1)) := by
  rw [Real.log_div (low_N_pos h1).ne' (by positivity)]
  linarith [low_logN_lb h1]

theorem low_loga_ge_X36 (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hmM : m ≤ lowM X) :
    X - 36 ≤ Real.log ((lowN X:ℝ) / ((m:ℝ) + 1)) := by
  linarith [low_loga_lb h1 (m := m), low_log_add_one_le_35 h1 h2 hmM]

theorem low_loga_le_X (h1 : (9.7e6:ℝ) ≤ X) {m : ℕ} :
    Real.log ((lowN X:ℝ) / ((m:ℝ) + 1)) ≤ X := by
  rw [Real.log_div (low_N_pos h1).ne' (by positivity)]
  have hlog1 : (0:ℝ) ≤ Real.log ((m:ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
  linarith [low_logN_ub h1]

theorem low_logb_ub (h1 : (9.7e6:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m) :
    Real.log ((lowN X:ℝ) / (m:ℝ)) ≤ X - Real.log (m:ℝ) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  rw [Real.log_div (low_N_pos h1).ne' hm0.ne']
  linarith [low_logN_ub h1]

theorem low_logb_le_X (h1 : (9.7e6:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m) :
    Real.log ((lowN X:ℝ) / (m:ℝ)) ≤ X := by
  have hlogm : (0:ℝ) ≤ Real.log (m:ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm1)
  linarith [low_logb_ub h1 hm1]

theorem low_loga_le_logb (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ lowM X) :
    Real.log ((lowN X:ℝ) / ((m:ℝ) + 1)) ≤ Real.log ((lowN X:ℝ) / (m:ℝ)) :=
  Real.log_le_log (lt_of_lt_of_le (by norm_num) (low_shell_a_ge_two h1 h2 hmM))
    (low_shell_a_le_b h1 hm1)

theorem low_logb_pos (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ lowM X) :
    (0:ℝ) < Real.log ((lowN X:ℝ) / (m:ℝ)) := by
  have := low_loga_ge_X36 h1 h2 hmM
  have := low_loga_le_logb h1 h2 hm1 hmM
  linarith

/-! ### FKS error at the shell endpoints -/

theorem low_fks_a (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hmM : m ≤ lowM X) :
    fksError ((lowN X:ℝ) / ((m:ℝ) + 1)) ≤ (lowN X:ℝ) / 10 ^ 100 := by
  have ha0 : (0:ℝ) ≤ (lowN X:ℝ) / ((m:ℝ) + 1) := by positivity
  have hlog : (9 * 10 ^ 6 : ℝ) ≤ Real.log ((lowN X:ℝ) / ((m:ℝ) + 1)) := by
    have := low_loga_ge_X36 h1 h2 hmM
    linarith
  have htiny := fksError_le_tiny ha0 hlog
  have hle : (lowN X:ℝ) / ((m:ℝ) + 1) ≤ (lowN X:ℝ) := by
    apply div_le_self (low_N_pos h1).le
    linarith [Nat.cast_nonneg (α := ℝ) m]
  calc fksError ((lowN X:ℝ) / ((m:ℝ) + 1))
      ≤ (lowN X:ℝ) / ((m:ℝ) + 1) / 10 ^ 100 := htiny
    _ ≤ (lowN X:ℝ) / 10 ^ 100 := by
        apply div_le_div_of_nonneg_right hle
        norm_num

theorem low_fks_b (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ lowM X) :
    fksError ((lowN X:ℝ) / (m:ℝ)) ≤ (lowN X:ℝ) / 10 ^ 100 := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hb0 : (0:ℝ) ≤ (lowN X:ℝ) / (m:ℝ) := by positivity
  have hlog : (9 * 10 ^ 6 : ℝ) ≤ Real.log ((lowN X:ℝ) / (m:ℝ)) := by
    have := low_loga_ge_X36 h1 h2 hmM
    have := low_loga_le_logb h1 h2 hm1 hmM
    linarith
  have htiny := fksError_le_tiny hb0 hlog
  have hle : (lowN X:ℝ) / (m:ℝ) ≤ (lowN X:ℝ) := by
    apply div_le_self (low_N_pos h1).le
    exact_mod_cast hm1
  calc fksError ((lowN X:ℝ) / (m:ℝ))
      ≤ (lowN X:ℝ) / (m:ℝ) / 10 ^ 100 := htiny
    _ ≤ (lowN X:ℝ) / 10 ^ 100 := by
        apply div_le_div_of_nonneg_right hle
        norm_num

/-- The exact real shell length: `N/m − N/(m+1) = N/(m(m+1))`. -/
theorem low_shell_length {N₀ : ℝ} {m : ℕ} (hm1 : 1 ≤ m) :
    N₀ / (m:ℝ) - N₀ / ((m:ℝ) + 1) = N₀ / ((m:ℝ) * ((m:ℝ) + 1)) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  field_simp
  ring

/-! ### Window-agnostic shared cores for the low/high shell family

The following `_of` helpers factor the parts of the per-shell estimates that
are *identical* between the low window (`Erdos320/Lemmas/ExplicitLowAveraging`)
and the high window (`Erdos320/Lemmas/ExplicitHighAveraging`).  The two windows
differ only in the uniform log-denominator (`D ∈ {X − 36, highLogDenom X}`) and
the per-endpoint FKS error allowance (junk term `J`, resp. slack `eps ∈
{1/10¹⁰⁰, highFksEps X}`); these are passed as parameters here and *never baked
in*, so each concrete low/high lemma is a thin call supplying its own `D`/`J`.
-/

/-- Shared core of `low/high_shell_card_ub`: the FKS upper shell count, with the
two per-endpoint errors bounded by an abstract junk term `J`. -/
theorem shell_card_ub_of {N m : ℕ} {J : ℝ} (hm1 : 1 ≤ m)
    (ha2 : (2:ℝ) ≤ (N:ℝ) / ((m:ℝ) + 1))
    (hab : (N:ℝ) / ((m:ℝ) + 1) ≤ (N:ℝ) / (m:ℝ))
    (hj : fksError ((N:ℝ) / ((m:ℝ) + 1)) + fksError ((N:ℝ) / (m:ℝ)) ≤ J) :
    ((shellPrimes N m).card : ℝ)
      ≤ (N:ℝ) / ((m:ℝ) * ((m:ℝ) + 1))
          / Real.log ((N:ℝ) / ((m:ℝ) + 1)) + J := by
  rw [low_card_shellPrimes hm1]
  have hupper := primeInterval_upper ha2 hab
  have hlen := low_shell_length (N₀ := (N:ℝ)) hm1
  have hrw : ((N:ℝ) / (m:ℝ) - (N:ℝ) / ((m:ℝ) + 1))
        / Real.log ((N:ℝ) / ((m:ℝ) + 1))
      = (N:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / Real.log ((N:ℝ) / ((m:ℝ) + 1)) := by
    rw [hlen]
  linarith [hrw ▸ hupper]

/-- Shared core of `low/high_shell_card_lb`: the FKS lower shell count with the
`X` denominator, per-endpoint error bounded by `J`. -/
theorem shell_card_lb_of {N m : ℕ} {Xv J : ℝ} (hm1 : 1 ≤ m)
    (ha2 : (2:ℝ) ≤ (N:ℝ) / ((m:ℝ) + 1))
    (hab : (N:ℝ) / ((m:ℝ) + 1) ≤ (N:ℝ) / (m:ℝ))
    (hlogbpos : (0:ℝ) < Real.log ((N:ℝ) / (m:ℝ)))
    (hlogbleX : Real.log ((N:ℝ) / (m:ℝ)) ≤ Xv)
    (hj : fksError ((N:ℝ) / ((m:ℝ) + 1)) + fksError ((N:ℝ) / (m:ℝ)) ≤ J) :
    (N:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / Xv - J ≤ ((shellPrimes N m).card : ℝ) := by
  rw [low_card_shellPrimes hm1]
  have hlower := primeInterval_lower ha2 hab
  have hlen := low_shell_length (N₀ := (N:ℝ)) hm1
  have hnum0 : (0:ℝ) ≤ (N:ℝ) / (m:ℝ) - (N:ℝ) / ((m:ℝ) + 1) := by linarith
  have hdenom : ((N:ℝ) / (m:ℝ) - (N:ℝ) / ((m:ℝ) + 1)) / Xv
      ≤ ((N:ℝ) / (m:ℝ) - (N:ℝ) / ((m:ℝ) + 1)) / Real.log ((N:ℝ) / (m:ℝ)) :=
    div_le_div_of_nonneg_left hnum0 hlogbpos hlogbleX
  rw [hlen] at hdenom hlower
  linarith

/-- Shared core of `low/high_shell_card_lb_sharp`: the FKS lower shell count with
the `log(N/m)` denominator, per-endpoint error bounded by `J`. -/
theorem shell_card_lb_sharp_of {N m : ℕ} {J : ℝ} (hm1 : 1 ≤ m)
    (ha2 : (2:ℝ) ≤ (N:ℝ) / ((m:ℝ) + 1))
    (hab : (N:ℝ) / ((m:ℝ) + 1) ≤ (N:ℝ) / (m:ℝ))
    (hj : fksError ((N:ℝ) / ((m:ℝ) + 1)) + fksError ((N:ℝ) / (m:ℝ)) ≤ J) :
    (N:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / Real.log ((N:ℝ) / (m:ℝ)) - J
      ≤ ((shellPrimes N m).card : ℝ) := by
  rw [low_card_shellPrimes hm1]
  have hlower := primeInterval_lower ha2 hab
  have hlen := low_shell_length (N₀ := (N:ℝ)) hm1
  rw [hlen] at hlower
  linarith

/-- Shared core of `low/high_shell_logSum_le_card_mul_cap`: the per-prime cap
`log σ_p(m) ≤ min(g(m), log(N/m))` summed over the shell, given the shell-prime
lower bound `hgt : m < p`. -/
theorem shell_logSum_le_card_mul_cap_of {N m : ℕ} (hm1 : 1 ≤ m)
    (hgt : ∀ p ∈ shellPrimes N m, m < p) :
    ∑ p ∈ shellPrimes N m, Real.log (sigma p m)
      ≤ ((shellPrimes N m).card : ℝ) * min (g m) (Real.log ((N:ℝ) / (m:ℝ))) := by
  have hm0 : 0 < m := hm1
  have hbound : ∀ p ∈ shellPrimes N m,
      Real.log (sigma p m) ≤ min (g m) (Real.log ((N:ℝ) / (m:ℝ))) := by
    intro p hp
    have hpr : p.Prime := (mem_shellPrimes.mp hp).2.2
    have hmp : m < p := hgt p hp
    have hσ1 : (1:ℝ) ≤ ((sigma p m : ℕ) : ℝ) := by exact_mod_cast one_le_sigma p m
    refine le_min ?_ ?_
    · have hσS : sigma p m ≤ S m := sigma_le_S hpr hmp
      exact Real.log_le_log (by linarith) (by exact_mod_cast hσS)
    · have hσp : ((sigma p m : ℕ) : ℝ) ≤ (p:ℝ) := by
        exact_mod_cast sigma_le_self hpr.pos m
      have hpub : (p:ℝ) ≤ (N:ℝ) / (m:ℝ) := by
        obtain ⟨-, hhi, -⟩ := mem_shellPrimes.mp hp
        have h1 : p * m ≤ N := (Nat.le_div_iff_mul_le hm0).mp hhi
        have h2 : (p:ℝ) * (m:ℝ) ≤ (N:ℝ) := by exact_mod_cast h1
        rw [le_div_iff₀ (by exact_mod_cast hm0 : (0:ℝ) < (m:ℝ))]
        exact h2
      exact Real.log_le_log (by linarith) (le_trans hσp hpub)
  calc ∑ p ∈ shellPrimes N m, Real.log (sigma p m)
      ≤ (shellPrimes N m).card • min (g m) (Real.log ((N:ℝ) / (m:ℝ))) :=
        Finset.sum_le_card_nsmul _ _ _ hbound
    _ = ((shellPrimes N m).card : ℝ)
          * min (g m) (Real.log ((N:ℝ) / (m:ℝ))) := nsmul_eq_mul _ _

/-- Shared core of `low/high_shell_upper_generic`: normalize the capped shell
sum by `X/N` and insert the FKS count, leaving the exact factor plus uniform
`300 X² · eps` junk.  `L` is `log(N/(m+1))`, `muV` the capped weight
`min(g(m), log(N/m))`, `cardv` the shell prime count, `s` the shell sum. -/
theorem shell_upper_generic_of {X eps L muV s cardv Nv : ℝ} {m : ℕ}
    (hNpos : 0 < Nv) (hm0 : 0 < (m:ℝ)) (hLpos : 0 < L)
    (hmu0 : 0 ≤ muV) (hmuX : muV ≤ X) (hX0 : 0 ≤ X) (heps0 : 0 ≤ eps)
    (hcap : s ≤ cardv * muV)
    (hcard : cardv ≤ Nv / ((m:ℝ) * ((m:ℝ) + 1)) / L + 2 * Nv * eps) :
    X / Nv * s
      ≤ X * muV / ((m:ℝ) * ((m:ℝ) + 1)) / L + 300 * X ^ 2 * eps := by
  have hNe : Nv ≠ 0 := hNpos.ne'
  have hme : (m:ℝ) ≠ 0 := hm0.ne'
  have hm1e : (m:ℝ) + 1 ≠ 0 := by positivity
  have hLe : L ≠ 0 := hLpos.ne'
  have hXN0 : (0:ℝ) ≤ X / Nv := by positivity
  have step1 : X / Nv * s
      ≤ X / Nv * ((Nv / ((m:ℝ) * ((m:ℝ) + 1)) / L + 2 * Nv * eps) * muV) := by
    apply mul_le_mul_of_nonneg_left _ hXN0
    exact le_trans hcap (mul_le_mul_of_nonneg_right hcard hmu0)
  have hexpand : X / Nv * ((Nv / ((m:ℝ) * ((m:ℝ) + 1)) / L + 2 * Nv * eps) * muV)
      = X * muV / ((m:ℝ) * ((m:ℝ) + 1)) / L + 2 * X * muV * eps := by
    field_simp
  have hjunk : 2 * X * muV * eps ≤ 300 * X ^ 2 * eps := by
    apply mul_le_mul_of_nonneg_right _ heps0
    nlinarith
  rw [hexpand] at step1
  linarith

/-- Shared core of `low/high_shell_upper_head` (head regime, fully clamped
`g(m) ≤ m log 2 ≤ D ≤ L`): the clamped-shell algebra, over the abstract
denominator `D` and abstract junk term `J`.  `lhs` is the normalized shell sum,
`gm = g(m)`, `L = log(N/(m+1))`, `Lm = log(N/m)`. -/
theorem shell_head_clamp_of {X D L Lm gm lhs J : ℝ} {m : ℕ}
    (hm0 : 0 < (m:ℝ)) (hD : 0 < D) (hDL : D ≤ L) (hLX : L ≤ X)
    (hg2 : gm ≤ (m:ℝ) * Real.log 2)
    (hmlog2 : (m:ℝ) * Real.log 2 ≤ D) (hab : L ≤ Lm)
    (hXL : X - L ≤ Real.log ((m:ℝ) + 1) + 1e-9)
    (hgen : lhs ≤ X * min gm Lm / ((m:ℝ) * ((m:ℝ) + 1)) / L + J) :
    lhs ≤ min gm X / ((m:ℝ) * ((m:ℝ) + 1))
        + Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9) / (((m:ℝ) + 1) * D))
        + J := by
  have hLpos : 0 < L := lt_of_lt_of_le hD hDL
  have hgL : gm ≤ L := le_trans (le_trans hg2 hmlog2) hDL
  have hgX : gm ≤ X := le_trans hgL hLX
  have hminb : min gm Lm = gm := min_eq_left (le_trans hgL hab)
  have hminX : min gm X = gm := min_eq_left hgX
  rw [hminb] at hgen
  rw [hminX]
  have hlog1 : (0:ℝ) ≤ Real.log ((m:ℝ) + 1) := Real.log_nonneg (by linarith)
  have hXLpos : 0 ≤ X - L := by linarith
  have hid : X * gm / ((m:ℝ) * ((m:ℝ) + 1)) / L - gm / ((m:ℝ) * ((m:ℝ) + 1))
      = gm * (X - L) / ((m:ℝ) * ((m:ℝ) + 1) * L) := by
    field_simp
  have hkey : gm * (X - L) / ((m:ℝ) * ((m:ℝ) + 1) * L)
      ≤ Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9) / (((m:ℝ) + 1) * D)) := by
    have hnum : gm * (X - L)
        ≤ ((m:ℝ) * Real.log 2) * (Real.log ((m:ℝ) + 1) + 1e-9) :=
      mul_le_mul hg2 hXL hXLpos (by positivity)
    have hstep : gm * (X - L) / ((m:ℝ) * ((m:ℝ) + 1) * L)
        ≤ ((m:ℝ) * Real.log 2) * (Real.log ((m:ℝ) + 1) + 1e-9)
          / ((m:ℝ) * ((m:ℝ) + 1) * D) := by
      gcongr
    have hidt : ((m:ℝ) * Real.log 2) * (Real.log ((m:ℝ) + 1) + 1e-9)
          / ((m:ℝ) * ((m:ℝ) + 1) * D)
        = Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9) / (((m:ℝ) + 1) * D)) := by
      field_simp
    linarith [hidt ▸ hstep]
  linarith

/-- Shared core of `low/high_shell_upper_tail` (tail regime, cap saturated at
`X`): the clamped/overflow case split, over the abstract denominator `D` and
abstract junk `J`, taking the window-specific overflow numerator bound `hnum`
(`X·log(N/m) − L² ≤ X(log(m+1) + 1e-7)`) as a parameter. -/
theorem shell_upper_tail_of {X D L Lm gm lhs J : ℝ} {m : ℕ}
    (hm0 : 0 < (m:ℝ)) (hD : 0 < D) (hX0 : 0 < X) (hDL : D ≤ L) (hLX : L ≤ X)
    (hab : L ≤ Lm)
    (hXL : X - L ≤ Real.log ((m:ℝ) + 1) + 1e-9)
    (hnum : X * Lm - L ^ 2 ≤ X * (Real.log ((m:ℝ) + 1) + 1e-7))
    (hgen : lhs ≤ X * min gm Lm / ((m:ℝ) * ((m:ℝ) + 1)) / L + J) :
    lhs ≤ min gm X / ((m:ℝ) * ((m:ℝ) + 1))
        + X / D * ((Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1)))
        + J := by
  have hLpos : 0 < L := lt_of_lt_of_le hD hDL
  have hlog1 : (0:ℝ) ≤ Real.log ((m:ℝ) + 1) := Real.log_nonneg (by linarith)
  have hcm0 : (0:ℝ) < (m:ℝ) * ((m:ℝ) + 1) := by positivity
  suffices hsuff : X * min gm Lm / ((m:ℝ) * ((m:ℝ) + 1)) / L
      ≤ min gm X / ((m:ℝ) * ((m:ℝ) + 1))
        + X / D * ((Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))) by
    linarith
  rcases le_or_gt gm L with hcase | hcase
  · have hgX : gm ≤ X := hcase.trans hLX
    have hminb : min gm Lm = gm := min_eq_left (hcase.trans hab)
    have hminX : min gm X = gm := min_eq_left hgX
    rw [hminb, hminX]
    have hid : X * gm / ((m:ℝ) * ((m:ℝ) + 1)) / L - gm / ((m:ℝ) * ((m:ℝ) + 1))
        = gm * (X - L) / ((m:ℝ) * ((m:ℝ) + 1) * L) := by
      field_simp
    have hkey : gm * (X - L) / ((m:ℝ) * ((m:ℝ) + 1) * L)
        ≤ X / D * ((Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))) := by
      have hnum2 : gm * (X - L) ≤ X * (Real.log ((m:ℝ) + 1) + 1e-7) := by
        have h9 : Real.log ((m:ℝ) + 1) + 1e-9 ≤ Real.log ((m:ℝ) + 1) + 1e-7 := by
          norm_num
        have := mul_le_mul hgX hXL (by linarith) hX0.le
        nlinarith
      have hstep : gm * (X - L) / ((m:ℝ) * ((m:ℝ) + 1) * L)
          ≤ X * (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1) * D) := by
        gcongr
      have hidt : X * (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1) * D)
          = X / D * ((Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))) := by
        field_simp
      linarith [hidt ▸ hstep]
    linarith
  · have hminX_ge : L ≤ min gm X := le_min hcase.le hLX
    have hstep : X * min gm Lm / ((m:ℝ) * ((m:ℝ) + 1)) / L
        ≤ X * Lm / ((m:ℝ) * ((m:ℝ) + 1)) / L := by
      gcongr
      exact min_le_right _ _
    have hmain : X * Lm / ((m:ℝ) * ((m:ℝ) + 1)) / L - L / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ X / D * ((Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))) := by
      have hid : X * Lm / ((m:ℝ) * ((m:ℝ) + 1)) / L - L / ((m:ℝ) * ((m:ℝ) + 1))
          = (X * Lm - L ^ 2) / ((m:ℝ) * ((m:ℝ) + 1) * L) := by
        field_simp
      have hR0 : (0:ℝ) ≤ X * (Real.log ((m:ℝ) + 1) + 1e-7) :=
        mul_nonneg hX0.le (by positivity)
      have hstep1 : (X * Lm - L ^ 2) / ((m:ℝ) * ((m:ℝ) + 1) * L)
          ≤ X * (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1) * L) :=
        div_le_div_of_nonneg_right hnum (mul_pos hcm0 hLpos).le
      have hstep2 : X * (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1) * L)
          ≤ X * (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1) * D) := by
        apply div_le_div_of_nonneg_left hR0 (by positivity)
        exact mul_le_mul_of_nonneg_left hDL hcm0.le
      have hidt : X * (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1) * D)
          = X / D * ((Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))) := by
        field_simp
      rw [hid, ← hidt]
      exact le_trans hstep1 hstep2
    have hLmin : L / ((m:ℝ) * ((m:ℝ) + 1)) ≤ min gm X / ((m:ℝ) * ((m:ℝ) + 1)) :=
      div_le_div_of_nonneg_right hminX_ge hcm0.le
    linarith

/-- Shared core of `low/high_collision_hb`: the collision-multiplicity `hb`
bound, over the abstract log-denominator `D` (`D ≤ log(N/(m+1))`). -/
theorem collision_hb_of {N m : ℕ} {D : ℝ} (hm1 : 1 ≤ m) (hD : 0 < D)
    (hden : D ≤ Real.log ((N:ℝ) / ((m:ℝ) + 1))) :
    Real.log ((((Finset.Icc 1 m).lcm id : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ))
        / Real.log ((N:ℝ) / ((m:ℝ) + 1))
      ≤ ((⌊(Real.log 4 * m + Real.sqrt m * Real.log m
          + Real.log (1 + Real.log m)) / D⌋₊ : ℕ) : ℝ) + 1 := by
  have hW := log_lcm_mul_harmonicSum_le hm1 (harmonicSum_le_one_add_log m)
  have hL1 : (1:ℝ) ≤ (((Finset.Icc 1 m).lcm id : ℕ) : ℝ) := by
    exact_mod_cast lcm_Icc_pos m
  have hH1 : (1:ℝ) ≤ ((harmonicSum m : ℚ) : ℝ) := by
    exact_mod_cast one_le_harmonicSum hm1
  have hnum0 : 0 ≤ Real.log ((((Finset.Icc 1 m).lcm id : ℕ) : ℝ)
      * ((harmonicSum m : ℚ) : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  have hquot : Real.log ((((Finset.Icc 1 m).lcm id : ℕ) : ℝ)
        * ((harmonicSum m : ℚ) : ℝ))
        / Real.log ((N:ℝ) / ((m:ℝ) + 1))
      ≤ (Real.log 4 * m + Real.sqrt m * Real.log m
          + Real.log (1 + Real.log m)) / D := by
    calc Real.log ((((Finset.Icc 1 m).lcm id : ℕ) : ℝ)
          * ((harmonicSum m : ℚ) : ℝ))
          / Real.log ((N:ℝ) / ((m:ℝ) + 1))
        ≤ Real.log ((((Finset.Icc 1 m).lcm id : ℕ) : ℝ)
            * ((harmonicSum m : ℚ) : ℝ)) / D :=
          div_le_div_of_nonneg_left hnum0 hD hden
      _ ≤ (Real.log 4 * m + Real.sqrt m * Real.log m
            + Real.log (1 + Real.log m)) / D :=
          div_le_div_of_nonneg_right hW hD.le
  have hfloor : (Real.log 4 * m + Real.sqrt m * Real.log m
        + Real.log (1 + Real.log m)) / D
      < ((⌊(Real.log 4 * m + Real.sqrt m * Real.log m
          + Real.log (1 + Real.log m)) / D⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  linarith

/-- Shared core of `low/high_collisionMult_cast_le`: the cast bound for the
ceiling `⌊W(m)/D⌋ + 1`, over the abstract log-denominator `D`. -/
theorem collisionMult_cast_le_of {D : ℝ} {m : ℕ} (hD : 0 < D) (hm1 : 1 ≤ m) :
    ((⌊(Real.log 4 * m + Real.sqrt m * Real.log m
          + Real.log (1 + Real.log m)) / D⌋₊ : ℕ) : ℝ) + 1
      ≤ (Real.log 4 * m + Real.sqrt m * Real.log m
          + Real.log (1 + Real.log m)) / D + 1 := by
  have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
  have hlogm0 : (0:ℝ) ≤ Real.log m := Real.log_nonneg hm1'
  have hW0 : (0:ℝ) ≤ Real.log 4 * m + Real.sqrt m * Real.log m
      + Real.log (1 + Real.log m) := by
    have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hs : (0:ℝ) ≤ Real.sqrt m * Real.log m :=
      mul_nonneg (Real.sqrt_nonneg _) hlogm0
    have hl : (0:ℝ) ≤ Real.log (1 + Real.log m) :=
      Real.log_nonneg (by linarith)
    nlinarith
  have hfloor : ((⌊(Real.log 4 * m + Real.sqrt m * Real.log m
        + Real.log (1 + Real.log m)) / D⌋₊ : ℕ) : ℝ)
      ≤ (Real.log 4 * m + Real.sqrt m * Real.log m
          + Real.log (1 + Real.log m)) / D :=
    Nat.floor_le (div_nonneg hW0 hD.le)
  linarith

/-! ### The two-sided FKS shell count (eq. `explicit-shell-count`) -/

/-- Upper shell count: `P_m ≤ (N c_m)/log(N/(m+1)) + 2N/10¹⁰⁰`. -/
theorem low_shell_card_ub (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ lowM X) :
    ((shellPrimes (lowN X) m).card : ℝ)
      ≤ (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1))
          / Real.log ((lowN X:ℝ) / ((m:ℝ) + 1))
        + 2 * (lowN X:ℝ) / 10 ^ 100 := by
  refine shell_card_ub_of hm1 (low_shell_a_ge_two h1 h2 hmM)
    (low_shell_a_le_b h1 hm1) ?_
  linarith [low_fks_a h1 h2 hmM, low_fks_b h1 h2 hm1 hmM]

/-- Lower shell count: `P_m ≥ (N c_m)/X − 2N/10¹⁰⁰`. -/
theorem low_shell_card_lb (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ lowM X) :
    (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / X - 2 * (lowN X:ℝ) / 10 ^ 100
      ≤ ((shellPrimes (lowN X) m).card : ℝ) := by
  refine shell_card_lb_of hm1 (low_shell_a_ge_two h1 h2 hmM)
    (low_shell_a_le_b h1 hm1) (low_logb_pos h1 h2 hm1 hmM) (low_logb_le_X h1 hm1) ?_
  linarith [low_fks_a h1 h2 hmM, low_fks_b h1 h2 hm1 hmM]

/-! ### Shell membership facts -/

theorem low_shell_prime_gt_m (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m p : ℕ} (hmM : m ≤ lowM X) (hp : p ∈ shellPrimes (lowN X) m) :
    m < p := by
  obtain ⟨hlo, -, -⟩ := mem_shellPrimes.mp hp
  have hchain : lowN X / (lowM X + 1) ≤ lowN X / (m + 1) :=
    Nat.div_le_div_left (by omega) (by omega)
  have hQM := low_M_le_Q h1 h2
  omega

theorem low_shell_prime_cast_lb {m p : ℕ}
    (hp : p ∈ shellPrimes (lowN X) m) :
    (lowN X:ℝ) / ((m:ℝ) + 1) < (p:ℝ) := by
  obtain ⟨hlo, -, -⟩ := mem_shellPrimes.mp hp
  have h1 : lowN X < p * (m + 1) :=
    (Nat.div_lt_iff_lt_mul (Nat.succ_pos m)).mp hlo
  have h2 : (lowN X:ℝ) < (p:ℝ) * ((m:ℝ) + 1) := by exact_mod_cast h1
  rw [div_lt_iff₀ (by positivity : (0:ℝ) < (m:ℝ) + 1)]
  exact h2

/-- The per-prime cap: on the `m`-th shell,
`log σ_p(m) ≤ min(g(m), log(N/m))` (paper: `log σ_p(m) ≤ a_m` and
`σ_p(m) ≤ p ≤ N/m`). -/
theorem low_shell_logSum_le_card_mul_cap (h1 : (9.7e6:ℝ) ≤ X)
    (h2 : X ≤ 1.07e7) {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ lowM X) :
    ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ ((shellPrimes (lowN X) m).card : ℝ)
        * min (g m) (Real.log ((lowN X:ℝ) / (m:ℝ))) :=
  shell_logSum_le_card_mul_cap_of hm1
    (fun _p hp => low_shell_prime_gt_m h1 h2 hmM hp)

end ShellEstimates

/-! ## Per-shell upper bounds (eq. `explicit-upper-start`) -/

section UpperShells

variable {X : ℝ}

/-- Generic per-shell upper bound: normalize the capped shell sum by `X/N`
and insert the FKS count, leaving the exact factor
`X·min(g(m), log(N/m)) / (m(m+1)) / log(N/(m+1))` plus uniform junk. -/
theorem low_shell_upper_generic (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ lowM X) :
    X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ X * min (g m) (Real.log ((lowN X:ℝ) / (m:ℝ)))
          / ((m:ℝ) * ((m:ℝ) + 1)) / Real.log ((lowN X:ℝ) / ((m:ℝ) + 1))
        + 300 * X ^ 2 / 10 ^ 100 := by
  have hLpos : (0:ℝ) < Real.log ((lowN X:ℝ) / ((m:ℝ) + 1)) := by
    have := low_loga_ge_X36 h1 h2 hmM
    linarith
  have hmu0 : 0 ≤ min (g m) (Real.log ((lowN X:ℝ) / (m:ℝ))) :=
    le_min (g_nonneg m) (low_logb_pos h1 h2 hm1 hmM).le
  have hmuX : min (g m) (Real.log ((lowN X:ℝ) / (m:ℝ))) ≤ X :=
    le_trans (min_le_right _ _) (low_logb_le_X h1 hm1)
  have hcard : ((shellPrimes (lowN X) m).card : ℝ)
      ≤ (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / Real.log ((lowN X:ℝ) / ((m:ℝ) + 1))
        + 2 * (lowN X:ℝ) * (1 / 10 ^ 100) := by
    have := low_shell_card_ub h1 h2 hm1 hmM
    linarith
  have h := shell_upper_generic_of (Nv := (lowN X:ℝ)) (eps := 1 / 10 ^ 100)
    (low_N_pos h1) (by exact_mod_cast hm1) hLpos hmu0 hmuX (by linarith)
    (by positivity) (low_shell_logSum_le_card_mul_cap h1 h2 hm1 hmM) hcard
  linarith [h]

/-- Per-shell upper bound, head regime `m ≤ T` (the paper's
`∑_{m ≤ T}` term of eq. `explicit-upper-start`): the shell is fully clamped
(`g(m) ≤ m log 2 ≤ X − 36 ≤ log(N/(m+1))`). -/
theorem low_shell_upper_head (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm1 : 1 ≤ m) (hmT : m ≤ lowT X) :
    X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
        + Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9) / (((m:ℝ) + 1) * (X - 36)))
        + 300 * X ^ 2 / 10 ^ 100 := by
  have hmM : m ≤ lowM X := le_trans hmT (low_T_le_M h1 h2)
  have hgeneric := low_shell_upper_generic h1 h2 hm1 hmM
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  exact shell_head_clamp_of hm0 (show (0:ℝ) < X - 36 by linarith)
    (low_loga_ge_X36 h1 h2 hmM) (low_loga_le_X h1)
    (g_le_mul_log_two m) (low_T_mul_log2_le h1 hmT)
    (low_loga_le_logb h1 h2 hm1 hmM) (by linarith [low_loga_lb h1 (m := m)])
    hgeneric

/-- Per-shell upper bound, tail regime `T < m ≤ M` (the paper's `∑_{m > T}`
term of eq. `explicit-upper-start`, with the cap saturated at `X`). -/
theorem low_shell_upper_tail (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hmT : lowT X < m) (hmM : m ≤ lowM X) :
    X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
        + X / (X - 36) * ((Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1)))
        + 300 * X ^ 2 / 10 ^ 100 := by
  have hm1 : 1 ≤ m := le_trans (low_one_le_T h1) hmT.le
  have hgeneric := low_shell_upper_generic h1 h2 hm1 hmM
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hmT' : (13994001:ℝ) ≤ (m:ℝ) := by
    have : (13994000:ℝ) ≤ (lowT X : ℝ) := by exact_mod_cast low_T_lb h1
    have hc : (lowT X : ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hmT
    linarith
  set L := Real.log ((lowN X:ℝ) / ((m:ℝ) + 1)) with hLdef
  have hL36 : X - 36 ≤ L := low_loga_ge_X36 h1 h2 hmM
  -- window-specific overflow numerator bound (the low file's `T ≥ 13994000`
  -- estimate), the only part not shared with the high window
  have hlogb_ub := low_logb_ub h1 hm1
  have hlogm0 : (0:ℝ) ≤ Real.log (m:ℝ) := Real.log_nonneg (by linarith)
  have hdelta : Real.log ((m:ℝ) + 1) - Real.log (m:ℝ) ≤ 1 / (m:ℝ) := by
    have hlogdiv : Real.log ((m:ℝ) + 1) - Real.log (m:ℝ)
        = Real.log (((m:ℝ) + 1) / (m:ℝ)) := by
      rw [Real.log_div (by linarith) hm0.ne']
    rw [hlogdiv]
    have := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < ((m:ℝ) + 1) / (m:ℝ) by positivity)
    have hquot : ((m:ℝ) + 1) / (m:ℝ) - 1 = 1 / (m:ℝ) := by
      field_simp
      ring
    linarith
  have hdelta0 : 0 ≤ Real.log ((m:ℝ) + 1) - Real.log (m:ℝ) := by
    have := Real.log_le_log hm0 (show (m:ℝ) ≤ (m:ℝ) + 1 by linarith)
    linarith
  have hinvm : (1:ℝ) / (m:ℝ) ≤ 1 / 13994001 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmT'
  have hLsq : (X - Real.log ((m:ℝ) + 1) - 1e-9) ^ 2 ≤ L ^ 2 := by
    have hle : X - Real.log ((m:ℝ) + 1) - 1e-9 ≤ L := low_loga_lb h1 (m := m)
    have hD0 : (0:ℝ) < X - Real.log ((m:ℝ) + 1) - 1e-9 := by
      have := low_log_add_one_le_35 h1 h2 hmM
      linarith
    nlinarith
  have hnum : X * Real.log ((lowN X:ℝ) / (m:ℝ)) - L ^ 2
      ≤ X * (Real.log ((m:ℝ) + 1) + 1e-7) := by
    have hb' : X * Real.log ((lowN X:ℝ) / (m:ℝ)) ≤ X * (X - Real.log (m:ℝ)) :=
      mul_le_mul_of_nonneg_left hlogb_ub (by linarith)
    have hexp : X * (X - Real.log (m:ℝ)) - (X - Real.log ((m:ℝ) + 1) - 1e-9) ^ 2
        ≤ X * (Real.log ((m:ℝ) + 1) + 1e-7) := by
      have hXm : X * (1/(m:ℝ)) ≤ X * (1/13994001) :=
        mul_le_mul_of_nonneg_left hinvm (by linarith)
      nlinarith [sq_nonneg (Real.log ((m:ℝ) + 1) + 1e-9), hdelta, hdelta0,
        mul_le_mul_of_nonneg_left hdelta (show (0:ℝ) ≤ X by linarith)]
    nlinarith [hLsq]
  exact shell_upper_tail_of hm0 (show (0:ℝ) < X - 36 by linarith)
    (show (0:ℝ) < X by linarith) hL36 (low_loga_le_X h1)
    (low_loga_le_logb h1 h2 hm1 hmM) (by linarith [low_loga_lb h1 (m := m)])
    hnum hgeneric

end UpperShells

/-! ## Summing the upper per-shell bounds -/

section UpperSums

variable {X : ℝ}

/-- The head sum (paper: `∑_{m ≤ T} ⋯ ≤ (log 2/(X−17))(½log²(T+1)+1) <
1.042·10⁻⁵`; here with denominator `X − 36` and total `≤ 1.041·10⁻⁵`). -/
theorem low_head_sum_le (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    ∑ m ∈ Finset.Icc 1 (lowT X),
        Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9) / (((m:ℝ) + 1) * (X - 36)))
      ≤ 1.041e-5 := by
  have hX36 : (0:ℝ) < X - 36 := by linarith
  have hbound : ∀ m ∈ Finset.Icc 1 (lowT X),
      Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9) / (((m:ℝ) + 1) * (X - 36)))
        ≤ Real.log 2 * Real.log ((m:ℝ) + 1) / ((m:ℝ) + 1) * (1 / (X - 36))
          + 1 / (m:ℝ) * (1e-9 * Real.log 2 / (X - 36)) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
    have hsplit : Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9) / (((m:ℝ) + 1) * (X - 36)))
        = Real.log 2 * Real.log ((m:ℝ) + 1) / ((m:ℝ) + 1) * (1 / (X - 36))
          + 1e-9 * Real.log 2 / (((m:ℝ) + 1) * (X - 36)) := by
      field_simp
    have hmono : 1e-9 * Real.log 2 / (((m:ℝ) + 1) * (X - 36))
        ≤ 1 / (m:ℝ) * (1e-9 * Real.log 2 / (X - 36)) := by
      have hR : 1 / (m:ℝ) * (1e-9 * Real.log 2 / (X - 36))
          = 1e-9 * Real.log 2 / ((m:ℝ) * (X - 36)) := by
        field_simp
      rw [hR]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    rw [hsplit]
    linarith
  have hsum1 := sum_min_cap_error_le (lowT X)
  have hsum2 := sum_one_div_le_log (lowT X)
  have h17 := low_log_T_add_one_ub h1 h2
  have h17' := low_log_T_ub h1 h2
  have hT1 : (1:ℝ) ≤ (lowT X : ℝ) := by exact_mod_cast low_one_le_T h1
  have hlogT0 : (0:ℝ) ≤ Real.log ((lowT X:ℝ) + 1) := Real.log_nonneg (by linarith)
  have hsq : Real.log ((lowT X:ℝ) + 1) ^ 2 ≤ 289 := by nlinarith
  have hlog2u := Real.log_two_lt_d9
  have hlog2l := low_log2_pos
  have hXd : 1 / (X - 36) ≤ 1 / 9699964 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  have hA : Real.log 2 * (Real.log ((lowT X:ℝ) + 1) ^ 2 / 2 + 1)
      ≤ 0.6931472 * 145.5 := by nlinarith
  have hA0 : (0:ℝ) ≤ Real.log 2 * (Real.log ((lowT X:ℝ) + 1) ^ 2 / 2 + 1) := by
    positivity
  have hB : 1 + Real.log (lowT X : ℝ) ≤ 18 := by linarith
  have hB0 : (0:ℝ) ≤ 1 + Real.log (lowT X : ℝ) := by
    have := Real.log_nonneg hT1
    linarith
  have hc' : 1e-9 * Real.log 2 / (X - 36) ≤ 1e-9 * 0.6931472 / 9699964 := by
    have hnum : 1e-9 * Real.log 2 ≤ 1e-9 * 0.6931472 := by nlinarith
    calc 1e-9 * Real.log 2 / (X - 36) ≤ 1e-9 * 0.6931472 / (X - 36) :=
          div_le_div_of_nonneg_right hnum hX36.le
      _ ≤ 1e-9 * 0.6931472 / 9699964 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          linarith
  have hc'0 : (0:ℝ) ≤ 1e-9 * Real.log 2 / (X - 36) := by positivity
  calc ∑ m ∈ Finset.Icc 1 (lowT X),
        Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9) / (((m:ℝ) + 1) * (X - 36)))
      ≤ ∑ m ∈ Finset.Icc 1 (lowT X),
          (Real.log 2 * Real.log ((m:ℝ) + 1) / ((m:ℝ) + 1) * (1 / (X - 36))
            + 1 / (m:ℝ) * (1e-9 * Real.log 2 / (X - 36))) :=
        Finset.sum_le_sum hbound
    _ = (∑ m ∈ Finset.Icc 1 (lowT X),
            Real.log 2 * Real.log ((m:ℝ) + 1) / ((m:ℝ) + 1)) * (1 / (X - 36))
        + (∑ m ∈ Finset.Icc 1 (lowT X), 1 / (m:ℝ))
            * (1e-9 * Real.log 2 / (X - 36)) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ Real.log 2 * (Real.log ((lowT X:ℝ) + 1) ^ 2 / 2 + 1) * (1 / (X - 36))
        + (1 + Real.log (lowT X : ℝ)) * (1e-9 * Real.log 2 / (X - 36)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hsum1 (by positivity)
        · exact mul_le_mul_of_nonneg_right hsum2 hc'0
    _ ≤ 0.6931472 * 145.5 * (1 / 9699964) + 18 * (1e-9 * 0.6931472 / 9699964) := by
        apply add_le_add
        · exact mul_le_mul hA hXd (by positivity) (by norm_num)
        · exact mul_le_mul hB hc' hc'0 (by norm_num)
    _ ≤ 1.041e-5 := by norm_num

/-- The tail sum (paper: `∑_{m > T} ⋯ ≤ (X/(X−34))((log T + 1)/T + 1/(2T²)) <
1.287·10⁻⁶`; here `≤ 1.3·10⁻⁶`). -/
theorem low_tail_sum_le (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    ∑ m ∈ Finset.Ioc (lowT X) (lowM X),
        X / (X - 36) * ((Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1)))
      ≤ 1.3e-6 := by
  have hX36 : (0:ℝ) < X - 36 := by linarith
  have hXX := low_X_div_X36_ub h1
  have hT0 : (13994000:ℝ) ≤ (lowT X : ℝ) := by exact_mod_cast low_T_lb h1
  rw [← Finset.mul_sum]
  have hterm : ∀ m ∈ Finset.Ioc (lowT X) (lowM X),
      (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ (1 + 1/13994001) * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1)))
          + 1e-7 * (1 / ((m:ℝ) * (m:ℝ))) := by
    intro m hm
    have hmT : lowT X < m := (Finset.mem_Ioc.mp hm).1
    have hm' : (13994001:ℝ) ≤ (m:ℝ) := by
      have : (lowT X:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hmT
      linarith
    have hm0 : (0:ℝ) < (m:ℝ) := by linarith
    have hL0 : (0:ℝ) ≤ Real.log ((m:ℝ) + 1) := Real.log_nonneg (by linarith)
    have hsplit : (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))
        = Real.log ((m:ℝ) + 1) / ((m:ℝ) * ((m:ℝ) + 1))
          + 1e-7 / ((m:ℝ) * ((m:ℝ) + 1)) := by
      rw [add_div]
    have hpiece1 : Real.log ((m:ℝ) + 1) / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ (1 + 1/13994001) * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1))) := by
      have hw : (1:ℝ) / ((m:ℝ) * ((m:ℝ) + 1))
          ≤ (1 + 1/13994001) / (((m:ℝ) + 1) * ((m:ℝ) + 1)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc Real.log ((m:ℝ) + 1) / ((m:ℝ) * ((m:ℝ) + 1))
          = Real.log ((m:ℝ) + 1) * (1 / ((m:ℝ) * ((m:ℝ) + 1))) := by
            rw [mul_one_div]
        _ ≤ Real.log ((m:ℝ) + 1) * ((1 + 1/13994001) / (((m:ℝ) + 1) * ((m:ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hw hL0
        _ = (1 + 1/13994001) * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1))) := by
            field_simp
    have hpiece2 : (1e-7:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) ≤ 1e-7 * (1 / ((m:ℝ) * (m:ℝ))) := by
      rw [mul_one_div]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    rw [hsplit]
    linarith
  have hsum1 := sum_log_div_sq_tail_le (lowT X) (lowM X)
    (le_trans (by norm_num) (low_T_lb h1))
  have hsum2 := sum_one_div_Ioc_le (lowT X) (lowM X) (low_one_le_T h1)
  have h17 := low_log_T_add_one_ub h1 h2
  have hinner : ∑ m ∈ Finset.Ioc (lowT X) (lowM X),
      (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1)) ≤ 1.2999e-6 := by
    have hs1' : (Real.log ((lowT X:ℝ) + 1) + 1) / ((lowT X:ℝ) + 1)
        ≤ 18 / 13994001 := by
      calc (Real.log ((lowT X:ℝ) + 1) + 1) / ((lowT X:ℝ) + 1)
          ≤ 18 / ((lowT X:ℝ) + 1) :=
            div_le_div_of_nonneg_right (by linarith) (by linarith)
        _ ≤ 18 / 13994001 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
            linarith
    have hs2' : (1:ℝ) / (lowT X : ℝ) ≤ 1 / 13994000 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    calc ∑ m ∈ Finset.Ioc (lowT X) (lowM X),
          (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ ∑ m ∈ Finset.Ioc (lowT X) (lowM X),
            ((1 + 1/13994001) * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1)))
              + 1e-7 * (1 / ((m:ℝ) * (m:ℝ)))) := Finset.sum_le_sum hterm
      _ = (1 + 1/13994001) * ∑ m ∈ Finset.Ioc (lowT X) (lowM X),
            Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1))
          + 1e-7 * ∑ m ∈ Finset.Ioc (lowT X) (lowM X), 1 / ((m:ℝ) * (m:ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (1 + 1/13994001) * (18 / 13994001) + 1e-7 * (1 / 13994000) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (by norm_num)
            linarith [hsum1, hs1']
          · apply mul_le_mul_of_nonneg_left _ (by norm_num)
            linarith [hsum2, hs2']
      _ ≤ 1.2999e-6 := by norm_num
  have hinner0 : (0:ℝ) ≤ ∑ m ∈ Finset.Ioc (lowT X) (lowM X),
      (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1)) := by
    apply Finset.sum_nonneg
    intro m hm
    have hmT : lowT X < m := (Finset.mem_Ioc.mp hm).1
    have hm0 : (0:ℝ) < (m:ℝ) := by
      have : 1 ≤ m := by
        have := low_one_le_T h1
        omega
      exact_mod_cast this
    have : (0:ℝ) ≤ Real.log ((m:ℝ) + 1) := Real.log_nonneg (by linarith)
    positivity
  calc X / (X - 36) * ∑ m ∈ Finset.Ioc (lowT X) (lowM X),
        (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))
      ≤ 1.0000038 * 1.2999e-6 := mul_le_mul hXX hinner hinner0 (by norm_num)
    _ ≤ 1.3e-6 := by norm_num

/-- The junk total: `M` shells, each carrying at most `300X²/10¹⁰⁰`. -/
theorem low_junk_total_le (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    (lowM X : ℝ) * (300 * X ^ 2 / 10 ^ 100) ≤ 1e-8 := by
  have hM := low_M_ub h1 h2
  have hM0 : (0:ℝ) ≤ (lowM X : ℝ) := Nat.cast_nonneg _
  have hXsq : X ^ 2 ≤ 1.2e14 := by nlinarith
  have hj : 300 * X ^ 2 / 10 ^ 100 ≤ 300 * 1.2e14 / 10 ^ 100 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    nlinarith
  calc (lowM X : ℝ) * (300 * X ^ 2 / 10 ^ 100)
      ≤ 1.59e15 * (300 * 1.2e14 / 10 ^ 100) := by
        apply mul_le_mul hM hj (by positivity) (by norm_num)
    _ ≤ 1e-8 := by norm_num

/-- The full upper shell-sum estimate: after normalization by `X/N`, the
shell sums exceed the truncated `𝓑`-sum by at most
`1.041·10⁻⁵ + 1.3·10⁻⁶ + 10⁻⁸`. -/
theorem low_sum_upper (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    X / (lowN X:ℝ)
        * ∑ m ∈ Finset.Icc 1 (lowM X),
            ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ (∑ m ∈ Finset.Icc 1 (lowM X), min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)))
        + (1.041e-5 + 1.3e-6 + 1e-8) := by
  have hTM := low_T_le_M h1 h2
  have hunion : Finset.Icc 1 (lowM X)
      = Finset.Icc 1 (lowT X) ∪ Finset.Ioc (lowT X) (lowM X) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (lowT X)) (Finset.Ioc (lowT X) (lowM X)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1
    simp only [Finset.mem_Ioc] at hk2
    omega
  rw [Finset.mul_sum, hunion, Finset.sum_union hdisj, Finset.sum_union hdisj]
  have hhead : ∑ m ∈ Finset.Icc 1 (lowT X),
      X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ (∑ m ∈ Finset.Icc 1 (lowT X), min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)))
        + ((∑ m ∈ Finset.Icc 1 (lowT X),
            Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9) / (((m:ℝ) + 1) * (X - 36))))
          + ∑ _m ∈ Finset.Icc 1 (lowT X), 300 * X ^ 2 / 10 ^ 100) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro m hm
    have hmem := Finset.mem_Icc.mp hm
    linarith [low_shell_upper_head h1 h2 hmem.1 hmem.2]
  have htail : ∑ m ∈ Finset.Ioc (lowT X) (lowM X),
      X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ (∑ m ∈ Finset.Ioc (lowT X) (lowM X), min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)))
        + ((∑ m ∈ Finset.Ioc (lowT X) (lowM X),
            X / (X - 36) * ((Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))))
          + ∑ _m ∈ Finset.Ioc (lowT X) (lowM X), 300 * X ^ 2 / 10 ^ 100) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro m hm
    have hmem := Finset.mem_Ioc.mp hm
    linarith [low_shell_upper_tail h1 h2 hmem.1 hmem.2]
  have hheadsum := low_head_sum_le h1 h2
  have htailsum := low_tail_sum_le h1 h2
  have hjunk : (∑ _m ∈ Finset.Icc 1 (lowT X), 300 * X ^ 2 / 10 ^ 100)
      + (∑ _m ∈ Finset.Ioc (lowT X) (lowM X), 300 * X ^ 2 / 10 ^ 100) ≤ 1e-8 := by
    rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, Nat.card_Ioc,
      nsmul_eq_mul, nsmul_eq_mul]
    have hcast : ((lowT X + 1 - 1 : ℕ) : ℝ) + ((lowM X - lowT X : ℕ) : ℝ)
        = (lowM X : ℝ) := by
      rw [Nat.cast_sub hTM]
      simp
    have hj0 : (0:ℝ) ≤ 300 * X ^ 2 / 10 ^ 100 := by positivity
    calc ((lowT X + 1 - 1 : ℕ) : ℝ) * (300 * X ^ 2 / 10 ^ 100)
          + ((lowM X - lowT X : ℕ) : ℝ) * (300 * X ^ 2 / 10 ^ 100)
        = (lowM X : ℝ) * (300 * X ^ 2 / 10 ^ 100) := by
          rw [← add_mul, hcast]
      _ ≤ 1e-8 := low_junk_total_le h1 h2
  linarith

end UpperSums

/-! ## The fibre core, the normalization bridge, and the `𝓑`-truncation -/

section CoreBridge

variable {X : ℝ}

/-- The normalized fibre cost (eq. `explicit-core`, `< 10⁻⁷`): harmonic
factor plus smooth denominator at scale `Q = ⌊N/(M+1)⌋`. -/
theorem low_core (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    X / (lowN X:ℝ) * (Real.log ((harmonicSum (lowN X) : ℝ) + 1)
        + Real.log (smoothPart (lowN X / (lowM X + 1)) (lowN X))) ≤ 1e-7 := by
  have hNpos := low_N_pos h1
  have hN := low_N_lb h1
  have hH0 : (0:ℝ) ≤ ((harmonicSum (lowN X) : ℚ) : ℝ) := by
    exact_mod_cast harmonicSum_nonneg (lowN X)
  have hH : Real.log ((harmonicSum (lowN X) : ℝ) + 1) ≤ 17 := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    have hHle : ((harmonicSum (lowN X) : ℚ) : ℝ) ≤ 1 + Real.log (lowN X) :=
      harmonicSum_le_one_add_log (lowN X)
    linarith [low_logN_ub h1, low_exp_17_lb]
  have hD : Real.log (smoothPart (lowN X / (lowM X + 1)) (lowN X))
      ≤ Real.log 4 * ((lowN X / (lowM X + 1) : ℕ) : ℝ)
        + Real.sqrt (lowN X) * X := by
    have hsmooth := log_smoothPart_le (low_two_le_Q h1 h2)
      (Nat.div_le_self (lowN X) (lowM X + 1))
    have hth := chebyshevTheta_le_log_four_mul
      (Nat.cast_nonneg (lowN X / (lowM X + 1)) : (0:ℝ) ≤ _)
    have hsqrtlog : Real.sqrt (lowN X) * Real.log (lowN X)
        ≤ Real.sqrt (lowN X) * X :=
      mul_le_mul_of_nonneg_left (low_logN_ub h1) (Real.sqrt_nonneg _)
    linarith
  have hXN0 : (0:ℝ) ≤ X / (lowN X:ℝ) := by positivity
  have hstep : X / (lowN X:ℝ) * (Real.log ((harmonicSum (lowN X) : ℝ) + 1)
        + Real.log (smoothPart (lowN X / (lowM X + 1)) (lowN X)))
      ≤ X / (lowN X:ℝ) * (17 + (Real.log 4 * ((lowN X / (lowM X + 1) : ℕ) : ℝ)
          + Real.sqrt (lowN X) * X)) := by
    apply mul_le_mul_of_nonneg_left _ hXN0
    linarith
  -- three pieces
  have hpiece1 : X / (lowN X:ℝ) * 17 ≤ 1e-9 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]
    have : (1.9e17:ℝ) ≤ (10:ℝ) ^ (209:ℕ) := by norm_num
    nlinarith
  have hQle : ((lowN X / (lowM X + 1) : ℕ) : ℝ) ≤ (lowN X:ℝ) / ((lowM X:ℝ) + 1) := by
    have := Nat.cast_div_le (m := lowN X) (n := lowM X + 1) (α := ℝ)
    push_cast at this
    linarith
  have hlog4 : Real.log 4 ≤ 1.3862943616 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_lt_d9]
  have hlog4pos : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hpiece2 : X / (lowN X:ℝ)
      * (Real.log 4 * ((lowN X / (lowM X + 1) : ℕ) : ℝ)) ≤ 8.1e-8 := by
    have hM1 := low_M_add_one_lb h1
    have hMpos : (0:ℝ) < (lowM X:ℝ) + 1 := by positivity
    have hchain : X / (lowN X:ℝ) * (Real.log 4 * ((lowN X / (lowM X + 1) : ℕ) : ℝ))
        ≤ X / (lowN X:ℝ) * (Real.log 4 * ((lowN X:ℝ) / ((lowM X:ℝ) + 1))) := by
      apply mul_le_mul_of_nonneg_left _ hXN0
      exact mul_le_mul_of_nonneg_left hQle hlog4pos
    have hid : X / (lowN X:ℝ) * (Real.log 4 * ((lowN X:ℝ) / ((lowM X:ℝ) + 1)))
        = X * Real.log 4 / ((lowM X:ℝ) + 1) := by
      field_simp
    have hfinal : X * Real.log 4 / ((lowM X:ℝ) + 1) ≤ 8.1e-8 := by
      rw [div_le_iff₀ hMpos]
      nlinarith
    linarith [hid ▸ hchain]
  have hpiece3 : X / (lowN X:ℝ) * (Real.sqrt (lowN X) * X) ≤ 1e-9 := by
    have hsqrt_lb : (10:ℝ) ^ (104:ℕ) ≤ Real.sqrt (lowN X) := by
      have hsq : ((10:ℝ) ^ (104:ℕ)) ^ 2 ≤ (lowN X:ℝ) := by
        have : ((10:ℝ) ^ (104:ℕ)) ^ 2 = (10:ℝ) ^ (208:ℕ) := by
          rw [← pow_mul]
        rw [this]
        calc (10:ℝ) ^ (208:ℕ) ≤ (10:ℝ) ^ (209:ℕ) := by
              apply pow_le_pow_right₀ (by norm_num) (by norm_num)
          _ ≤ (lowN X:ℝ) := hN
      calc (10:ℝ) ^ (104:ℕ) = Real.sqrt (((10:ℝ) ^ (104:ℕ)) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (lowN X) := Real.sqrt_le_sqrt hsq
    have hNs : Real.sqrt (lowN X) * Real.sqrt (lowN X) = (lowN X:ℝ) :=
      Real.mul_self_sqrt hNpos.le
    have hsqrtN : Real.sqrt (lowN X) ≤ (lowN X:ℝ) / (10:ℝ) ^ (104:ℕ) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < (10:ℝ) ^ (104:ℕ))]
      calc Real.sqrt (lowN X) * (10:ℝ) ^ (104:ℕ)
          ≤ Real.sqrt (lowN X) * Real.sqrt (lowN X) :=
            mul_le_mul_of_nonneg_left hsqrt_lb (Real.sqrt_nonneg _)
        _ = (lowN X:ℝ) := hNs
    have hchain : X / (lowN X:ℝ) * (Real.sqrt (lowN X) * X)
        ≤ X / (lowN X:ℝ) * ((lowN X:ℝ) / (10:ℝ) ^ (104:ℕ) * X) := by
      apply mul_le_mul_of_nonneg_left _ hXN0
      exact mul_le_mul_of_nonneg_right hsqrtN (by linarith)
    have hid : X / (lowN X:ℝ) * ((lowN X:ℝ) / (10:ℝ) ^ (104:ℕ) * X)
        = X ^ 2 / (10:ℝ) ^ (104:ℕ) := by
      field_simp
    have hfinal : X ^ 2 / (10:ℝ) ^ (104:ℕ) ≤ 1e-9 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (10:ℝ) ^ (104:ℕ))]
      have : (1.2e14:ℝ) ≤ 1e-9 * (10:ℝ) ^ (104:ℕ) := by norm_num
      nlinarith
    linarith [hid ▸ hchain]
  have hexpand : X / (lowN X:ℝ) * (17 + (Real.log 4 * ((lowN X / (lowM X + 1) : ℕ) : ℝ)
        + Real.sqrt (lowN X) * X))
      = X / (lowN X:ℝ) * 17
        + X / (lowN X:ℝ) * (Real.log 4 * ((lowN X / (lowM X + 1) : ℕ) : ℝ))
        + X / (lowN X:ℝ) * (Real.sqrt (lowN X) * X) := by
    ring
  rw [hexpand] at hstep
  linarith

/-- The normalization bridge: `|F(e^X) − (X/N)·g(N)| ≤ 10⁻⁹` on the window
(the paper's "The use of `N` in place of `e^X` … fit(s) in the same
allowance"). -/
theorem low_bridge (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    |FReal (Real.exp X) - X / (lowN X:ℝ) * g (lowN X)| ≤ 1e-9 := by
  have h := abs_FReal_exp_sub_div_floor (show (1:ℝ) ≤ X by linarith)
  have hbound : X * Real.log 2 / Real.exp X ≤ 1e-9 := by
    have hnum : X * Real.log 2 ≤ 7.5e6 := by
      nlinarith [Real.log_two_lt_d9, low_log2_pos]
    have hEpos : (0:ℝ) < Real.exp X := Real.exp_pos X
    rw [div_le_iff₀ hEpos]
    have h10 : (7.5e15:ℝ) ≤ (10:ℝ) ^ (210:ℕ) := by norm_num
    nlinarith [low_exp_X_lb h1]
  exact le_trans h hbound

/-- `BTerm` is nonnegative for nonnegative cap. -/
theorem low_BTerm_nonneg {Xv : ℝ} (hX : 0 ≤ Xv) (i : ℕ) : 0 ≤ BTerm Xv i := by
  rw [BTerm]
  apply div_nonneg _ (by positivity)
  exact le_min (g_nonneg _) hX

/-- The truncated `𝓑`-sum over `1 ≤ m ≤ M'` is the `range`-indexed partial
sum of the `BTerm` series. -/
theorem low_partial_eq (Xv : ℝ) (M' : ℕ) :
    ∑ m ∈ Finset.Icc 1 M', min (g m) Xv / ((m:ℝ) * ((m:ℝ) + 1))
      = ∑ i ∈ Finset.range M', BTerm Xv i := by
  have hIcc : Finset.Icc 1 M' = Finset.Ico 1 (M' + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i _
  have h1i : 1 + i = i + 1 := Nat.add_comm 1 i
  rw [h1i, BTerm]
  push_cast
  ring_nf

/-- The truncated `𝓑`-sum is at most `𝓑(X)` (all terms are nonnegative). -/
theorem low_partial_le_B (hX : 0 ≤ X) (M' : ℕ) :
    ∑ m ∈ Finset.Icc 1 M', min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)) ≤ B X := by
  rw [low_partial_eq]
  exact Summable.sum_le_tsum _ (fun i _ => low_BTerm_nonneg hX i) (summable_BTerm X)

/-- `𝓑(X)` exceeds its truncation at `M'` by at most the tail `X/(M'+1)`
(the paper's `∑_{m>M} X c_m = X/(M+1)`). -/
theorem low_B_le_partial_add_tail (M' : ℕ) :
    B X ≤ (∑ m ∈ Finset.Icc 1 M', min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)))
      + X / ((M':ℝ) + 1) := by
  rw [low_partial_eq]
  have hsplit := (summable_BTerm X).sum_add_tsum_nat_add M'
  have hshift_sum : Summable (fun i => BTerm X (i + M')) :=
    (summable_nat_add_iff M').mpr (summable_BTerm X)
  have hw_sum : Summable (fun i => weightTail (M' + 1) (i + M')) :=
    (summable_nat_add_iff M').mpr (summable_weightTail (M' + 1))
  have htail : (∑' i, BTerm X (i + M')) ≤ X / ((M':ℝ) + 1) := by
    have hbound : ∀ i, BTerm X (i + M') ≤ X * weightTail (M' + 1) (i + M') := by
      intro i
      rw [BTerm, weightTail, if_pos (by omega : M' + 1 ≤ i + M' + 1)]
      rw [mul_one_div]
      apply div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
    have htsum_w : (∑' i, weightTail (M' + 1) (i + M')) = 1 / ((M':ℝ) + 1) := by
      have h := (summable_weightTail (M' + 1)).sum_add_tsum_nat_add M'
      rw [tsum_weightTail (by omega : 1 ≤ M' + 1)] at h
      have hzero : ∑ i ∈ Finset.range M', weightTail (M' + 1) i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hiM : i < M' := Finset.mem_range.mp hi
        rw [weightTail, if_neg (by omega)]
      rw [hzero, zero_add] at h
      rw [h]
      push_cast
      ring
    calc (∑' i, BTerm X (i + M'))
        ≤ ∑' i, X * weightTail (M' + 1) (i + M') :=
          Summable.tsum_le_tsum hbound hshift_sum (hw_sum.mul_left X)
      _ = X * ∑' i, weightTail (M' + 1) (i + M') := tsum_mul_left
      _ = X / ((M':ℝ) + 1) := by rw [htsum_w, mul_one_div]
  have hB : B X = (∑ i ∈ Finset.range M', BTerm X i) + ∑' i, BTerm X (i + M') := by
    rw [B]
    exact hsplit.symm
  linarith

end CoreBridge

/-! ## The upper half of eq. `explicit-low-averaging` -/

/-- **Upper explicit averaging bound** (`lem:explicit-low-averaging`, upper
half): `𝓡(X) < 1.19·10⁻⁵` for `9.7·10⁶ ≤ X ≤ 1.07·10⁷`. -/
theorem explicit_low_averaging_upper {X : ℝ} (h1 : (9.7e6:ℝ) ≤ X)
    (h2 : X ≤ 1.07e7) : averagingError X < 1.19e-5 := by
  have hbridge := low_bridge h1 h2
  have hdec := (g_shell_decomposition (N := lowN X) (M := lowM X)
    (low_hQN h1) (low_hQ2 h1 h2)).2
  have hcore := low_core h1 h2
  have hsum := low_sum_upper h1 h2
  have hpartial := low_partial_le_B (show (0:ℝ) ≤ X by linarith) (lowM X)
  have hXN0 : (0:ℝ) ≤ X / (lowN X:ℝ) :=
    div_nonneg (by linarith) (low_N_pos h1).le
  have hmul := mul_le_mul_of_nonneg_left hdec hXN0
  have hexpand : X / (lowN X:ℝ)
        * ((∑ m ∈ Finset.Icc 1 (lowM X),
              ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m))
          + Real.log ((harmonicSum (lowN X) : ℝ) + 1)
          + Real.log (smoothPart (lowN X / (lowM X + 1)) (lowN X)))
      = X / (lowN X:ℝ)
          * ∑ m ∈ Finset.Icc 1 (lowM X),
              ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
        + X / (lowN X:ℝ) * (Real.log ((harmonicSum (lowN X) : ℝ) + 1)
            + Real.log (smoothPart (lowN X / (lowM X + 1)) (lowN X))) := by
    ring
  have hF : FReal (Real.exp X) ≤ X / (lowN X:ℝ) * g (lowN X) + 1e-9 := by
    linarith [(abs_le.mp hbridge).2]
  rw [averagingError]
  rw [hexpand] at hmul
  linarith

/-! ## Per-shell lower bounds (eq. `explicit-collision`) -/

section LowerShells

variable {X : ℝ}

/-- The collision multiplicity `b_m = lowCollisionMult X m` satisfies the
`hb` hypothesis of `shell_collision_lower` (eq. `explicit-bm`). -/
theorem low_collision_hb (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ lowM X) :
    Real.log ((((Finset.Icc 1 m).lcm id : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ))
        / Real.log ((lowN X : ℝ) / ((m : ℝ) + 1))
      ≤ (lowCollisionMult X m : ℝ) := by
  have hcast : (lowCollisionMult X m : ℝ)
      = ((⌊(Real.log 4 * m + Real.sqrt m * Real.log m
          + Real.log (1 + Real.log m)) / (X - 36)⌋₊ : ℕ) : ℝ) + 1 := by
    rw [lowCollisionMult]
    push_cast
    ring
  rw [hcast]
  exact collision_hb_of hm1 (by linarith) (low_loga_ge_X36 h1 h2 hmM)

/-- Cast bound for the collision multiplicity. -/
theorem low_collisionMult_cast_le (h1 : (9.7e6:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m) :
    (lowCollisionMult X m : ℝ)
      ≤ (Real.log 4 * m + Real.sqrt m * Real.log m
          + Real.log (1 + Real.log m)) / (X - 36) + 1 := by
  have hcast : (lowCollisionMult X m : ℝ)
      = ((⌊(Real.log 4 * m + Real.sqrt m * Real.log m
          + Real.log (1 + Real.log m)) / (X - 36)⌋₊ : ℕ) : ℝ) + 1 := by
    rw [lowCollisionMult]
    push_cast
    ring
  rw [hcast]
  exact collisionMult_cast_le_of (by linarith) hm1

/-- Sharp lower shell count with the `log(N/m)` denominator (the form the
collision positive term consumes). -/
theorem low_shell_card_lb_sharp (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ lowM X) :
    (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / Real.log ((lowN X:ℝ) / (m:ℝ))
        - 2 * (lowN X:ℝ) / 10 ^ 100
      ≤ ((shellPrimes (lowN X) m).card : ℝ) := by
  refine shell_card_lb_sharp_of hm1 (low_shell_a_ge_two h1 h2 hmM)
    (low_shell_a_le_b h1 hm1) ?_
  linarith [low_fks_a h1 h2 hmM, low_fks_b h1 h2 hm1 hmM]

/-- Crude but positive lower shell count: `P_m ≥ N c_m/(2X) > 0`. -/
theorem low_shell_card_half_lb (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ lowM X) :
    (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / (2 * X)
      ≤ ((shellPrimes (lowN X) m).card : ℝ) := by
  have hlb := low_shell_card_lb h1 h2 hm1 hmM
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hmub : (m:ℝ) ≤ 1.59e15 := by
    have : (m:ℝ) ≤ (lowM X:ℝ) := Nat.cast_le.mpr hmM
    linarith [low_M_ub h1 h2]
  have hX0 : (0:ℝ) < X := by linarith
  have hN0 : (0:ℝ) ≤ (lowN X:ℝ) := (low_N_pos h1).le
  have hdd : (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / (2 * X)
      = (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1) * (2 * X)) := by
    rw [div_div]
  have hdd' : (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / X
      = (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1) * X) := by
    rw [div_div]
  have h2N : 2 * (lowN X:ℝ) / 10 ^ 100
      ≤ (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1) * (2 * X)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have hprod : (m:ℝ) * ((m:ℝ) + 1) * (2 * X) * 2 ≤ 10 ^ 100 := by
      have hm1' : (m:ℝ) + 1 ≤ 1.6e15 := by linarith
      have hstep : (m:ℝ) * ((m:ℝ) + 1) ≤ 1.59e15 * 1.6e15 :=
        mul_le_mul hmub hm1' (by positivity) (by norm_num)
      have h2X : 2 * X ≤ 2.2e7 := by linarith
      have hstep2 : (m:ℝ) * ((m:ℝ) + 1) * (2 * X) ≤ 1.59e15 * 1.6e15 * 2.2e7 :=
        mul_le_mul hstep h2X (by positivity) (by norm_num)
      have hbig : (1.59e15 * 1.6e15 * 2.2e7 * 2 : ℝ) ≤ 10 ^ 100 := by norm_num
      linarith
    nlinarith
  have hhalf : (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1) * (2 * X))
        + (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1) * (2 * X))
      = (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1) * X) := by
    field_simp
    ring
  rw [hdd]
  rw [hdd'] at hlb
  linarith

/-- The `m`-th shell is nonempty on the window. -/
theorem low_shell_nonempty (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ lowM X) :
    (shellPrimes (lowN X) m).Nonempty := by
  have hlb := low_shell_card_half_lb h1 h2 hm1 hmM
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hpos : (0:ℝ) < (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / (2 * X) := by
    have := low_N_pos h1
    have : (0:ℝ) < X := by linarith
    positivity
  have hcard : 0 < (shellPrimes (lowN X) m).card := by
    by_contra hc
    have h0 : (shellPrimes (lowN X) m).card = 0 := by omega
    rw [h0] at hlb
    norm_num at hlb
    linarith
  exact Finset.card_pos.mp hcard

/-- **Per-shell collision lower bound** — eq. `collision-sum` specialized to
the window and combined with the deficit transfer of eq. `explicit-collision`
and the two-sided FKS shell counts: the normalized shell sum falls short of
`min(g(m), X)·c_m` by at most the deficit factor plus uniform junk. -/
theorem low_shell_collision (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ lowM X) :
    min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
      - (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100)
          * Real.log (1 + 4 * (lowCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
              * Real.exp (min ((m:ℝ) * Real.log 2) X - X))
      - 2 * X ^ 2 / 10 ^ 100
      ≤ X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m) := by
  have hX0 : (0:ℝ) < X := by linarith
  have hX36 : (0:ℝ) < X - 36 := by linarith
  have hNpos := low_N_pos h1
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hcm0 : (0:ℝ) < (m:ℝ) * ((m:ℝ) + 1) := by positivity
  set c : ℝ := ((shellPrimes (lowN X) m).card : ℝ) with hcdef
  set bR : ℝ := (lowCollisionMult X m : ℝ) with hbRdef
  set Y : ℝ := Real.log ((lowN X:ℝ) / (m:ℝ)) with hYdef
  set Lg : ℝ := Real.log ((lowN X:ℝ) / ((m:ℝ) + 1)) with hLgdef
  have hYpos : (0:ℝ) < Y := low_logb_pos h1 h2 hm1 hmM
  have hYX : Y ≤ X := low_logb_le_X h1 hm1
  have hLg36 : X - 36 ≤ Lg := low_loga_ge_X36 h1 h2 hmM
  have hLgpos : (0:ℝ) < Lg := by linarith
  have hbR0 : (0:ℝ) ≤ bR := Nat.cast_nonneg _
  have hclow := low_shell_card_half_lb h1 h2 hm1 hmM
  have hPlow_pos : (0:ℝ) < (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / (2 * X) := by
    positivity
  have hc_pos : (0:ℝ) < c := lt_of_lt_of_le hPlow_pos hclow
  -- the collision bound
  have hcol := shell_collision_lower (N := lowN X) (m := m)
    (shellPrimes (lowN X) m) (low_shell_nonempty h1 h2 hm1 hmM)
    (fun p hp => (mem_shellPrimes.mp hp).2.2)
    (fun p hp => low_shell_prime_gt_m h1 h2 hmM hp)
    (fun p hp => low_shell_prime_cast_lb hp)
    (lt_of_lt_of_le (by norm_num) (low_shell_a_ge_two h1 h2 hmM))
    (lowCollisionMult X m) (low_collision_hb h1 h2 hm1 hmM)
  -- the deficit transfer
  have hS1 : (1:ℝ) ≤ ((S m : ℕ) : ℝ) := by exact_mod_cast one_le_S m
  have hgc : Real.log ((S m : ℕ) : ℝ) ≤ (m:ℝ) * Real.log 2 := g_le_mul_log_two m
  have htrans := low_deficit_transfer (P := c) (bR := bR)
    (S := ((S m : ℕ) : ℝ)) (Y := Y) (c₁ := (m:ℝ) * Real.log 2) (c₂ := X)
    hc_pos hS1 hbR0 hgc hYX
  have hg_eq : g m = Real.log ((S m : ℕ) : ℝ) := rfl
  rw [← hg_eq] at htrans
  -- chain: c·(min(g,Y) − ℓ') ≤ c·(g − ℓ) ≤ Σ
  have hchain : c * (min (g m) Y
        - Real.log (1 + bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c))
      ≤ ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m) :=
    le_trans (mul_le_mul_of_nonneg_left htrans hc_pos.le) hcol
  have hXN0 : (0:ℝ) ≤ X / (lowN X:ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hchain hXN0
  have hexpand : X / (lowN X:ℝ) * (c * (min (g m) Y
        - Real.log (1 + bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c)))
      = X / (lowN X:ℝ) * c * min (g m) Y
        - X / (lowN X:ℝ) * c
          * Real.log (1 + bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c) := by
    ring
  rw [hexpand] at hmul
  -- positive part: (X/N)·c·min(g,Y) ≥ min(g,X)/(m(m+1)) − 2X²/10¹⁰⁰
  have hmin0 : (0:ℝ) ≤ min (g m) Y := le_min (g_nonneg m) hYpos.le
  have hminX : min (g m) Y ≤ X := le_trans (min_le_right _ _) hYX
  have hpos_part : min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)) - 2 * X ^ 2 / 10 ^ 100
      ≤ X / (lowN X:ℝ) * c * min (g m) Y := by
    have hclb := low_shell_card_lb_sharp h1 h2 hm1 hmM
    have hE : X / (lowN X:ℝ)
          * ((lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / Y - 2 * (lowN X:ℝ) / 10 ^ 100)
        ≤ X / (lowN X:ℝ) * c := mul_le_mul_of_nonneg_left hclb hXN0
    have hidE : X / (lowN X:ℝ)
          * ((lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / Y - 2 * (lowN X:ℝ) / 10 ^ 100)
        = X / Y * (1 / ((m:ℝ) * ((m:ℝ) + 1))) - 2 * X / 10 ^ 100 := by
      field_simp
    rw [hidE] at hE
    have hmul2 : (X / Y * (1 / ((m:ℝ) * ((m:ℝ) + 1))) - 2 * X / 10 ^ 100)
          * min (g m) Y
        ≤ X / (lowN X:ℝ) * c * min (g m) Y :=
      mul_le_mul_of_nonneg_right hE hmin0
    have htransport := low_cap_transport_free hYpos hYX (g_nonneg m)
    have hexp2 : (X / Y * (1 / ((m:ℝ) * ((m:ℝ) + 1))) - 2 * X / 10 ^ 100)
          * min (g m) Y
        = X / Y * min (g m) Y * (1 / ((m:ℝ) * ((m:ℝ) + 1)))
          - 2 * X / 10 ^ 100 * min (g m) Y := by
      ring
    have hjunk2 : 2 * X / 10 ^ 100 * min (g m) Y ≤ 2 * X ^ 2 / 10 ^ 100 := by
      have h2X0 : (0:ℝ) ≤ 2 * X / 10 ^ 100 := by positivity
      calc 2 * X / 10 ^ 100 * min (g m) Y ≤ 2 * X / 10 ^ 100 * X :=
            mul_le_mul_of_nonneg_left hminX h2X0
        _ = 2 * X ^ 2 / 10 ^ 100 := by ring
    have hcap2 : min (g m) X * (1 / ((m:ℝ) * ((m:ℝ) + 1)))
        ≤ X / Y * min (g m) Y * (1 / ((m:ℝ) * ((m:ℝ) + 1))) :=
      mul_le_mul_of_nonneg_right htransport (by positivity)
    have hdivform : min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
        = min (g m) X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) := by
      rw [mul_one_div]
    rw [hdivform]
    linarith [hexp2 ▸ hmul2]
  -- deficit part
  have harg_pos : (0:ℝ) < 1 + bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c := by
    have : (0:ℝ) ≤ bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c := by positivity
    linarith
  have hdef_nonneg : (0:ℝ)
      ≤ Real.log (1 + bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c) := by
    apply Real.log_nonneg
    have : (0:ℝ) ≤ bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c := by positivity
    linarith
  have hdef_part : X / (lowN X:ℝ) * c
        * Real.log (1 + bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c)
      ≤ (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100)
          * Real.log (1 + 4 * bR * X * ((m:ℝ) * ((m:ℝ) + 1))
              * Real.exp (min ((m:ℝ) * Real.log 2) X - X)) := by
    -- coefficient bound
    have hcub := low_shell_card_ub h1 h2 hm1 hmM
    have hcoeff : X / (lowN X:ℝ) * c
        ≤ X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100 := by
      have hE := mul_le_mul_of_nonneg_left hcub hXN0
      have hidE : X / (lowN X:ℝ)
            * ((lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / Lg + 2 * (lowN X:ℝ) / 10 ^ 100)
          = X / Lg * (1 / ((m:ℝ) * ((m:ℝ) + 1))) + 2 * X / 10 ^ 100 := by
        field_simp
      rw [hidE] at hE
      have hLgX : X / Lg ≤ X / (X - 36) :=
        div_le_div_of_nonneg_left hX0.le hX36 hLg36
      have : X / Lg * (1 / ((m:ℝ) * ((m:ℝ) + 1)))
          ≤ X / (X - 36) * (1 / ((m:ℝ) * ((m:ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right hLgX (by positivity)
      have hidX : X / (X - 36) * (1 / ((m:ℝ) * ((m:ℝ) + 1)))
          = X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) := by
        ring
      linarith [hidX ▸ this]
    -- the log-argument bound
    have hlog_arg : Real.log (1 + bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c)
        ≤ Real.log (1 + 4 * bR * X * ((m:ℝ) * ((m:ℝ) + 1))
            * Real.exp (min ((m:ℝ) * Real.log 2) X - X)) := by
      apply Real.log_le_log harg_pos
      have hstep1 : bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c
          ≤ bR * Real.exp (min ((m:ℝ) * Real.log 2) X)
            / ((lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / (2 * X)) := by
        apply div_le_div_of_nonneg_left (by positivity) hPlow_pos hclow
      have hid3 : bR * Real.exp (min ((m:ℝ) * Real.log 2) X)
            / ((lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / (2 * X))
          = 2 * bR * X * ((m:ℝ) * ((m:ℝ) + 1))
            * (Real.exp (min ((m:ℝ) * Real.log 2) X) / (lowN X:ℝ)) := by
        field_simp
      have hexpN : Real.exp (min ((m:ℝ) * Real.log 2) X) / (lowN X:ℝ)
          ≤ 2 * Real.exp (min ((m:ℝ) * Real.log 2) X - X) := by
        have hNge : Real.exp X / 2 ≤ (lowN X:ℝ) :=
          exp_div_two_le_expFloor (by linarith)
        have hEX : (0:ℝ) < Real.exp X / 2 := by positivity
        calc Real.exp (min ((m:ℝ) * Real.log 2) X) / (lowN X:ℝ)
            ≤ Real.exp (min ((m:ℝ) * Real.log 2) X) / (Real.exp X / 2) :=
              div_le_div_of_nonneg_left (Real.exp_pos _).le hEX hNge
          _ = 2 * Real.exp (min ((m:ℝ) * Real.log 2) X - X) := by
              rw [Real.exp_sub]
              field_simp
      have hstep2 : 2 * bR * X * ((m:ℝ) * ((m:ℝ) + 1))
            * (Real.exp (min ((m:ℝ) * Real.log 2) X) / (lowN X:ℝ))
          ≤ 2 * bR * X * ((m:ℝ) * ((m:ℝ) + 1))
            * (2 * Real.exp (min ((m:ℝ) * Real.log 2) X - X)) := by
        apply mul_le_mul_of_nonneg_left hexpN
        positivity
      have hid4 : 2 * bR * X * ((m:ℝ) * ((m:ℝ) + 1))
            * (2 * Real.exp (min ((m:ℝ) * Real.log 2) X - X))
          = 4 * bR * X * ((m:ℝ) * ((m:ℝ) + 1))
            * Real.exp (min ((m:ℝ) * Real.log 2) X - X) := by
        ring
      have := le_trans hstep1 (le_of_eq hid3)
      linarith [hid3 ▸ hstep1, hid4 ▸ hstep2]
    have hcoeff0 : (0:ℝ) ≤ X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36)
        + 2 * X / 10 ^ 100 := by positivity
    calc X / (lowN X:ℝ) * c
          * Real.log (1 + bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c)
        ≤ (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100)
            * Real.log (1 + bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c) :=
          mul_le_mul_of_nonneg_right hcoeff hdef_nonneg
      _ ≤ (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100)
            * Real.log (1 + 4 * bR * X * ((m:ℝ) * ((m:ℝ) + 1))
                * Real.exp (min ((m:ℝ) * Real.log 2) X - X)) :=
          mul_le_mul_of_nonneg_left hlog_arg hcoeff0
  linarith

set_option maxHeartbeats 1000000 in
/-- Per-shell lower bound, regime `m ≤ A` (paper: "For `m ≤ T₊/2` the total
is below `10⁻¹⁰⁰⁰`"): the collision deficit carries `e^{a*_m − X} ≤ e^{−X/2}`. -/
theorem low_shell_lower_regime_I (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hm1 : 1 ≤ m) (hmA : m ≤ lowA X) :
    min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
      - (10:ℝ) ^ (30:ℕ) * Real.exp (-(X / 2)) - 300 * X ^ 2 / 10 ^ 100
      ≤ X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m) := by
  have hmM : m ≤ lowM X := le_trans hmA (low_A_le_M h1 h2)
  have hcore := low_shell_collision h1 h2 hm1 hmM
  have hX0 : (0:ℝ) < X := by linarith
  have hX36 : (0:ℝ) < X - 36 := by linarith
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hcm0 : (0:ℝ) < (m:ℝ) * ((m:ℝ) + 1) := by positivity
  have hbR0 : (0:ℝ) ≤ (lowCollisionMult X m : ℝ) := Nat.cast_nonneg _
  set U : ℝ := 4 * (lowCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
      * Real.exp (min ((m:ℝ) * Real.log 2) X - X) with hUdef
  have hU0 : (0:ℝ) ≤ U := by positivity
  -- coefficient at most 1
  have hcoeff : X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100
      ≤ 1 := by
    have hinv2 : 1 / ((m:ℝ) * ((m:ℝ) + 1)) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      nlinarith
    have hnum : X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) ≤ X / 2 := by
      have := mul_le_mul_of_nonneg_left hinv2 hX0.le
      linarith
    have hdiv : X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) ≤ X / 2 / (X - 36) :=
      div_le_div_of_nonneg_right hnum hX36.le
    have h06 : X / 2 / (X - 36) ≤ 0.6 := by
      rw [div_le_iff₀ hX36]
      linarith
    have hj : 2 * X / 10 ^ 100 ≤ 0.4 := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10 ^ 100)]
      have : (2.2e7:ℝ) ≤ 0.4 * 10 ^ 100 := by norm_num
      linarith
    linarith
  have hcoeff0 : (0:ℝ) ≤ X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36)
      + 2 * X / 10 ^ 100 := by positivity
  -- the collision multiplicity is at most 2.2 in this regime
  have hmA' : (m:ℝ) ≤ 7.8e6 := by
    have h : (m:ℝ) ≤ (lowA X : ℝ) := Nat.cast_le.mpr hmA
    linarith [low_A_cast_ub h1 h2]
  have hb22 : (lowCollisionMult X m : ℝ) ≤ 2.2 := by
    have hcast := low_collisionMult_cast_le h1 hm1
    have hsqrt : Real.sqrt m ≤ 2793 := by
      have h : ((m:ℝ)) ≤ 2793 ^ 2 := by nlinarith
      calc Real.sqrt m ≤ Real.sqrt (2793 ^ 2) := Real.sqrt_le_sqrt h
        _ = 2793 := Real.sqrt_sq (by norm_num)
    have hlogm : Real.log m ≤ 16 := by
      rw [Real.log_le_iff_le_exp hm0]
      linarith [low_exp_16_lb]
    have hlogm0 : (0:ℝ) ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
    have hlog1m : Real.log (1 + Real.log m) ≤ 3.7 := by
      rw [Real.log_le_iff_le_exp (by linarith)]
      linarith [low_exp_3_7_lb]
    have hlog4 : Real.log 4 ≤ 1.3862943616 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
        norm_num
      linarith [Real.log_two_lt_d9]
    have hlog4pos : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hp1 : Real.log 4 * (m:ℝ) ≤ 1.3862943616 * 7.8e6 :=
      mul_le_mul hlog4 hmA' hm0.le (by norm_num)
    have hp2 : Real.sqrt m * Real.log m ≤ 2793 * 16 :=
      mul_le_mul hsqrt hlogm hlogm0 (by norm_num)
    have hW : Real.log 4 * (m:ℝ) + Real.sqrt m * Real.log m
        + Real.log (1 + Real.log m) ≤ 10857788 := by
      nlinarith
    have hWdiv : (Real.log 4 * (m:ℝ) + Real.sqrt m * Real.log m
        + Real.log (1 + Real.log m)) / (X - 36) ≤ 10857788 / 9699964 := by
      have hW0 : (0:ℝ) ≤ Real.log 4 * (m:ℝ) + Real.sqrt m * Real.log m
          + Real.log (1 + Real.log m) := by
        have hs : (0:ℝ) ≤ Real.sqrt m * Real.log m :=
          mul_nonneg (Real.sqrt_nonneg _) hlogm0
        have hl : (0:ℝ) ≤ Real.log (1 + Real.log m) :=
          Real.log_nonneg (by linarith)
        nlinarith
      calc (Real.log 4 * (m:ℝ) + Real.sqrt m * Real.log m
            + Real.log (1 + Real.log m)) / (X - 36)
          ≤ (Real.log 4 * (m:ℝ) + Real.sqrt m * Real.log m
            + Real.log (1 + Real.log m)) / 9699964 :=
            div_le_div_of_nonneg_left hW0 (by norm_num) (by linarith)
        _ ≤ 10857788 / 9699964 :=
            div_le_div_of_nonneg_right hW (by norm_num)
    have : (10857788:ℝ) / 9699964 + 1 ≤ 2.2 := by norm_num
    linarith
  -- the exponential factor
  have hastar : min ((m:ℝ) * Real.log 2) X - X ≤ -(X / 2) := by
    have hmlog2 := low_A_mul_log2_le h1 hmA
    have : min ((m:ℝ) * Real.log 2) X ≤ X / 2 :=
      le_trans (min_le_left _ _) hmlog2
    linarith
  have hexp_a : Real.exp (min ((m:ℝ) * Real.log 2) X - X) ≤ Real.exp (-(X / 2)) :=
    Real.exp_le_exp.mpr hastar
  -- product bound
  have hmm : (m:ℝ) * ((m:ℝ) + 1) ≤ 6.1e13 := by nlinarith
  have hs2 : 4 * (lowCollisionMult X m : ℝ) * X ≤ 8.8 * 1.07e7 := by
    have h4b : 4 * (lowCollisionMult X m : ℝ) ≤ 8.8 := by linarith
    have := mul_le_mul h4b h2 hX0.le (by norm_num)
    linarith
  have hs3 : 4 * (lowCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
      ≤ 8.8 * 1.07e7 * 6.1e13 := by
    have := mul_le_mul hs2 hmm hcm0.le (by norm_num)
    linarith
  have hUle : U ≤ 5.8e21 * Real.exp (-(X / 2)) := by
    rw [hUdef]
    calc 4 * (lowCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
          * Real.exp (min ((m:ℝ) * Real.log 2) X - X)
        ≤ (8.8 * 1.07e7 * 6.1e13) * Real.exp (-(X / 2)) := by
          apply mul_le_mul hs3 hexp_a (Real.exp_pos _).le (by norm_num)
      _ ≤ 5.8e21 * Real.exp (-(X / 2)) := by
          apply mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
  have hlogU : Real.log (1 + U) ≤ U := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + U by linarith)
    linarith
  have hlogU0 : (0:ℝ) ≤ Real.log (1 + U) := Real.log_nonneg (by linarith)
  have hdef : (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100)
        * Real.log (1 + U)
      ≤ (10:ℝ) ^ (30:ℕ) * Real.exp (-(X / 2)) := by
    calc (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100)
          * Real.log (1 + U)
        ≤ 1 * (5.8e21 * Real.exp (-(X / 2))) := by
          apply mul_le_mul hcoeff (le_trans hlogU hUle) hlogU0 (by norm_num)
      _ ≤ (10:ℝ) ^ (30:ℕ) * Real.exp (-(X / 2)) := by
          rw [one_mul]
          apply mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
  have hjunk : 2 * X ^ 2 / 10 ^ 100 ≤ 300 * X ^ 2 / 10 ^ 100 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    nlinarith
  linarith

set_option maxHeartbeats 1000000 in
/-- Per-shell lower bound, regime `A < m ≤ M` (the paper's `m ≥ T₊` integral
regime, merged with the transition range — see the module docstring). -/
theorem low_shell_lower_regime_II (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7)
    {m : ℕ} (hmA : lowA X < m) (hmM : m ≤ lowM X) :
    min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
      - X / (X - 36) * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
          / ((m:ℝ) * ((m:ℝ) + 1)))
      - 300 * X ^ 2 / 10 ^ 100
      ≤ X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m) := by
  have hm1 : 1 ≤ m := by
    have := low_A_lb h1
    omega
  have hcore := low_shell_collision h1 h2 hm1 hmM
  have hX0 : (0:ℝ) < X := by linarith
  have hX36 : (0:ℝ) < X - 36 := by linarith
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hcm0 : (0:ℝ) < (m:ℝ) * ((m:ℝ) + 1) := by positivity
  have hm_lb : (6997001:ℝ) ≤ (m:ℝ) := by
    have hA : (6997000:ℝ) ≤ (lowA X:ℝ) := by exact_mod_cast low_A_lb h1
    have : (lowA X:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hmA
    linarith
  have hbR0 : (0:ℝ) ≤ (lowCollisionMult X m : ℝ) := Nat.cast_nonneg _
  have hlog1 : (0:ℝ) ≤ Real.log ((m:ℝ) + 1) := Real.log_nonneg (by linarith)
  set U : ℝ := 4 * (lowCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
      * Real.exp (min ((m:ℝ) * Real.log 2) X - X) with hUdef
  have hU0 : (0:ℝ) ≤ U := by positivity
  -- collision multiplicity bound `b_m ≤ 2.783 m/(X−36)` (eq. `explicit-bm`)
  have hbm : (lowCollisionMult X m : ℝ) ≤ 2.783 * (m:ℝ) / (X - 36) := by
    have hcast := low_collisionMult_cast_le h1 hm1
    have hsqrtlog : Real.sqrt m * Real.log m ≤ 0.01 * (m:ℝ) :=
      low_sqrt_mul_log_le (by linarith)
    have hlogm35 : Real.log m ≤ 35 := by
      have hstep : Real.log (m:ℝ) ≤ Real.log ((m:ℝ) + 1) :=
        Real.log_le_log hm0 (by linarith)
      linarith [low_log_add_one_le_35 h1 h2 hmM]
    have hlogm0 : (0:ℝ) ≤ Real.log m := Real.log_nonneg (by linarith)
    have hlog1m : Real.log (1 + Real.log m) ≤ 3.7 := by
      rw [Real.log_le_iff_le_exp (by linarith)]
      linarith [low_exp_3_7_lb]
    have hlog4 : Real.log 4 ≤ 1.3862943616 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
        norm_num
      linarith [Real.log_two_lt_d9]
    have h37 : (3.7:ℝ) ≤ 0.0004 * (m:ℝ) := by linarith
    have hW : Real.log 4 * (m:ℝ) + Real.sqrt m * Real.log m
        + Real.log (1 + Real.log m) ≤ 1.3966943616 * (m:ℝ) := by
      have := mul_le_mul_of_nonneg_right hlog4 hm0.le
      nlinarith
    have hone : 1 ≤ 1.3862943616 * (m:ℝ) / (X - 36) := by
      have hgtA := low_gt_A_cast hmA
      have h2log2 : 2 * Real.log 2 * (m:ℝ) ≤ 1.3862943616 * (m:ℝ) := by
        nlinarith [Real.log_two_lt_d9]
      rw [le_div_iff₀ hX36]
      linarith
    have hWdiv : (Real.log 4 * (m:ℝ) + Real.sqrt m * Real.log m
        + Real.log (1 + Real.log m)) / (X - 36) ≤ 1.3966943616 * (m:ℝ) / (X - 36) :=
      div_le_div_of_nonneg_right hW hX36.le
    have hsum : 1.3966943616 * (m:ℝ) / (X - 36) + 1.3862943616 * (m:ℝ) / (X - 36)
        = 2.7829887232 * (m:ℝ) / (X - 36) := by
      ring
    have hfin : 2.7829887232 * (m:ℝ) / (X - 36) ≤ 2.783 * (m:ℝ) / (X - 36) := by
      apply div_le_div_of_nonneg_right _ hX36.le
      nlinarith
    linarith
  -- `1 + U ≤ 12(m+1)³`
  have hexp1 : Real.exp (min ((m:ℝ) * Real.log 2) X - X) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    apply Real.exp_le_exp.mpr
    have := min_le_right ((m:ℝ) * Real.log 2) X
    linarith
  have hUle : U ≤ 11.14 * ((m:ℝ) + 1) ^ 3 := by
    have hb4 : 4 * (lowCollisionMult X m : ℝ) ≤ 11.132 * (m:ℝ) / (X - 36) := by
      rw [show (11.132:ℝ) * (m:ℝ) / (X - 36) = 4 * (2.783 * (m:ℝ) / (X - 36)) by ring]
      linarith
    have hstep : 4 * (lowCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
        ≤ 11.132 * (m:ℝ) / (X - 36) * X * ((m:ℝ) * ((m:ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_right _ hcm0.le
      exact mul_le_mul_of_nonneg_right hb4 hX0.le
    have hid : 11.132 * (m:ℝ) / (X - 36) * X * ((m:ℝ) * ((m:ℝ) + 1))
        = 11.132 * (X / (X - 36)) * ((m:ℝ) * (m:ℝ) * ((m:ℝ) + 1)) := by
      ring
    have hXdiv := low_X_div_X36_ub h1
    have hcoef : 11.132 * (X / (X - 36)) ≤ 11.14 := by nlinarith
    have hm3 : (m:ℝ) * (m:ℝ) * ((m:ℝ) + 1) ≤ ((m:ℝ) + 1) ^ 3 := by nlinarith
    have hfin : 11.132 * (X / (X - 36)) * ((m:ℝ) * (m:ℝ) * ((m:ℝ) + 1))
        ≤ 11.14 * ((m:ℝ) + 1) ^ 3 := by
      apply mul_le_mul hcoef hm3 (by positivity) (by norm_num)
    have hUmid : U ≤ 4 * (lowCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1)) := by
      rw [hUdef]
      calc 4 * (lowCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
            * Real.exp (min ((m:ℝ) * Real.log 2) X - X)
          ≤ 4 * (lowCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1)) * 1 := by
            apply mul_le_mul_of_nonneg_left hexp1 (by positivity)
        _ = 4 * (lowCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1)) := by
            rw [mul_one]
    linarith [hid ▸ hstep]
  have h1U : 1 + U ≤ 12 * ((m:ℝ) + 1) ^ 3 := by nlinarith
  have hlog12 : Real.log (1 + U) ≤ Real.log 12 + 3 * Real.log ((m:ℝ) + 1) := by
    have hstep : Real.log (1 + U) ≤ Real.log (12 * ((m:ℝ) + 1) ^ 3) :=
      Real.log_le_log (by linarith) h1U
    have hid : Real.log (12 * ((m:ℝ) + 1) ^ 3)
        = Real.log 12 + 3 * Real.log ((m:ℝ) + 1) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    linarith [hid ▸ hstep]
  -- assemble the deficit bound
  have hcoeff0 : (0:ℝ) ≤ X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) := by
    positivity
  have hR0 : (0:ℝ) ≤ Real.log 12 + 3 * Real.log ((m:ℝ) + 1) := by
    have : (0:ℝ) ≤ Real.log 12 := Real.log_nonneg (by norm_num)
    linarith
  have hlogU0 : (0:ℝ) ≤ Real.log (1 + U) := Real.log_nonneg (by linarith)
  have hdef : (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100)
        * Real.log (1 + U)
      ≤ X / (X - 36) * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
          / ((m:ℝ) * ((m:ℝ) + 1)))
        + 298 * X ^ 2 / 10 ^ 100 := by
    have hmain : (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100)
          * Real.log (1 + U)
        ≤ (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100)
            * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left hlog12
      positivity
    have hexpand : (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100)
          * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
        = X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36)
            * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
          + 2 * X / 10 ^ 100 * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) := by
      ring
    have hid1 : X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36)
          * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
        = X / (X - 36) * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
            / ((m:ℝ) * ((m:ℝ) + 1))) := by
      ring
    have hlogm35 := low_log_add_one_le_35 h1 h2 hmM
    have hlog12u := low_log_12_ub
    have hRle : Real.log 12 + 3 * Real.log ((m:ℝ) + 1) ≤ 108 := by linarith
    have hpiece2 : 2 * X / 10 ^ 100 * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
        ≤ 298 * X ^ 2 / 10 ^ 100 := by
      have h2X0 : (0:ℝ) ≤ 2 * X / 10 ^ 100 := by positivity
      have hstep : 2 * X / 10 ^ 100 * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
          ≤ 2 * X / 10 ^ 100 * 108 := mul_le_mul_of_nonneg_left hRle h2X0
      have hid2 : 2 * X / 10 ^ 100 * 108 = 216 * X / 10 ^ 100 := by ring
      have hfin : 216 * X / 10 ^ 100 ≤ 298 * X ^ 2 / 10 ^ 100 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        nlinarith
      linarith [hid2 ▸ hstep]
    calc (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100)
          * Real.log (1 + U)
        ≤ (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36) + 2 * X / 10 ^ 100)
            * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) := hmain
      _ = X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / (X - 36)
            * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
          + 2 * X / 10 ^ 100 * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) := hexpand
      _ ≤ X / (X - 36) * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
            / ((m:ℝ) * ((m:ℝ) + 1)))
          + 298 * X ^ 2 / 10 ^ 100 := by
          rw [← hid1]
          linarith
  linarith

end LowerShells

/-! ## Summing the lower per-shell bounds -/

section LowerSums

variable {X : ℝ}

/-- Total regime-I deficit: at most `A` shells, each contributing at most
`10³⁰·e^{−X/2} ≤ 10⁻⁷⁵` — beyond negligible (paper: `< 10⁻¹⁰⁰⁰`). -/
theorem low_deficit_I_sum_le (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    ∑ _m ∈ Finset.Icc 1 (lowA X), (10:ℝ) ^ (30:ℕ) * Real.exp (-(X / 2))
      ≤ 1e-8 := by
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hcast : ((lowA X + 1 - 1 : ℕ) : ℝ) = (lowA X : ℝ) := by simp
  rw [hcast]
  have hA := low_A_cast_ub h1 h2
  have hA0 : (0:ℝ) ≤ (lowA X : ℝ) := Nat.cast_nonneg _
  have hexp := low_exp_half_X_lb h1
  have hexpneg : Real.exp (-(X / 2)) ≤ 1 / (10:ℝ) ^ (105:ℕ) := by
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    calc (1 / (10:ℝ) ^ (105:ℕ))⁻¹ = (10:ℝ) ^ (105:ℕ) := by
          rw [one_div, inv_inv]
      _ ≤ Real.exp (X / 2) := hexp
  calc (lowA X : ℝ) * ((10:ℝ) ^ (30:ℕ) * Real.exp (-(X / 2)))
      ≤ 7.8e6 * ((10:ℝ) ^ (30:ℕ) * (1 / (10:ℝ) ^ (105:ℕ))) := by
        apply mul_le_mul hA _ (by positivity) (by norm_num)
        exact mul_le_mul_of_nonneg_left hexpneg (by positivity)
    _ ≤ 1e-8 := by norm_num

/-- Total regime-II deficit (paper: `< 1.018·10⁻⁵` from `T₊`; here
`≤ 7.7·10⁻⁶` from `A = ⌊X/(2 log 2)⌋`, absorbing the transition range). -/
theorem low_deficit_II_sum_le (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
        X / (X - 36) * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
          / ((m:ℝ) * ((m:ℝ) + 1)))
      ≤ 7.7e-6 := by
  have hX36 : (0:ℝ) < X - 36 := by linarith
  have hXX := low_X_div_X36_ub h1
  have hA0 : (6997000:ℝ) ≤ (lowA X : ℝ) := by exact_mod_cast low_A_lb h1
  rw [← Finset.mul_sum]
  have hlog12u := low_log_12_ub
  have hlog12l : (0:ℝ) ≤ Real.log 12 := Real.log_nonneg (by norm_num)
  have hterm : ∀ m ∈ Finset.Ioc (lowA X) (lowM X),
      (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ Real.log 12 * (1 / ((m:ℝ) * (m:ℝ)))
          + 3 * (1 + 1/6997001)
              * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1))) := by
    intro m hm
    have hmA : lowA X < m := (Finset.mem_Ioc.mp hm).1
    have hm' : (6997001:ℝ) ≤ (m:ℝ) := by
      have : (lowA X:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hmA
      linarith
    have hm0 : (0:ℝ) < (m:ℝ) := by linarith
    have hL0 : (0:ℝ) ≤ Real.log ((m:ℝ) + 1) := Real.log_nonneg (by linarith)
    have hsplit : (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) / ((m:ℝ) * ((m:ℝ) + 1))
        = Real.log 12 / ((m:ℝ) * ((m:ℝ) + 1))
          + 3 * Real.log ((m:ℝ) + 1) / ((m:ℝ) * ((m:ℝ) + 1)) := by
      rw [add_div]
    have hpiece1 : Real.log 12 / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ Real.log 12 * (1 / ((m:ℝ) * (m:ℝ))) := by
      rw [mul_one_div]
      apply div_le_div_of_nonneg_left hlog12l (by positivity)
      nlinarith
    have hpiece2 : 3 * Real.log ((m:ℝ) + 1) / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ 3 * (1 + 1/6997001)
            * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1))) := by
      have hw : (1:ℝ) / ((m:ℝ) * ((m:ℝ) + 1))
          ≤ (1 + 1/6997001) / (((m:ℝ) + 1) * ((m:ℝ) + 1)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc 3 * Real.log ((m:ℝ) + 1) / ((m:ℝ) * ((m:ℝ) + 1))
          = 3 * Real.log ((m:ℝ) + 1) * (1 / ((m:ℝ) * ((m:ℝ) + 1))) := by
            rw [mul_one_div]
        _ ≤ 3 * Real.log ((m:ℝ) + 1)
              * ((1 + 1/6997001) / (((m:ℝ) + 1) * ((m:ℝ) + 1))) := by
            apply mul_le_mul_of_nonneg_left hw (by positivity)
        _ = 3 * (1 + 1/6997001)
              * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1))) := by
            field_simp
    rw [hsplit]
    linarith
  have hsum1 := sum_one_div_Ioc_le (lowA X) (lowM X)
    (le_trans (by norm_num) (low_A_lb h1))
  have hsum2 := sum_log_div_sq_tail_le (lowA X) (lowM X)
    (le_trans (by norm_num) (low_A_lb h1))
  have h16 := low_log_A_add_one_ub h1 h2
  have hinner : ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
      (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) / ((m:ℝ) * ((m:ℝ) + 1))
      ≤ 7.686e-6 := by
    have hs1' : (1:ℝ) / (lowA X : ℝ) ≤ 1 / 6997000 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    have hs2' : (Real.log ((lowA X:ℝ) + 1) + 1) / ((lowA X:ℝ) + 1)
        ≤ 17 / 6997001 := by
      calc (Real.log ((lowA X:ℝ) + 1) + 1) / ((lowA X:ℝ) + 1)
          ≤ 17 / ((lowA X:ℝ) + 1) :=
            div_le_div_of_nonneg_right (by linarith) (by linarith)
        _ ≤ 17 / 6997001 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
            linarith
    calc ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
          (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
            (Real.log 12 * (1 / ((m:ℝ) * (m:ℝ)))
              + 3 * (1 + 1/6997001)
                  * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1)))) :=
          Finset.sum_le_sum hterm
      _ = Real.log 12 * ∑ m ∈ Finset.Ioc (lowA X) (lowM X), 1 / ((m:ℝ) * (m:ℝ))
          + 3 * (1 + 1/6997001) * ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
              Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2.7725888 * (1 / 6997000) + 3 * (1 + 1/6997001) * (17 / 6997001) := by
          apply add_le_add
          · apply mul_le_mul hlog12u (by linarith [hsum1, hs1']) _ (by norm_num)
            apply Finset.sum_nonneg
            intro m _
            positivity
          · apply mul_le_mul_of_nonneg_left _ (by norm_num)
            linarith [hsum2, hs2']
      _ ≤ 7.686e-6 := by norm_num
  have hinner0 : (0:ℝ) ≤ ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
      (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) / ((m:ℝ) * ((m:ℝ) + 1)) := by
    apply Finset.sum_nonneg
    intro m hm
    have hmA : lowA X < m := (Finset.mem_Ioc.mp hm).1
    have hm0 : (0:ℝ) < (m:ℝ) := by
      have : 0 < m := by
        have := low_A_lb h1
        omega
      exact_mod_cast this
    have hL0 : (0:ℝ) ≤ Real.log ((m:ℝ) + 1) := Real.log_nonneg (by linarith)
    have : (0:ℝ) ≤ Real.log 12 + 3 * Real.log ((m:ℝ) + 1) := by linarith
    positivity
  calc X / (X - 36) * ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
        (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) / ((m:ℝ) * ((m:ℝ) + 1))
      ≤ 1.0000038 * 7.686e-6 := mul_le_mul hXX hinner hinner0 (by norm_num)
    _ ≤ 7.7e-6 := by norm_num

/-- The full lower shell-sum estimate: after normalization by `X/N`, the
shell sums fall short of the truncated `𝓑`-sum by at most
`7.7·10⁻⁶ + 2·10⁻⁸`. -/
theorem low_sum_lower (h1 : (9.7e6:ℝ) ≤ X) (h2 : X ≤ 1.07e7) :
    (∑ m ∈ Finset.Icc 1 (lowM X), min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)))
        - (7.7e-6 + 1e-8 + 1e-8)
      ≤ X / (lowN X:ℝ)
        * ∑ m ∈ Finset.Icc 1 (lowM X),
            ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m) := by
  have hAM := low_A_le_M h1 h2
  have hunion : Finset.Icc 1 (lowM X)
      = Finset.Icc 1 (lowA X) ∪ Finset.Ioc (lowA X) (lowM X) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (lowA X)) (Finset.Ioc (lowA X) (lowM X)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1
    simp only [Finset.mem_Ioc] at hk2
    omega
  rw [Finset.mul_sum, hunion, Finset.sum_union hdisj, Finset.sum_union hdisj]
  have hheadI0 : ∑ m ∈ Finset.Icc 1 (lowA X),
      (min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
        - (10:ℝ) ^ (30:ℕ) * Real.exp (-(X / 2)) - 300 * X ^ 2 / 10 ^ 100)
      ≤ ∑ m ∈ Finset.Icc 1 (lowA X),
          X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m) := by
    apply Finset.sum_le_sum
    intro m hm
    have hmem := Finset.mem_Icc.mp hm
    exact low_shell_lower_regime_I h1 h2 hmem.1 hmem.2
  have hheadIeq : ∑ m ∈ Finset.Icc 1 (lowA X),
      (min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
        - (10:ℝ) ^ (30:ℕ) * Real.exp (-(X / 2)) - 300 * X ^ 2 / 10 ^ 100)
      = (∑ m ∈ Finset.Icc 1 (lowA X), min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)))
        - (∑ _m ∈ Finset.Icc 1 (lowA X), (10:ℝ) ^ (30:ℕ) * Real.exp (-(X / 2)))
        - ∑ _m ∈ Finset.Icc 1 (lowA X), 300 * X ^ 2 / 10 ^ 100 := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hheadI := hheadIeq ▸ hheadI0
  have htailII0 : ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
      (min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
        - X / (X - 36) * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
            / ((m:ℝ) * ((m:ℝ) + 1)))
        - 300 * X ^ 2 / 10 ^ 100)
      ≤ ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
          X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m) := by
    apply Finset.sum_le_sum
    intro m hm
    have hmem := Finset.mem_Ioc.mp hm
    exact low_shell_lower_regime_II h1 h2 hmem.1 hmem.2
  have htailIIeq : ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
      (min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
        - X / (X - 36) * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
            / ((m:ℝ) * ((m:ℝ) + 1)))
        - 300 * X ^ 2 / 10 ^ 100)
      = (∑ m ∈ Finset.Ioc (lowA X) (lowM X), min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)))
        - (∑ m ∈ Finset.Ioc (lowA X) (lowM X),
            X / (X - 36) * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
              / ((m:ℝ) * ((m:ℝ) + 1))))
        - ∑ _m ∈ Finset.Ioc (lowA X) (lowM X), 300 * X ^ 2 / 10 ^ 100 := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have htailII := htailIIeq ▸ htailII0
  have hdefI := low_deficit_I_sum_le h1 h2
  have hdefII := low_deficit_II_sum_le h1 h2
  have hjunk : (∑ _m ∈ Finset.Icc 1 (lowA X), 300 * X ^ 2 / 10 ^ 100)
      + (∑ _m ∈ Finset.Ioc (lowA X) (lowM X), 300 * X ^ 2 / 10 ^ 100) ≤ 1e-8 := by
    rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, Nat.card_Ioc,
      nsmul_eq_mul, nsmul_eq_mul]
    have hcast : ((lowA X + 1 - 1 : ℕ) : ℝ) + ((lowM X - lowA X : ℕ) : ℝ)
        = (lowM X : ℝ) := by
      rw [Nat.cast_sub hAM]
      simp
    calc ((lowA X + 1 - 1 : ℕ) : ℝ) * (300 * X ^ 2 / 10 ^ 100)
          + ((lowM X - lowA X : ℕ) : ℝ) * (300 * X ^ 2 / 10 ^ 100)
        = (lowM X : ℝ) * (300 * X ^ 2 / 10 ^ 100) := by
          rw [← add_mul, hcast]
      _ ≤ 1e-8 := low_junk_total_le h1 h2
  linarith

end LowerSums

/-! ## The lower half and the final enclosure of eq. `explicit-low-averaging` -/

/-- **Lower explicit averaging bound** (`lem:explicit-low-averaging`, lower
half): `−1.03·10⁻⁵ < 𝓡(X)` for `9.7·10⁶ ≤ X ≤ 1.07·10⁷`.  (The realized
bound is in fact `𝓡(X) > −7.9·10⁻⁶`; the paper's stated `−1.03·10⁻⁵` follows
a fortiori.) -/
theorem explicit_low_averaging_lower {X : ℝ} (h1 : (9.7e6:ℝ) ≤ X)
    (h2 : X ≤ 1.07e7) : -1.03e-5 < averagingError X := by
  have hbridge := low_bridge h1 h2
  have hdec := (g_shell_decomposition (N := lowN X) (M := lowM X)
    (low_hQN h1) (low_hQ2 h1 h2)).1
  have hsum := low_sum_lower h1 h2
  have hBle := low_B_le_partial_add_tail (X := X) (lowM X)
  have hBtail : X / ((lowM X:ℝ) + 1) ≤ 6e-8 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [low_M_add_one_lb h1]
  have hXN0 : (0:ℝ) ≤ X / (lowN X:ℝ) :=
    div_nonneg (by linarith) (low_N_pos h1).le
  have hmul := mul_le_mul_of_nonneg_left hdec hXN0
  have hF : X / (lowN X:ℝ) * g (lowN X) - 1e-9 ≤ FReal (Real.exp X) := by
    linarith [(abs_le.mp hbridge).1]
  rw [averagingError]
  linarith

/-- **Explicit low-interval averaging error** (`lem:explicit-low-averaging`,
eq. `explicit-low-averaging`): for `9.7·10⁶ ≤ X ≤ 1.07·10⁷`,
`|𝓡(X)| < 1.2·10⁻⁵` — the enclosure consumed by the low finite-input
certificate ledger (`comp:low`). -/
theorem explicit_low_averaging {X : ℝ} (h1 : (9.7e6 : ℝ) ≤ X)
    (h2 : X ≤ 1.07e7) : |averagingError X| < 1.2e-5 := by
  rw [abs_lt]
  constructor
  · linarith [explicit_low_averaging_lower h1 h2]
  · linarith [explicit_low_averaging_upper h1 h2]

end Erdos320
