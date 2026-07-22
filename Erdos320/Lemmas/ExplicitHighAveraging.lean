import Erdos320.Lemmas.ExplicitLowAveraging
import Erdos320.Lemmas.ElementaryThreshold

/-!
# Explicit high-interval averaging error and the high-interval bound for `ρ`
# (`cor:explicit-high-averaging`, `cor:explicit-high-rho`)

The manuscript's two corollaries in `sec:certificates`:

* **High-interval averaging error** (eq. `explicit-high-averaging`): for
  `X ≥ 8·10²⁶`,
  ```
  |𝓡(X)| < (log X + 2)²/X,      |𝓡(X)| < 2·10⁻²⁴,
  ```
  here `explicit_high_averaging` and `explicit_high_averaging_small`.
* **High-interval bound for `ρ`** (eq. `explicit-high-rho`): if
  `E_{s−1}(u) ≥ 8·10²⁶` then `|ρ_s(u)| < 10·E_{s−2}(u)²/E_{s−1}(u)`,
  here `rhoDepth_lt_of_big` (via the depth-free form `high_rho_abs_lt`).

The proof of the first corollary reruns the proof of
`lem:explicit-low-averaging` (`Erdos320/Lemmas/ExplicitLowAveraging.lean`)
with the same cutoff `M = ⌊X^2.05⌋` on the one-sided window `X ≥ 8·10²⁶`;
the second applies eq. `threshold-displacement` (derived here inline) with
`x = E_{s−1}(u)`, the elementary threshold bounds
(`mStar_lower` / `mStar_upper_explicit`), and the first corollary at
`z = log m_*(e^x)`.

Design notes (deviations from the paper's displayed constants, all safe):

* The scale definitions `N = ⌊e^X⌋` and `M = ⌊X^2.05⌋` are *shared* with the
  low-window file (`lowN`, `lowM`), as is the lower-estimate split index
  `A = ⌊X/(2 log 2)⌋` (`lowA`); their low-window lemmas that only need
  `X ≥ 9.7·10⁶` are reused directly.  The upper-estimate split index and the
  collision multiplicity get their own `high` versions (`highT`,
  `highCollisionMult`) because the uniform log-denominator changes from the
  low file's `X − 36` to `highLogDenom X = X − 3 log X − 1` (on this window
  `log(m + 1)` can reach `≈ 2.05 log X > 36`).
* The FKS endpoint errors cannot be absorbed by the fixed allowance
  `𝓔(t) ≤ t/10¹⁰⁰` of the low file: there are `M ≈ X^{2.05}` shells and the
  junk budget is `≈ 10⁻²⁴`, so the fixed `10⁻¹⁰⁰` relative error would
  overflow.  Instead each endpoint error is bounded by
  `N·ε(X)` with `ε(X) = exp(−0.79·√X)` (`highFksEps`, from
  `fksError_le_of_log_ge`), and all junk totals are absorbed into
  `exp(−0.7·√X) ≤ 0.001/X` (`high_tiny_le`).
* The paper's ledger constants `1.72·10⁻²⁴`, `8.0·10⁻²⁶`, `6.5·10⁻²⁵` are
  realized as the master enclosure
  `−(8.7(log X + 2) + 0.2)/X ≤ 𝓡(X) ≤ (0.7003((log X+1)²/2+1) +
  1.021(log X+2) + 0.2)/X`, which evaluates to `|𝓡(X)| < 1.94·10⁻²⁴` at the
  window edge — inside the paper's `2·10⁻²⁴` — and is dominated by
  `(log X+2)²/X` for every `X ≥ 8·10²⁶`.
* In `high_B_le` (the paper's `𝓑(x) < log 2·(log x + 2)` step of
  `cor:explicit-high-rho`) the realized constant is `log 2·(log x + 2.4)`;
  the extra `0.4` is amply covered by the corollary's factor-`10` headroom
  (the assembled total is `< 2.5·E_{s−2}²/E_{s−1}`, versus the paper's `6`).

All auxiliary declarations are prefixed `high`/`high_`.
-/

namespace Erdos320

/-! ## The window's derived parameters

Paper notation (proof of `cor:explicit-high-averaging`): `N = ⌊e^X⌋` and
`M = ⌊X^2.05⌋` are the shared `lowN`, `lowM`; the lower split index
`A = ⌊X/(2 log 2)⌋` is the shared `lowA`.  New here: -/

/-- The uniform lower bound `X − 3 log X − 1` for the shell log-denominators
`log(N/(m+1))`, `1 ≤ m ≤ M` (the high-window replacement for the low file's
`X − 36`; here `log(m+1) ≤ 2.05·log X + log 2 < 3 log X + 1 − 10⁻⁹`). -/
noncomputable def highLogDenom (X : ℝ) : ℝ := X - 3 * Real.log X - 1

/-- The upper-estimate split index `T = ⌊(X − 3 log X − 1)/log 2⌋`: for
`m ≤ T` the shell is clamped (`g(m) ≤ m log 2 ≤ highLogDenom X ≤
log(N/(m+1))`).  On this window `T ≥ X` (the paper's `T ≥ X`). -/
noncomputable def highT (X : ℝ) : ℕ := ⌊highLogDenom X / Real.log 2⌋₊

/-- The collision multiplicity `b_m` of eq. `explicit-bm`, with the
high-window denominator `highLogDenom X` (any integer at least
`log(L_m·H_m)/log(N/(m+1))` works; cf. `lowCollisionMult`). -/
noncomputable def highCollisionMult (X : ℝ) (m : ℕ) : ℕ :=
  ⌊(Real.log 4 * m + Real.sqrt m * Real.log m + Real.log (1 + Real.log m))
      / highLogDenom X⌋₊ + 1

/-- The per-endpoint FKS error allowance `ε(X) = exp(−0.79·√X)`: on this
window `fksError(N/(m+1)) ≤ N·ε(X)` (see `high_fks_a`).  This replaces the
low file's fixed `1/10¹⁰⁰`, which does not survive summation over
`M ≈ X^{2.05}` shells when `X ≥ 8·10²⁶`. -/
noncomputable def highFksEps (X : ℝ) : ℝ := Real.exp (-(0.79 * Real.sqrt X))

/-! ## Explicit numeric exponential facts -/

/-- `1.345³ ≥ 2.433`, hence `2.433 ≤ e^0.9`. -/
theorem high_exp_09_lb : (2.433 : ℝ) ≤ Real.exp 0.9 := by
  have h03 : (1.345 : ℝ) ≤ Real.exp 0.3 := by
    nlinarith [Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.3 by norm_num)]
  have hcube : (1.345 : ℝ) ^ (3:ℕ) ≤ Real.exp 0.3 ^ (3:ℕ) :=
    pow_le_pow_left₀ (by norm_num) h03 3
  have hexp : Real.exp 0.3 ^ (3:ℕ) = Real.exp 0.9 := by
    rw [← Real.exp_nat_mul]; norm_num
  calc (2.433 : ℝ) ≤ (1.345 : ℝ) ^ (3:ℕ) := by norm_num
    _ ≤ Real.exp 0.3 ^ (3:ℕ) := hcube
    _ = Real.exp 0.9 := hexp

/-- `e^0.9 ≤ (320/311)³² ≤ 2.492` (via `e^{9/320} ≤ 1/(1 − 9/320)`). -/
theorem high_exp_09_ub : Real.exp 0.9 ≤ 2.492 := by
  have hstep : Real.exp ((9:ℝ)/320) ≤ 320/311 := by
    have h := low_exp_le_inv_one_sub (show (9:ℝ)/320 < 1 by norm_num)
    calc Real.exp ((9:ℝ)/320) ≤ 1 / (1 - 9/320) := h
      _ = 320/311 := by norm_num
  have hpow : Real.exp ((9:ℝ)/320) ^ (32:ℕ) = Real.exp 0.9 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp ((9:ℝ)/320) ^ (32:ℕ) ≤ ((320:ℝ)/311) ^ (32:ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos _).le hstep 32
  have h3 : ((320:ℝ)/311) ^ (32:ℕ) ≤ 2.492 := by norm_num
  linarith [hpow ▸ h2]

/-- `7.54·10²⁶ ≤ e^61.9` — the anchor for the polynomial-versus-exponential
comparisons `high_poly_sq`, `high_poly_lin`. -/
theorem high_exp_61_9_lb : (7.54e26 : ℝ) ≤ Real.exp 61.9 := by
  have h61 := low_exp_nat_lb 61
  have h09 := high_exp_09_lb
  have hsplit : (61.9:ℝ) = ((61:ℕ):ℝ) + 0.9 := by norm_num
  rw [hsplit, Real.exp_add]
  calc (7.54e26 : ℝ) ≤ (2.7182818283 : ℝ) ^ (61:ℕ) * 2.433 := by norm_num
    _ ≤ Real.exp ((61:ℕ):ℝ) * Real.exp 0.9 :=
        mul_le_mul h61 h09 (by norm_num) (Real.exp_pos _).le

/-- `e^61.9 ≤ 7.8·10²⁶ ≤ 8·10²⁶` — behind `log X ≥ 61.9` on the window. -/
theorem high_exp_61_9_ub : Real.exp 61.9 ≤ 7.8e26 := by
  have h61 := low_exp_nat_ub 61
  have h09 := high_exp_09_ub
  have hsplit : (61.9:ℝ) = ((61:ℕ):ℝ) + 0.9 := by norm_num
  rw [hsplit, Real.exp_add]
  calc Real.exp ((61:ℕ):ℝ) * Real.exp 0.9
      ≤ (2.7182818286 : ℝ) ^ (61:ℕ) * 2.492 :=
        mul_le_mul h61 h09 (Real.exp_pos _).le (by positivity)
    _ ≤ 7.8e26 := by norm_num

/-! ## Window facts (`X ≥ 8·10²⁶`) -/

section HighWindow

variable {X : ℝ}

theorem high_X_pos (hX : (8e26:ℝ) ≤ X) : (0:ℝ) < X := by linarith

theorem high_logX_lb (hX : (8e26:ℝ) ≤ X) : (61.9:ℝ) ≤ Real.log X := by
  rw [Real.le_log_iff_exp_le (high_X_pos hX)]
  linarith [high_exp_61_9_ub]

theorem high_sqrt_lb (hX : (8e26:ℝ) ≤ X) : (2.8e13:ℝ) ≤ Real.sqrt X := by
  have h : (2.8e13:ℝ) = Real.sqrt (2.8e13 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  rw [h]
  exact Real.sqrt_le_sqrt (by nlinarith)

theorem high_sqrt_sq (hX : (8e26:ℝ) ≤ X) : Real.sqrt X * Real.sqrt X = X :=
  Real.mul_self_sqrt (high_X_pos hX).le

/-- `log X ≤ 10⁻⁶·√X` on the window — the absorption that lets every
polynomial-in-`log X` factor disappear into `exp(−c·√X)` junk. -/
theorem high_logX_le_sqrt (hX : (8e26:ℝ) ≤ X) :
    Real.log X ≤ 1e-6 * Real.sqrt X := by
  have hX0 : (0:ℝ) < X := high_X_pos hX
  have hs0 : (0:ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hr0 : (0:ℝ) < Real.sqrt (Real.sqrt X) := Real.sqrt_pos.mpr hs0
  have hrr : Real.sqrt (Real.sqrt X) * Real.sqrt (Real.sqrt X) = Real.sqrt X :=
    Real.mul_self_sqrt hs0.le
  have hlogX : Real.log X = 2 * Real.log (Real.sqrt X) := by
    rw [Real.log_sqrt hX0.le]; ring
  have hlogs : Real.log (Real.sqrt X) = 2 * Real.log (Real.sqrt (Real.sqrt X)) := by
    rw [Real.log_sqrt hs0.le]; ring
  have hlogr : Real.log (Real.sqrt (Real.sqrt X)) ≤ Real.sqrt (Real.sqrt X) - 1 :=
    Real.log_le_sub_one_of_pos hr0
  have hsbig : (2.8e13:ℝ) ≤ Real.sqrt X := high_sqrt_lb hX
  have hrbig : (5.2e6:ℝ) ≤ Real.sqrt (Real.sqrt X) := by nlinarith
  nlinarith

theorem high_logDenom_lb (hX : (8e26:ℝ) ≤ X) : 0.99 * X ≤ highLogDenom X := by
  have hL := high_logX_le_sqrt hX
  have hs := high_sqrt_lb hX
  have hss := high_sqrt_sq hX
  rw [highLogDenom]
  nlinarith

theorem high_logDenom_le (hX : (8e26:ℝ) ≤ X) : highLogDenom X ≤ X := by
  have hL := high_logX_lb hX
  rw [highLogDenom]
  linarith

theorem high_logDenom_pos (hX : (8e26:ℝ) ≤ X) : (0:ℝ) < highLogDenom X := by
  have h := high_logDenom_lb hX
  nlinarith [high_X_pos hX]

/-- The window's uniform bound `X/(X − 3 log X − 1) ≤ 1.011`. -/
theorem high_X_div_logDenom_ub (hX : (8e26:ℝ) ≤ X) :
    X / highLogDenom X ≤ 1.011 := by
  rw [div_le_iff₀ (high_logDenom_pos hX)]
  nlinarith [high_logDenom_lb hX, high_X_pos hX]

theorem high_exp_log (hX : (8e26:ℝ) ≤ X) : Real.exp (Real.log X) = X :=
  Real.exp_log (high_X_pos hX)

/-! ### Polynomial-versus-exponential anchors at `L ≥ 61.9` -/

/-- `(L+1)²/2 + 1 ≤ 2.63·10⁻²⁴·e^L` for `L ≥ 61.9` — the head-sum cap in
numeric form (the sharp value at the window edge is `≈ 2.62·10⁻²⁴`). -/
theorem high_poly_sq {L : ℝ} (hL : (61.9:ℝ) ≤ L) :
    (L + 1) ^ 2 / 2 + 1 ≤ 2.63e-24 * Real.exp L := by
  have hsplit : Real.exp L = Real.exp 61.9 * Real.exp (L - 61.9) := by
    rw [← Real.exp_add]; ring_nf
  have hq := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ L - 61.9 by linarith)
  have hanchor := high_exp_61_9_lb
  rw [hsplit]
  nlinarith [Real.exp_pos (L - 61.9), sq_nonneg (L - 61.9)]

/-- `L + 2 ≤ 8.5·10⁻²⁶·e^L` for `L ≥ 61.9` — the tail-sum cap in numeric
form. -/
theorem high_poly_lin {L : ℝ} (hL : (61.9:ℝ) ≤ L) :
    L + 2 ≤ 8.5e-26 * Real.exp L := by
  have hsplit : Real.exp L = Real.exp 61.9 * Real.exp (L - 61.9) := by
    rw [← Real.exp_add]; ring_nf
  have hq := Real.add_one_le_exp (L - 61.9)
  have hanchor := high_exp_61_9_lb
  rw [hsplit]
  nlinarith [Real.exp_pos (L - 61.9)]

/-! ### The universal junk majorant `exp(−0.7·√X)` -/

/-- `exp(−0.7·√X) ≤ 0.001/X`: the single lemma through which every junk
total (FKS endpoint errors, fibre cost remainders, regime-I deficits, the
normalization bridge) reaches both the numeric and the symbolic ledger. -/
theorem high_tiny_le (hX : (8e26:ℝ) ≤ X) :
    Real.exp (-(0.7 * Real.sqrt X)) ≤ 0.001 / X := by
  have hX0 := high_X_pos hX
  have hL := high_logX_le_sqrt hX
  have hs := high_sqrt_lb hX
  have hsplit : Real.exp (-(0.7 * Real.sqrt X))
      = Real.exp (Real.log X - 0.7 * Real.sqrt X) * (1 / X) := by
    rw [Real.exp_sub, high_exp_log hX, Real.exp_neg]
    field_simp
  rw [hsplit]
  have harg : Real.log X - 0.7 * Real.sqrt X ≤ -7 := by nlinarith
  have hexp7 : Real.exp (Real.log X - 0.7 * Real.sqrt X) ≤ Real.exp (-7 : ℝ) :=
    Real.exp_le_exp.mpr harg
  have he7 : Real.exp (-7 : ℝ) ≤ 0.001 := by
    have h7 := low_exp_nat_lb 7
    have hpos := Real.exp_pos (7:ℝ)
    have hmul : Real.exp (-7:ℝ) * Real.exp (7:ℝ) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hbig : (1000:ℝ) ≤ Real.exp (7:ℝ) := by
      calc (1000:ℝ) ≤ (2.7182818283:ℝ) ^ (7:ℕ) := by norm_num
        _ ≤ Real.exp ((7:ℕ):ℝ) := h7
        _ = Real.exp (7:ℝ) := by norm_num
    nlinarith [Real.exp_pos (-7:ℝ)]
  calc Real.exp (Real.log X - 0.7 * Real.sqrt X) * (1 / X)
      ≤ 0.001 * (1 / X) := by
        apply mul_le_mul_of_nonneg_right (hexp7.trans he7) (by positivity)
    _ = 0.001 / X := by ring

theorem high_eps_le_tiny (X : ℝ) :
    highFksEps X ≤ Real.exp (-(0.7 * Real.sqrt X)) := by
  rw [highFksEps]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.sqrt_nonneg X]

theorem high_eps_nonneg (X : ℝ) : 0 ≤ highFksEps X := (Real.exp_pos _).le

/-- `X^n = exp(n·log X)` for `X > 0` — the bridge between power-type junk
factors and the exponential ledger. -/
theorem high_pow_eq_exp {X : ℝ} (hX0 : 0 < X) (n : ℕ) :
    X ^ n = Real.exp ((n:ℝ) * Real.log X) := by
  rw [Real.exp_nat_mul, Real.exp_log hX0]

end HighWindow

/-! ## Scale facts: `N = ⌊e^X⌋`, `M = ⌊X^2.05⌋`, `Q`, `T`, `A` -/

section HighScales

variable {X : ℝ}

/-- The low-window one-sided hypothesis holds on this window; lets the
`X`-one-sided lemmas of `ExplicitLowAveraging` be reused. -/
theorem high_le_low_window (hX : (8e26:ℝ) ≤ X) : (9.7e6:ℝ) ≤ X := by linarith

theorem high_N_lb (hX : (8e26:ℝ) ≤ X) : (4e26:ℝ) ≤ (lowN X : ℝ) := by
  have hfloor : Real.exp X / 2 ≤ (lowN X : ℝ) :=
    exp_div_two_le_expFloor (show (1:ℝ) ≤ X by linarith)
  have hexp : (8e26:ℝ) ≤ Real.exp X := by
    have := Real.add_one_le_exp X
    linarith
  linarith

/-! ### The shell cutoff `M = ⌊X^2.05⌋` -/

theorem high_M_cast_le_rpow (hX : (8e26:ℝ) ≤ X) : (lowM X : ℝ) ≤ X ^ (2.05:ℝ) :=
  Nat.floor_le (Real.rpow_nonneg (high_X_pos hX).le _)

theorem high_rpow_lt_M_add_one (X : ℝ) : X ^ (2.05:ℝ) < (lowM X : ℝ) + 1 := by
  exact_mod_cast Nat.lt_floor_add_one (X ^ (2.05:ℝ))

theorem high_rpow_le_cube (hX : (8e26:ℝ) ≤ X) : X ^ (2.05:ℝ) ≤ X ^ 3 := by
  have h3 : X ^ ((3:ℕ):ℝ) = X ^ (3:ℕ) := Real.rpow_natCast X 3
  calc X ^ (2.05:ℝ) ≤ X ^ ((3:ℕ):ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = X ^ 3 := h3

theorem high_sq_le_rpow (hX : (8e26:ℝ) ≤ X) : X ^ 2 ≤ X ^ (2.05:ℝ) := by
  have h2 : X ^ ((2:ℕ):ℝ) = X ^ (2:ℕ) := Real.rpow_natCast X 2
  calc X ^ 2 = X ^ ((2:ℕ):ℝ) := h2.symm
    _ ≤ X ^ (2.05:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)

theorem high_M_cast_le_cube (hX : (8e26:ℝ) ≤ X) : (lowM X : ℝ) ≤ X ^ 3 :=
  le_trans (high_M_cast_le_rpow hX) (high_rpow_le_cube hX)

/-- `log(m+1) ≤ 3 log X + 0.7` for every shell index `m ≤ M` (the paper's
`log(m+1) ≤ 2.05 log X + O(1)`). -/
theorem high_log_m_succ_le (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm : m ≤ lowM X) :
    Real.log ((m:ℝ) + 1) ≤ 3 * Real.log X + 0.7 := by
  have hM := high_M_cast_le_cube hX
  have hm' : (m:ℝ) ≤ (lowM X : ℝ) := Nat.cast_le.mpr hm
  have hX1 : (1:ℝ) ≤ X := by linarith
  have hcube1 : (1:ℝ) ≤ X ^ 3 := one_le_pow₀ hX1
  have hstep : Real.log ((m:ℝ) + 1) ≤ Real.log (2 * X ^ 3) :=
    Real.log_le_log (by positivity) (by nlinarith)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hstep
  have hlog2 := Real.log_two_lt_d9
  push_cast at hstep
  linarith

/-- The uniform log-denominator: `log(N/(m+1)) ≥ X − 3 log X − 1` on every
shell `m ≤ M` (the high-window replacement for the low file's `≥ X − 36`). -/
theorem high_loga_ge_logDenom (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm : m ≤ lowM X) :
    highLogDenom X ≤ Real.log ((lowN X : ℝ) / ((m:ℝ) + 1)) := by
  have hlog := high_log_m_succ_le hX hm
  have h := low_loga_lb (high_le_low_window hX) (m := m)
  rw [highLogDenom]
  linarith

theorem high_shell_a_ge_two (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm : m ≤ lowM X) :
    (2:ℝ) ≤ (lowN X : ℝ) / ((m:ℝ) + 1) := by
  have hpos : (0:ℝ) < (lowN X : ℝ) / ((m:ℝ) + 1) := by
    have := low_N_pos (high_le_low_window hX)
    positivity
  have hlog : Real.log 2 ≤ Real.log ((lowN X : ℝ) / ((m:ℝ) + 1)) := by
    have h := high_loga_ge_logDenom hX hm
    have hD := high_logDenom_lb hX
    nlinarith [Real.log_two_lt_d9]
  calc (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (Real.log ((lowN X : ℝ) / ((m:ℝ) + 1))) := Real.exp_le_exp.mpr hlog
    _ = (lowN X : ℝ) / ((m:ℝ) + 1) := Real.exp_log hpos

theorem high_loga_le_logb (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ lowM X) :
    Real.log ((lowN X : ℝ) / ((m:ℝ) + 1)) ≤ Real.log ((lowN X : ℝ) / (m:ℝ)) :=
  Real.log_le_log (lt_of_lt_of_le (by norm_num) (high_shell_a_ge_two hX hm))
    (low_shell_a_le_b (high_le_low_window hX) hm1)

theorem high_logb_pos (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ lowM X) : (0:ℝ) < Real.log ((lowN X : ℝ) / (m:ℝ)) := by
  have h1 := high_loga_ge_logDenom hX hm
  have h2 := high_loga_le_logb hX hm1 hm
  have h3 := high_logDenom_pos hX
  linarith

/-! ### The quotient scale `Q = ⌊N/(M+1)⌋` -/

theorem high_M_mul_le_N (hX : (8e26:ℝ) ≤ X) :
    lowM X * (lowM X + 1) ≤ lowN X := by
  have hX0 := high_X_pos hX
  have hM := high_M_cast_le_cube hX
  have hN : Real.exp X / 2 ≤ (lowN X : ℝ) :=
    exp_div_two_le_expFloor (by linarith)
  have hL := high_logX_le_sqrt hX
  have hs := high_sqrt_lb hX
  have hss := high_sqrt_sq hX
  have hX1 : (1:ℝ) ≤ X := by linarith
  have hcube1 : (1:ℝ) ≤ X ^ 3 := one_le_pow₀ hX1
  have hM0 : (0:ℝ) ≤ (lowM X : ℝ) := Nat.cast_nonneg _
  -- `M(M+1) ≤ 2X⁶ = 2·exp(6 log X) ≤ exp(X)/2 ≤ N`
  have hprod : (lowM X : ℝ) * ((lowM X : ℝ) + 1) ≤ 2 * X ^ 6 := by
    have h1 : (lowM X : ℝ) + 1 ≤ 2 * X ^ 3 := by linarith
    have h2 : (lowM X : ℝ) * ((lowM X : ℝ) + 1) ≤ X ^ 3 * (2 * X ^ 3) :=
      mul_le_mul hM h1 (by positivity) (by positivity)
    nlinarith
  have hexp6 : 2 * X ^ 6 ≤ Real.exp X / 2 := by
    have hpow := high_pow_eq_exp hX0 6
    have hmono : Real.exp ((6:ℝ) * Real.log X) ≤ Real.exp (X - 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hsplit : Real.exp (X - 2) * Real.exp 2 = Real.exp X := by
      rw [← Real.exp_add]; ring_nf
    have he2 : (4:ℝ) ≤ Real.exp 2 := by
      nlinarith [Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]
    nlinarith [Real.exp_pos (X - 2), hpow ▸ hmono]
  have hcast : ((lowM X * (lowM X + 1) : ℕ) : ℝ) ≤ (lowN X : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hcast

theorem high_M_le_Q (hX : (8e26:ℝ) ≤ X) :
    lowM X ≤ lowN X / (lowM X + 1) :=
  (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (high_M_mul_le_N hX)

theorem high_two_le_Q (hX : (8e26:ℝ) ≤ X) :
    2 ≤ lowN X / (lowM X + 1) :=
  le_trans (low_two_le_M (high_le_low_window hX)) (high_M_le_Q hX)

theorem high_hQ2 (hX : (8e26:ℝ) ≤ X) :
    lowN X < lowN X / (lowM X + 1) * (lowN X / (lowM X + 1)) := by
  have hX0 := high_X_pos hX
  have hX1 : (1:ℝ) ≤ X := by linarith
  have hL := high_logX_le_sqrt hX
  have hs := high_sqrt_lb hX
  have hss := high_sqrt_sq hX
  have hNexp : Real.exp X / 2 ≤ (lowN X : ℝ) :=
    exp_div_two_le_expFloor (by linarith)
  -- `N ≥ 32 X⁶`
  have hNbig : 32 * X ^ 6 ≤ (lowN X : ℝ) := by
    have hpow := high_pow_eq_exp hX0 6
    have hmono : Real.exp ((6:ℝ) * Real.log X) ≤ Real.exp (X - 5) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hsplit : Real.exp (X - 5) * Real.exp 5 = Real.exp X := by
      rw [← Real.exp_add]; ring_nf
    have he5 : (64:ℝ) ≤ Real.exp 5 := by
      have h5 := low_exp_nat_lb 5
      calc (64:ℝ) ≤ (2.7182818283:ℝ) ^ (5:ℕ) := by norm_num
        _ ≤ Real.exp ((5:ℕ):ℝ) := h5
        _ = Real.exp 5 := by norm_num
    nlinarith [Real.exp_pos (X - 5), hpow ▸ hmono]
  set W : ℝ := 2 * X ^ 3 with hWdef
  have hcube1 : (1:ℝ) ≤ X ^ 3 := one_le_pow₀ hX1
  have hW0 : (0:ℝ) < W := by rw [hWdef]; positivity
  have hM1W : (lowM X : ℝ) + 1 ≤ W := by
    have := high_M_cast_le_cube hX
    rw [hWdef]
    linarith
  have hqR : (lowN X:ℝ) / ((lowM X:ℝ) + 1) - 1
      < ((lowN X / (lowM X + 1) : ℕ) : ℝ) := by
    have h := low_nat_div_cast_lb (a := lowN X) (b := lowM X + 1) (Nat.succ_pos _)
    push_cast at h
    linarith
  have hN0 : (0:ℝ) < (lowN X:ℝ) := by
    have := high_N_lb hX
    linarith
  have hdiv : (lowN X:ℝ) / W ≤ (lowN X:ℝ) / ((lowM X:ℝ) + 1) :=
    div_le_div_of_nonneg_left hN0.le (by positivity) hM1W
  have hgap : (lowN X:ℝ) / (2 * W) ≤ (lowN X:ℝ) / W - 1 := by
    -- `N/W − N/(2W) = N/(2W) ≥ 1` since `N ≥ 2W`
    have h2W : 2 * W ≤ (lowN X:ℝ) := by
      rw [hWdef]
      nlinarith
    have hid : (lowN X:ℝ) / W - (lowN X:ℝ) / (2 * W) = (lowN X:ℝ) / (2 * W) := by
      field_simp
      ring
    have hone : (1:ℝ) ≤ (lowN X:ℝ) / (2 * W) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith
  set Q := lowN X / (lowM X + 1) with hQdef
  have hQlb : (lowN X:ℝ) / (2 * W) ≤ (Q:ℝ) := by linarith
  have hNQ : (lowN X:ℝ) ≤ 2 * W * (Q:ℝ) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * W)] at hQlb
    linarith
  have hQ0 : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg _
  have hsq : (lowN X:ℝ) * (lowN X:ℝ) ≤ (2 * W * (Q:ℝ)) * (2 * W * (Q:ℝ)) :=
    mul_le_mul hNQ hNQ hN0.le (by positivity)
  have hWsq : 4 * W ^ 2 < (lowN X:ℝ) := by
    rw [hWdef]
    nlinarith
  have hgoal : (lowN X:ℝ) < (Q:ℝ) * (Q:ℝ) := by nlinarith
  exact_mod_cast hgoal

theorem high_hQN (hX : (8e26:ℝ) ≤ X) : lowN X / (lowM X + 1) < lowN X :=
  low_hQN (high_le_low_window hX)

/-! ### The upper-estimate split index `T = ⌊highLogDenom X / log 2⌋` -/

theorem high_T_cast_lb (hX : (8e26:ℝ) ≤ X) : X ≤ (highT X : ℝ) := by
  have hfloor : highLogDenom X / Real.log 2 < (highT X : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hD := high_logDenom_lb hX
  have hkey : X + 1 ≤ highLogDenom X / Real.log 2 := by
    rw [le_div_iff₀ low_log2_pos]
    have hmul : (X + 1) * Real.log 2 ≤ (X + 1) * 0.6931471808 :=
      mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (by linarith)
    nlinarith
  linarith

theorem high_one_le_T (hX : (8e26:ℝ) ≤ X) : 1 ≤ highT X := by
  have h := high_T_cast_lb hX
  have h1 : (1:ℝ) ≤ (highT X : ℝ) := by linarith
  exact_mod_cast h1

theorem high_T_mul_log2_le (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm : m ≤ highT X) :
    (m:ℝ) * Real.log 2 ≤ highLogDenom X := by
  have hfl : (highT X : ℝ) ≤ highLogDenom X / Real.log 2 :=
    Nat.floor_le (div_nonneg (high_logDenom_pos hX).le low_log2_pos.le)
  have hm' : (m:ℝ) ≤ (highT X : ℝ) := Nat.cast_le.mpr hm
  calc (m:ℝ) * Real.log 2 ≤ highLogDenom X / Real.log 2 * Real.log 2 := by
        apply mul_le_mul_of_nonneg_right _ low_log2_pos.le
        linarith
    _ = highLogDenom X := div_mul_cancel₀ _ low_log2_pos.ne'

theorem high_T_cast_ub (hX : (8e26:ℝ) ≤ X) : (highT X : ℝ) ≤ 1.45 * X := by
  have hfl : (highT X : ℝ) ≤ highLogDenom X / Real.log 2 :=
    Nat.floor_le (div_nonneg (high_logDenom_pos hX).le low_log2_pos.le)
  have hub : highLogDenom X / Real.log 2 ≤ 1.45 * X := by
    rw [div_le_iff₀ low_log2_pos]
    have hgt := Real.log_two_gt_d9
    have hDle := high_logDenom_le hX
    nlinarith [high_X_pos hX]
  linarith

theorem high_T_le_M (hX : (8e26:ℝ) ≤ X) : highT X ≤ lowM X := by
  have hT := high_T_cast_ub hX
  have hM1 := high_rpow_lt_M_add_one X
  have hsq := high_sq_le_rpow hX
  have hcast : (highT X : ℝ) < (lowM X : ℝ) + 1 := by nlinarith [high_X_pos hX]
  have hnat : highT X < lowM X + 1 := by exact_mod_cast hcast
  omega

theorem high_log_T_add_one_ub (hX : (8e26:ℝ) ≤ X) :
    Real.log ((highT X : ℝ) + 1) ≤ Real.log X + 1 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  rw [Real.exp_add, high_exp_log hX]
  have he := Real.exp_one_gt_d9
  nlinarith [high_T_cast_ub hX, high_X_pos hX]

theorem high_log_T_ub (hX : (8e26:ℝ) ≤ X) :
    Real.log (highT X : ℝ) ≤ Real.log X + 1 := by
  have hT1 : (1:ℝ) ≤ (highT X : ℝ) := by exact_mod_cast high_one_le_T hX
  calc Real.log (highT X : ℝ) ≤ Real.log ((highT X : ℝ) + 1) :=
        Real.log_le_log (by linarith) (by linarith)
    _ ≤ Real.log X + 1 := high_log_T_add_one_ub hX

/-! ### The lower-estimate split index `A = ⌊X/(2 log 2)⌋` (shared `lowA`) -/

theorem high_A_cast_lb (hX : (8e26:ℝ) ≤ X) : 0.7 * X ≤ (lowA X : ℝ) := by
  have hfloor : X / (2 * Real.log 2) < (lowA X : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hkey : 0.7 * X + 1 ≤ X / (2 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.log 2)]
    have hmul : (0.7 * X + 1) * (2 * Real.log 2)
        ≤ (0.7 * X + 1) * 1.3862943616 := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith [Real.log_two_lt_d9]
    nlinarith
  linarith

theorem high_A_cast_ub (hX : (8e26:ℝ) ≤ X) : (lowA X : ℝ) ≤ 0.722 * X := by
  have hfl : (lowA X : ℝ) ≤ X / (2 * Real.log 2) :=
    Nat.floor_le (div_nonneg (by linarith) (by positivity))
  have hub : X / (2 * Real.log 2) ≤ 0.722 * X := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.log 2)]
    have hgt := Real.log_two_gt_d9
    nlinarith [high_X_pos hX]
  linarith

theorem high_A_le_M (hX : (8e26:ℝ) ≤ X) : lowA X ≤ lowM X := by
  have hA := high_A_cast_ub hX
  have hM1 := high_rpow_lt_M_add_one X
  have hsq := high_sq_le_rpow hX
  have hcast : (lowA X : ℝ) < (lowM X : ℝ) + 1 := by nlinarith [high_X_pos hX]
  have hnat : lowA X < lowM X + 1 := by exact_mod_cast hcast
  omega

theorem high_log_A_add_one_ub (hX : (8e26:ℝ) ≤ X) :
    Real.log ((lowA X : ℝ) + 1) ≤ Real.log X := by
  have hA := high_A_cast_ub hX
  exact Real.log_le_log (by positivity) (by nlinarith [high_X_pos hX])

end HighScales

/-! ## FKS endpoint errors and the two-sided shell counts -/

section HighShellCounts

variable {X : ℝ}

/-- Any point `t ≤ N` whose log clears the uniform denominator has FKS error
at most `N·ε(X)` with `ε(X) = exp(−0.79·√X)` — the high-window replacement
for `fksError_le_tiny`. -/
theorem high_fks_of_log_ge (hX : (8e26:ℝ) ≤ X) {t : ℝ} (ht0 : 0 ≤ t)
    (htN : t ≤ (lowN X : ℝ)) (hlog : highLogDenom X ≤ Real.log t) :
    fksError t ≤ (lowN X : ℝ) * highFksEps X := by
  have hD := high_logDenom_lb hX
  have hs := high_sqrt_lb hX
  have hss := high_sqrt_sq hX
  have hlog4e6 : (4 * 10 ^ 6 : ℝ) ≤ Real.log t := by nlinarith
  have h1 := fksError_le_of_log_ge ht0 hlog4e6
  have hsqrtlog : 0.99 * Real.sqrt X ≤ Real.sqrt (Real.log t) := by
    have h099 : (0.99:ℝ) * Real.sqrt X
        = Real.sqrt ((0.99 * Real.sqrt X) ^ 2) :=
      (Real.sqrt_sq (by positivity)).symm
    rw [h099]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hexp : Real.exp (-0.8 * Real.sqrt (Real.log t))
      ≤ Real.exp (-(0.792 * Real.sqrt X)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h10 : (10:ℝ) * Real.exp (-(0.792 * Real.sqrt X)) ≤ highFksEps X := by
    rw [highFksEps]
    have hkey : (10:ℝ) ≤ Real.exp (0.002 * Real.sqrt X) := by
      have := Real.add_one_le_exp (0.002 * Real.sqrt X)
      nlinarith
    have hsplit : Real.exp (0.002 * Real.sqrt X)
        * Real.exp (-(0.792 * Real.sqrt X)) = Real.exp (-(0.79 * Real.sqrt X)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith [Real.exp_pos (-(0.792 * Real.sqrt X))]
  have hNpos := low_N_pos (high_le_low_window hX)
  calc fksError t
      ≤ 10 * t * Real.exp (-0.8 * Real.sqrt (Real.log t)) := h1
    _ ≤ 10 * (lowN X : ℝ) * Real.exp (-(0.792 * Real.sqrt X)) := by
        apply mul_le_mul (by nlinarith) hexp (Real.exp_pos _).le (by positivity)
    _ = (lowN X : ℝ) * (10 * Real.exp (-(0.792 * Real.sqrt X))) := by ring
    _ ≤ (lowN X : ℝ) * highFksEps X := mul_le_mul_of_nonneg_left h10 hNpos.le

theorem high_fks_a (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm : m ≤ lowM X) :
    fksError ((lowN X : ℝ) / ((m:ℝ) + 1)) ≤ (lowN X : ℝ) * highFksEps X := by
  apply high_fks_of_log_ge hX (by positivity) _ (high_loga_ge_logDenom hX hm)
  apply div_le_self (low_N_pos (high_le_low_window hX)).le
  linarith [Nat.cast_nonneg (α := ℝ) m]

theorem high_fks_b (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ lowM X) :
    fksError ((lowN X : ℝ) / (m:ℝ)) ≤ (lowN X : ℝ) * highFksEps X := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  apply high_fks_of_log_ge hX (by positivity) _
    (le_trans (high_loga_ge_logDenom hX hm) (high_loga_le_logb hX hm1 hm))
  apply div_le_self (low_N_pos (high_le_low_window hX)).le
  exact_mod_cast hm1

/-- Upper shell count: `P_m ≤ (N c_m)/log(N/(m+1)) + 2N·ε(X)`
(eq. `explicit-shell-count`, upper half). -/
theorem high_shell_card_ub (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ lowM X) :
    ((shellPrimes (lowN X) m).card : ℝ)
      ≤ (lowN X : ℝ) / ((m:ℝ) * ((m:ℝ) + 1))
          / Real.log ((lowN X : ℝ) / ((m:ℝ) + 1))
        + 2 * (lowN X : ℝ) * highFksEps X := by
  refine shell_card_ub_of hm1 (high_shell_a_ge_two hX hm)
    (low_shell_a_le_b (high_le_low_window hX) hm1) ?_
  linarith [high_fks_a hX hm, high_fks_b hX hm1 hm,
    (by ring : (lowN X:ℝ) * highFksEps X + (lowN X:ℝ) * highFksEps X
      = 2 * (lowN X:ℝ) * highFksEps X)]

/-- Lower shell count: `(N c_m)/X − 2N·ε(X) ≤ P_m`. -/
theorem high_shell_card_lb (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ lowM X) :
    (lowN X : ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / X - 2 * (lowN X : ℝ) * highFksEps X
      ≤ ((shellPrimes (lowN X) m).card : ℝ) := by
  refine shell_card_lb_of hm1 (high_shell_a_ge_two hX hm)
    (low_shell_a_le_b (high_le_low_window hX) hm1) (high_logb_pos hX hm1 hm)
    (low_logb_le_X (high_le_low_window hX) hm1) ?_
  linarith [high_fks_a hX hm, high_fks_b hX hm1 hm,
    (by ring : (lowN X:ℝ) * highFksEps X + (lowN X:ℝ) * highFksEps X
      = 2 * (lowN X:ℝ) * highFksEps X)]

/-- Sharp lower shell count with the `log(N/m)` denominator (consumed by the
collision positive term). -/
theorem high_shell_card_lb_sharp (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ lowM X) :
    (lowN X : ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / Real.log ((lowN X : ℝ) / (m:ℝ))
        - 2 * (lowN X : ℝ) * highFksEps X
      ≤ ((shellPrimes (lowN X) m).card : ℝ) := by
  refine shell_card_lb_sharp_of hm1 (high_shell_a_ge_two hX hm)
    (low_shell_a_le_b (high_le_low_window hX) hm1) ?_
  linarith [high_fks_a hX hm, high_fks_b hX hm1 hm,
    (by ring : (lowN X:ℝ) * highFksEps X + (lowN X:ℝ) * highFksEps X
      = 2 * (lowN X:ℝ) * highFksEps X)]

/-- The FKS allowance is absorbed by any shell weight:
`8X·m(m+1)·ε(X) ≤ 1` for `m ≤ M`. -/
theorem high_eps_absorb (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm : m ≤ lowM X) :
    8 * X * ((m:ℝ) * ((m:ℝ) + 1)) * highFksEps X ≤ 1 := by
  have hX0 := high_X_pos hX
  have hX1 : (1:ℝ) ≤ X := by linarith
  have hL := high_logX_le_sqrt hX
  have hs := high_sqrt_lb hX
  have hss := high_sqrt_sq hX
  have hm' : (m:ℝ) ≤ X ^ 3 :=
    le_trans (Nat.cast_le.mpr hm) (high_M_cast_le_cube hX)
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _
  have hcube1 : (1:ℝ) ≤ X ^ 3 := one_le_pow₀ hX1
  have hprod : (m:ℝ) * ((m:ℝ) + 1) ≤ 2 * X ^ 6 := by
    have h2 : (m:ℝ) * ((m:ℝ) + 1) ≤ X ^ 3 * (2 * X ^ 3) :=
      mul_le_mul hm' (by linarith) (by positivity) (by positivity)
    nlinarith
  have hcoeff : 8 * X * ((m:ℝ) * ((m:ℝ) + 1)) ≤ X ^ 9 := by
    have h16 : 8 * X * (2 * X ^ 6) = 16 * X ^ 7 := by ring
    have hstep : 8 * X * ((m:ℝ) * ((m:ℝ) + 1)) ≤ 16 * X ^ 7 := by
      rw [← h16]
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    have h79 : 16 * X ^ 7 ≤ X ^ 9 := by
      have h2 : (16:ℝ) ≤ X ^ 2 := by nlinarith [mul_self_nonneg (X - 4)]
      calc 16 * X ^ 7 ≤ X ^ 2 * X ^ 7 :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = X ^ 9 := by ring
    linarith
  have hpow9 : X ^ 9 * highFksEps X ≤ 1 := by
    rw [highFksEps, high_pow_eq_exp hX0 9, ← Real.exp_add]
    calc Real.exp ((9:ℝ) * Real.log X + -(0.79 * Real.sqrt X))
        ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  calc 8 * X * ((m:ℝ) * ((m:ℝ) + 1)) * highFksEps X
      ≤ X ^ 9 * highFksEps X :=
        mul_le_mul_of_nonneg_right hcoeff (high_eps_nonneg X)
    _ ≤ 1 := hpow9

/-- Crude but positive lower shell count: `P_m ≥ N c_m/(2X) > 0`. -/
theorem high_shell_card_half_lb (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ lowM X) :
    (lowN X : ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / (2 * X)
      ≤ ((shellPrimes (lowN X) m).card : ℝ) := by
  have hlb := high_shell_card_lb hX hm1 hm
  have habs := high_eps_absorb hX hm
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hX0 := high_X_pos hX
  have hN0 := low_N_pos (high_le_low_window hX)
  have hkey : 2 * (lowN X : ℝ) * highFksEps X
      ≤ (lowN X : ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / (2 * X) := by
    rw [div_div, le_div_iff₀ (by positivity)]
    have h4 : 4 * X * ((m:ℝ) * ((m:ℝ) + 1)) * highFksEps X ≤ 1 := by
      nlinarith [high_eps_nonneg X,
        mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 4 * X)
          (by positivity : (0:ℝ) ≤ (m:ℝ) * ((m:ℝ) + 1))) (high_eps_nonneg X)]
    nlinarith [mul_le_mul_of_nonneg_left h4 hN0.le]
  have hhalf : (lowN X : ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / (2 * X)
        + (lowN X : ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / (2 * X)
      = (lowN X : ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / X := by
    field_simp
    ring
  linarith

/-- The `m`-th shell is nonempty on the window. -/
theorem high_shell_nonempty (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ lowM X) : (shellPrimes (lowN X) m).Nonempty := by
  have hlb := high_shell_card_half_lb hX hm1 hm
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hpos : (0:ℝ) < (lowN X : ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / (2 * X) := by
    have hN := low_N_pos (high_le_low_window hX)
    have hXp := high_X_pos hX
    positivity
  have hcard : 0 < (shellPrimes (lowN X) m).card := by
    by_contra hc
    have h0 : (shellPrimes (lowN X) m).card = 0 := by omega
    rw [h0] at hlb
    norm_num at hlb
    linarith
  exact Finset.card_pos.mp hcard

theorem high_shell_prime_gt_m (hX : (8e26:ℝ) ≤ X) {m p : ℕ}
    (hmM : m ≤ lowM X) (hp : p ∈ shellPrimes (lowN X) m) : m < p := by
  obtain ⟨hlo, -, -⟩ := mem_shellPrimes.mp hp
  have hchain : lowN X / (lowM X + 1) ≤ lowN X / (m + 1) :=
    Nat.div_le_div_left (by omega) (by omega)
  have hQM := high_M_le_Q hX
  omega

/-- Per-prime cap on the `m`-th shell:
`log σ_p(m) ≤ min(g(m), log(N/m))`. -/
theorem high_shell_logSum_le_card_mul_cap (hX : (8e26:ℝ) ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ lowM X) :
    ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ ((shellPrimes (lowN X) m).card : ℝ)
        * min (g m) (Real.log ((lowN X : ℝ) / (m:ℝ))) :=
  shell_logSum_le_card_mul_cap_of hm1
    (fun _p hp => high_shell_prime_gt_m hX hm hp)

end HighShellCounts

/-! ## Per-shell upper bounds (eq. `explicit-upper-start`, high window) -/

section HighUpperShells

variable {X : ℝ}

/-- Generic per-shell upper bound: normalize the capped shell sum by `X/N`
and insert the FKS count, leaving the exact factor plus uniform
`300X²·ε(X)` junk. -/
theorem high_shell_upper_generic (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m)
    (hmM : m ≤ lowM X) :
    X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ X * min (g m) (Real.log ((lowN X:ℝ) / (m:ℝ)))
          / ((m:ℝ) * ((m:ℝ) + 1)) / Real.log ((lowN X:ℝ) / ((m:ℝ) + 1))
        + 300 * X ^ 2 * highFksEps X := by
  have h1' := high_le_low_window hX
  have hLpos : (0:ℝ) < Real.log ((lowN X:ℝ) / ((m:ℝ) + 1)) := by
    have := high_loga_ge_logDenom hX hmM
    linarith [high_logDenom_pos hX]
  have hmu0 : 0 ≤ min (g m) (Real.log ((lowN X:ℝ) / (m:ℝ))) :=
    le_min (g_nonneg m) (high_logb_pos hX hm1 hmM).le
  have hmuX : min (g m) (Real.log ((lowN X:ℝ) / (m:ℝ))) ≤ X :=
    le_trans (min_le_right _ _) (low_logb_le_X h1' hm1)
  exact shell_upper_generic_of (Nv := (lowN X:ℝ)) (eps := highFksEps X)
    (low_N_pos h1') (by exact_mod_cast hm1) hLpos hmu0 hmuX (high_X_pos hX).le
    (high_eps_nonneg X) (high_shell_logSum_le_card_mul_cap hX hm1 hmM)
    (high_shell_card_ub hX hm1 hmM)

/-- Per-shell upper bound, head regime `m ≤ T` (fully clamped:
`g(m) ≤ m log 2 ≤ highLogDenom X ≤ log(N/(m+1))`). -/
theorem high_shell_upper_head (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m)
    (hmT : m ≤ highT X) :
    X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
        + Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9)
            / (((m:ℝ) + 1) * highLogDenom X))
        + 300 * X ^ 2 * highFksEps X := by
  have hmM : m ≤ lowM X := le_trans hmT (high_T_le_M hX)
  have hgeneric := high_shell_upper_generic hX hm1 hmM
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  exact shell_head_clamp_of hm0 (high_logDenom_pos hX)
    (high_loga_ge_logDenom hX hmM) (low_loga_le_X (high_le_low_window hX))
    (g_le_mul_log_two m) (high_T_mul_log2_le hX hmT)
    (high_loga_le_logb hX hm1 hmM)
    (by linarith [low_loga_lb (high_le_low_window hX) (m := m)])
    hgeneric

set_option maxHeartbeats 1000000 in
/-- Per-shell upper bound, tail regime `T < m ≤ M` (cap saturated at `X`). -/
theorem high_shell_upper_tail (hX : (8e26:ℝ) ≤ X) {m : ℕ}
    (hmT : highT X < m) (hmM : m ≤ lowM X) :
    X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
        + X / highLogDenom X * ((Real.log ((m:ℝ) + 1) + 1e-7)
            / ((m:ℝ) * ((m:ℝ) + 1)))
        + 300 * X ^ 2 * highFksEps X := by
  have h1' := high_le_low_window hX
  have hm1 : 1 ≤ m := le_trans (high_one_le_T hX) hmT.le
  have hgeneric := high_shell_upper_generic hX hm1 hmM
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hX0 : (0:ℝ) < X := high_X_pos hX
  have hmX : X ≤ (m:ℝ) := by
    have hT := high_T_cast_lb hX
    have hc : (highT X:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hmT
    linarith
  set L := Real.log ((lowN X:ℝ) / ((m:ℝ) + 1)) with hLdef
  have hLD : highLogDenom X ≤ L := high_loga_ge_logDenom hX hmM
  -- high-window-specific overflow numerator bound (the `X ≤ m`, `log X ≥ 61.9`
  -- estimate), the only part not shared with the low window
  have hlogb_ub := low_logb_ub h1' hm1
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
  have hXdelta : X * (Real.log ((m:ℝ) + 1) - Real.log (m:ℝ)) ≤ 1 := by
    have hXinvm : X * (1 / (m:ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one hm0]
      exact hmX
    calc X * (Real.log ((m:ℝ) + 1) - Real.log (m:ℝ)) ≤ X * (1 / (m:ℝ)) :=
          mul_le_mul_of_nonneg_left hdelta hX0.le
      _ ≤ 1 := hXinvm
  have hlogm1_lb : (61.9:ℝ) ≤ Real.log ((m:ℝ) + 1) := by
    have hstep : Real.log X ≤ Real.log ((m:ℝ) + 1) :=
      Real.log_le_log hX0 (by linarith)
    linarith [high_logX_lb hX]
  have hLsq : (X - Real.log ((m:ℝ) + 1) - 1e-9) ^ 2 ≤ L ^ 2 := by
    have hle : X - Real.log ((m:ℝ) + 1) - 1e-9 ≤ L := low_loga_lb h1' (m := m)
    have hD0 : (0:ℝ) < X - Real.log ((m:ℝ) + 1) - 1e-9 := by
      have h1 := high_log_m_succ_le hX hmM
      have h2 := high_logDenom_pos hX
      rw [highLogDenom] at h2
      linarith
    nlinarith
  have hnum : X * Real.log ((lowN X:ℝ) / (m:ℝ)) - L ^ 2
      ≤ X * (Real.log ((m:ℝ) + 1) + 1e-7) := by
    have hb' : X * Real.log ((lowN X:ℝ) / (m:ℝ)) ≤ X * (X - Real.log (m:ℝ)) :=
      mul_le_mul_of_nonneg_left hlogb_ub hX0.le
    have hexp : X * (X - Real.log (m:ℝ)) - (X - Real.log ((m:ℝ) + 1) - 1e-9) ^ 2
        ≤ X * (Real.log ((m:ℝ) + 1) + 1e-7) := by
      nlinarith [hXdelta, hlogm1_lb,
        sq_nonneg (Real.log ((m:ℝ) + 1) + 1e-9 - 61.9), hX0.le]
    nlinarith [hLsq]
  exact shell_upper_tail_of hm0 (high_logDenom_pos hX) hX0 hLD
    (low_loga_le_X h1') (high_loga_le_logb hX hm1 hmM)
    (by linarith [low_loga_lb h1' (m := m)]) hnum hgeneric

end HighUpperShells

/-! ## Summing the upper per-shell bounds -/

section HighUpperSums

variable {X : ℝ}

/-- The head sum (paper: `≤ (log 2/(X − log X − 1))(½(log X+1)² + 1)
< 1.72·10⁻²⁴`; realized as the symbolic `0.7003·((log X+1)²/2+1)/X` plus a
negligible floor-slop layer). -/
theorem high_head_sum_le (hX : (8e26:ℝ) ≤ X) :
    ∑ m ∈ Finset.Icc 1 (highT X),
        Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9)
          / (((m:ℝ) + 1) * highLogDenom X))
      ≤ 0.7003 * ((Real.log X + 1) ^ 2 / 2 + 1) / X
        + 1e-9 * (Real.log X + 2) / X := by
  have hDpos := high_logDenom_pos hX
  have hDlb := high_logDenom_lb hX
  have hX0 := high_X_pos hX
  have hbound : ∀ m ∈ Finset.Icc 1 (highT X),
      Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9)
          / (((m:ℝ) + 1) * highLogDenom X))
        ≤ Real.log 2 * Real.log ((m:ℝ) + 1) / ((m:ℝ) + 1) * (1 / highLogDenom X)
          + 1 / (m:ℝ) * (1e-9 * Real.log 2 / highLogDenom X) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
    have hsplit : Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9)
          / (((m:ℝ) + 1) * highLogDenom X))
        = Real.log 2 * Real.log ((m:ℝ) + 1) / ((m:ℝ) + 1) * (1 / highLogDenom X)
          + 1e-9 * Real.log 2 / (((m:ℝ) + 1) * highLogDenom X) := by
      field_simp
    have hmono : 1e-9 * Real.log 2 / (((m:ℝ) + 1) * highLogDenom X)
        ≤ 1 / (m:ℝ) * (1e-9 * Real.log 2 / highLogDenom X) := by
      have hR : 1 / (m:ℝ) * (1e-9 * Real.log 2 / highLogDenom X)
          = 1e-9 * Real.log 2 / ((m:ℝ) * highLogDenom X) := by
        field_simp
      rw [hR]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    rw [hsplit]
    linarith
  have hsum1 := sum_min_cap_error_le (highT X)
  have hsum2 := sum_one_div_le_log (highT X)
  have hlogT1 := high_log_T_add_one_ub hX
  have hlogT := high_log_T_ub hX
  have hT1 : (1:ℝ) ≤ (highT X : ℝ) := by exact_mod_cast high_one_le_T hX
  have hlogT0 : (0:ℝ) ≤ Real.log ((highT X:ℝ) + 1) := Real.log_nonneg (by linarith)
  have hL := high_logX_lb hX
  have hlog2u := Real.log_two_lt_d9
  have hlog2l := low_log2_pos
  have hstep1 : Real.log 2 * (Real.log ((highT X:ℝ) + 1) ^ 2 / 2 + 1)
        * (1 / highLogDenom X)
      ≤ 0.7003 * ((Real.log X + 1) ^ 2 / 2 + 1) / X := by
    have hsq : Real.log ((highT X:ℝ) + 1) ^ 2 ≤ (Real.log X + 1) ^ 2 := by
      nlinarith
    have hA : Real.log 2 * (Real.log ((highT X:ℝ) + 1) ^ 2 / 2 + 1)
        ≤ 0.6931472 * ((Real.log X + 1) ^ 2 / 2 + 1) := by nlinarith
    have hD1 : (1:ℝ) / highLogDenom X ≤ 1 / (0.99 * X) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hDlb
    have hA0 : (0:ℝ) ≤ Real.log 2 * (Real.log ((highT X:ℝ) + 1) ^ 2 / 2 + 1) := by
      positivity
    calc Real.log 2 * (Real.log ((highT X:ℝ) + 1) ^ 2 / 2 + 1)
          * (1 / highLogDenom X)
        ≤ 0.6931472 * ((Real.log X + 1) ^ 2 / 2 + 1) * (1 / (0.99 * X)) := by
          apply mul_le_mul hA hD1 (by positivity) (by nlinarith)
      _ = 0.6931472 / 0.99 * ((Real.log X + 1) ^ 2 / 2 + 1) / X := by
          field_simp
      _ ≤ 0.7003 * ((Real.log X + 1) ^ 2 / 2 + 1) / X := by
          apply div_le_div_of_nonneg_right _ hX0.le
          nlinarith [sq_nonneg (Real.log X + 1)]
  have hstep2 : (1 + Real.log (highT X : ℝ))
        * (1e-9 * Real.log 2 / highLogDenom X)
      ≤ 1e-9 * (Real.log X + 2) / X := by
    have hB : 1 + Real.log (highT X : ℝ) ≤ Real.log X + 2 := by linarith
    have hB0 : (0:ℝ) ≤ 1 + Real.log (highT X : ℝ) := by
      have := Real.log_nonneg hT1
      linarith
    have hc : 1e-9 * Real.log 2 / highLogDenom X ≤ 1e-9 / X := by
      have h1 : 1e-9 * Real.log 2 ≤ 1e-9 * 0.6931472 := by nlinarith
      calc 1e-9 * Real.log 2 / highLogDenom X
          ≤ 1e-9 * 0.6931472 / highLogDenom X :=
            div_le_div_of_nonneg_right h1 hDpos.le
        _ ≤ 1e-9 * 0.6931472 / (0.99 * X) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hDlb
        _ ≤ 1e-9 / X := by
            rw [div_le_div_iff₀ (by positivity) hX0]
            nlinarith
    have hc0 : (0:ℝ) ≤ 1e-9 * Real.log 2 / highLogDenom X := by positivity
    calc (1 + Real.log (highT X : ℝ)) * (1e-9 * Real.log 2 / highLogDenom X)
        ≤ (Real.log X + 2) * (1e-9 / X) :=
          mul_le_mul hB hc hc0 (by linarith)
      _ = 1e-9 * (Real.log X + 2) / X := by ring
  calc ∑ m ∈ Finset.Icc 1 (highT X),
        Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9)
          / (((m:ℝ) + 1) * highLogDenom X))
      ≤ ∑ m ∈ Finset.Icc 1 (highT X),
          (Real.log 2 * Real.log ((m:ℝ) + 1) / ((m:ℝ) + 1) * (1 / highLogDenom X)
            + 1 / (m:ℝ) * (1e-9 * Real.log 2 / highLogDenom X)) :=
        Finset.sum_le_sum hbound
    _ = (∑ m ∈ Finset.Icc 1 (highT X),
            Real.log 2 * Real.log ((m:ℝ) + 1) / ((m:ℝ) + 1)) * (1 / highLogDenom X)
        + (∑ m ∈ Finset.Icc 1 (highT X), 1 / (m:ℝ))
            * (1e-9 * Real.log 2 / highLogDenom X) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ Real.log 2 * (Real.log ((highT X:ℝ) + 1) ^ 2 / 2 + 1) * (1 / highLogDenom X)
        + (1 + Real.log (highT X : ℝ)) * (1e-9 * Real.log 2 / highLogDenom X) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hsum1 (by positivity)
        · exact mul_le_mul_of_nonneg_right hsum2 (by positivity)
    _ ≤ 0.7003 * ((Real.log X + 1) ^ 2 / 2 + 1) / X
        + 1e-9 * (Real.log X + 2) / X := add_le_add hstep1 hstep2

/-- The tail sum (paper: `≤ (X/(X − 3 log X))((log X + 2)/X + 1/(2X²))
< 8·10⁻²⁶`; realized as `(1.02(log X + 2) + 10⁻⁶)/X`). -/
theorem high_tail_sum_le (hX : (8e26:ℝ) ≤ X) :
    ∑ m ∈ Finset.Ioc (highT X) (lowM X),
        X / highLogDenom X * ((Real.log ((m:ℝ) + 1) + 1e-7)
          / ((m:ℝ) * ((m:ℝ) + 1)))
      ≤ (1.02 * (Real.log X + 2) + 1e-6) / X := by
  have hXD := high_X_div_logDenom_ub hX
  have hX0 := high_X_pos hX
  have hT := high_T_cast_lb hX
  have hL := high_logX_lb hX
  rw [← Finset.mul_sum]
  have hterm : ∀ m ∈ Finset.Ioc (highT X) (lowM X),
      (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ (1 + 1e-26) * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1)))
          + 1e-7 * (1 / ((m:ℝ) * (m:ℝ))) := by
    intro m hm
    have hmT : highT X < m := (Finset.mem_Ioc.mp hm).1
    have hm' : X ≤ (m:ℝ) := by
      have : (highT X:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hmT
      linarith
    have hm0 : (0:ℝ) < (m:ℝ) := by linarith
    have hL0 : (0:ℝ) ≤ Real.log ((m:ℝ) + 1) := Real.log_nonneg (by linarith)
    have hsplit : (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))
        = Real.log ((m:ℝ) + 1) / ((m:ℝ) * ((m:ℝ) + 1))
          + 1e-7 / ((m:ℝ) * ((m:ℝ) + 1)) := by
      rw [add_div]
    have hpiece1 : Real.log ((m:ℝ) + 1) / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ (1 + 1e-26) * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1))) := by
      have hw : (1:ℝ) / ((m:ℝ) * ((m:ℝ) + 1))
          ≤ (1 + 1e-26) / (((m:ℝ) + 1) * ((m:ℝ) + 1)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc Real.log ((m:ℝ) + 1) / ((m:ℝ) * ((m:ℝ) + 1))
          = Real.log ((m:ℝ) + 1) * (1 / ((m:ℝ) * ((m:ℝ) + 1))) := by
            rw [mul_one_div]
        _ ≤ Real.log ((m:ℝ) + 1) * ((1 + 1e-26) / (((m:ℝ) + 1) * ((m:ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hw hL0
        _ = (1 + 1e-26) * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1))) := by
            field_simp
    have hpiece2 : (1e-7:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) ≤ 1e-7 * (1 / ((m:ℝ) * (m:ℝ))) := by
      rw [mul_one_div]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    rw [hsplit]
    linarith
  have hT3 : 3 ≤ highT X := by
    have h3 : (3:ℝ) ≤ (highT X:ℝ) := by linarith
    exact_mod_cast h3
  have hsum1 := sum_log_div_sq_tail_le (highT X) (lowM X) hT3
  have hsum2 := sum_one_div_Ioc_le (highT X) (lowM X) (high_one_le_T hX)
  have hlogT1 := high_log_T_add_one_ub hX
  have hinner : ∑ m ∈ Finset.Ioc (highT X) (lowM X),
      (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))
      ≤ (1 + 1e-26) * ((Real.log X + 2) / X) + 1e-7 * (1 / X) := by
    have hs1' : (Real.log ((highT X:ℝ) + 1) + 1) / ((highT X:ℝ) + 1)
        ≤ (Real.log X + 2) / X := by
      apply div_le_div₀ (by linarith) (by linarith) hX0 (by linarith)
    have hs2' : (1:ℝ) / (highT X : ℝ) ≤ 1 / X :=
      div_le_div_of_nonneg_left (by norm_num) hX0 hT
    calc ∑ m ∈ Finset.Ioc (highT X) (lowM X),
          (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ ∑ m ∈ Finset.Ioc (highT X) (lowM X),
            ((1 + 1e-26) * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1)))
              + 1e-7 * (1 / ((m:ℝ) * (m:ℝ)))) := Finset.sum_le_sum hterm
      _ = (1 + 1e-26) * ∑ m ∈ Finset.Ioc (highT X) (lowM X),
            Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1))
          + 1e-7 * ∑ m ∈ Finset.Ioc (highT X) (lowM X), 1 / ((m:ℝ) * (m:ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (1 + 1e-26) * ((Real.log X + 2) / X) + 1e-7 * (1 / X) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (by norm_num)
            linarith [hsum1, hs1']
          · apply mul_le_mul_of_nonneg_left _ (by norm_num)
            linarith [hsum2, hs2']
  have hinner0 : (0:ℝ) ≤ ∑ m ∈ Finset.Ioc (highT X) (lowM X),
      (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1)) := by
    apply Finset.sum_nonneg
    intro m hm
    have hmT : highT X < m := (Finset.mem_Ioc.mp hm).1
    have hm0 : (0:ℝ) < (m:ℝ) := by
      have : 1 ≤ m := by
        have := high_one_le_T hX
        omega
      exact_mod_cast this
    have : (0:ℝ) ≤ Real.log ((m:ℝ) + 1) := Real.log_nonneg (by linarith)
    positivity
  calc X / highLogDenom X * ∑ m ∈ Finset.Ioc (highT X) (lowM X),
        (Real.log ((m:ℝ) + 1) + 1e-7) / ((m:ℝ) * ((m:ℝ) + 1))
      ≤ 1.011 * ((1 + 1e-26) * ((Real.log X + 2) / X) + 1e-7 * (1 / X)) :=
        mul_le_mul hXD hinner hinner0 (by norm_num)
    _ = (1.011 * (1 + 1e-26) * (Real.log X + 2) + 1.011e-7) / X := by
        field_simp
        ring
    _ ≤ (1.02 * (Real.log X + 2) + 1e-6) / X := by
        apply div_le_div_of_nonneg_right _ hX0.le
        nlinarith

/-- The junk total: `M` shells, each carrying `300X²·ε(X)`, absorbed into
`exp(−0.7√X)`. -/
theorem high_junk_total_le (hX : (8e26:ℝ) ≤ X) :
    (lowM X : ℝ) * (300 * X ^ 2 * highFksEps X)
      ≤ Real.exp (-(0.7 * Real.sqrt X)) := by
  have hX0 := high_X_pos hX
  have hL := high_logX_le_sqrt hX
  have hs := high_sqrt_lb hX
  have hM := high_M_cast_le_cube hX
  have hM0 : (0:ℝ) ≤ (lowM X:ℝ) := Nat.cast_nonneg _
  have hcoeff : (lowM X:ℝ) * (300 * X ^ 2) ≤ X ^ 6 := by
    have hstep : (lowM X:ℝ) * (300 * X ^ 2) ≤ X ^ 3 * (X * X ^ 2) := by
      apply mul_le_mul hM _ (by positivity) (by positivity)
      nlinarith
    nlinarith
  have hpow : X ^ 6 * highFksEps X ≤ Real.exp (-(0.7 * Real.sqrt X)) := by
    rw [highFksEps, high_pow_eq_exp hX0 6, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc (lowM X:ℝ) * (300 * X ^ 2 * highFksEps X)
      = (lowM X:ℝ) * (300 * X ^ 2) * highFksEps X := by ring
    _ ≤ X ^ 6 * highFksEps X :=
        mul_le_mul_of_nonneg_right hcoeff (high_eps_nonneg X)
    _ ≤ Real.exp (-(0.7 * Real.sqrt X)) := hpow

/-- The full upper shell-sum estimate. -/
theorem high_sum_upper (hX : (8e26:ℝ) ≤ X) :
    X / (lowN X:ℝ)
        * ∑ m ∈ Finset.Icc 1 (lowM X),
            ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ (∑ m ∈ Finset.Icc 1 (lowM X), min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)))
        + (0.7003 * ((Real.log X + 1) ^ 2 / 2 + 1) / X
            + 1e-9 * (Real.log X + 2) / X
            + (1.02 * (Real.log X + 2) + 1e-6) / X
            + Real.exp (-(0.7 * Real.sqrt X))) := by
  have hTM := high_T_le_M hX
  have hunion : Finset.Icc 1 (lowM X)
      = Finset.Icc 1 (highT X) ∪ Finset.Ioc (highT X) (lowM X) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (highT X))
      (Finset.Ioc (highT X) (lowM X)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1
    simp only [Finset.mem_Ioc] at hk2
    omega
  rw [Finset.mul_sum, hunion, Finset.sum_union hdisj, Finset.sum_union hdisj]
  have hhead : ∑ m ∈ Finset.Icc 1 (highT X),
      X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ (∑ m ∈ Finset.Icc 1 (highT X), min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)))
        + ((∑ m ∈ Finset.Icc 1 (highT X),
            Real.log 2 * ((Real.log ((m:ℝ) + 1) + 1e-9)
              / (((m:ℝ) + 1) * highLogDenom X)))
          + ∑ _m ∈ Finset.Icc 1 (highT X), 300 * X ^ 2 * highFksEps X) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro m hm
    have hmem := Finset.mem_Icc.mp hm
    linarith [high_shell_upper_head hX hmem.1 hmem.2]
  have htail : ∑ m ∈ Finset.Ioc (highT X) (lowM X),
      X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m)
      ≤ (∑ m ∈ Finset.Ioc (highT X) (lowM X), min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)))
        + ((∑ m ∈ Finset.Ioc (highT X) (lowM X),
            X / highLogDenom X * ((Real.log ((m:ℝ) + 1) + 1e-7)
              / ((m:ℝ) * ((m:ℝ) + 1))))
          + ∑ _m ∈ Finset.Ioc (highT X) (lowM X), 300 * X ^ 2 * highFksEps X) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro m hm
    have hmem := Finset.mem_Ioc.mp hm
    linarith [high_shell_upper_tail hX hmem.1 hmem.2]
  have hheadsum := high_head_sum_le hX
  have htailsum := high_tail_sum_le hX
  have hjunk : (∑ _m ∈ Finset.Icc 1 (highT X), 300 * X ^ 2 * highFksEps X)
      + (∑ _m ∈ Finset.Ioc (highT X) (lowM X), 300 * X ^ 2 * highFksEps X)
      ≤ Real.exp (-(0.7 * Real.sqrt X)) := by
    rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, Nat.card_Ioc,
      nsmul_eq_mul, nsmul_eq_mul]
    have hcast : ((highT X + 1 - 1 : ℕ) : ℝ) + ((lowM X - highT X : ℕ) : ℝ)
        = (lowM X : ℝ) := by
      rw [Nat.cast_sub hTM]
      simp
    calc ((highT X + 1 - 1 : ℕ) : ℝ) * (300 * X ^ 2 * highFksEps X)
          + ((lowM X - highT X : ℕ) : ℝ) * (300 * X ^ 2 * highFksEps X)
        = (lowM X : ℝ) * (300 * X ^ 2 * highFksEps X) := by
          rw [← add_mul, hcast]
      _ ≤ Real.exp (-(0.7 * Real.sqrt X)) := high_junk_total_le hX
  linarith

end HighUpperSums

/-! ## The fibre core and the normalization bridge -/

section HighCoreBridge

variable {X : ℝ}

set_option maxHeartbeats 1000000 in
/-- The normalized fibre cost (paper: `2X^{−1.05} < 1.2·10⁻²⁸`; realized as
`≤ 0.1/X`, dominated by `X·log 4/(M+1) ≤ 1.39·X^{−1.05} ≤ (1.39/22)/X`). -/
theorem high_core (hX : (8e26:ℝ) ≤ X) :
    X / (lowN X:ℝ) * (Real.log ((harmonicSum (lowN X) : ℝ) + 1)
        + Real.log (smoothPart (lowN X / (lowM X + 1)) (lowN X))) ≤ 0.1 / X := by
  have h1' := high_le_low_window hX
  have hNpos := low_N_pos h1'
  have hX0 := high_X_pos hX
  have hL61 := high_logX_lb hX
  have hL := high_logX_le_sqrt hX
  have hs := high_sqrt_lb hX
  have hss := high_sqrt_sq hX
  have hNexp : Real.exp X / 2 ≤ (lowN X:ℝ) :=
    exp_div_two_le_expFloor (by linarith)
  have htiny := high_tiny_le hX
  have hH : Real.log ((harmonicSum (lowN X) : ℝ) + 1) ≤ X := by
    have hH0 : (0:ℝ) ≤ ((harmonicSum (lowN X) : ℚ) : ℝ) := by
      exact_mod_cast harmonicSum_nonneg (lowN X)
    rw [Real.log_le_iff_le_exp (by linarith)]
    have hHle : ((harmonicSum (lowN X) : ℚ) : ℝ) ≤ 1 + Real.log (lowN X) :=
      harmonicSum_le_one_add_log (lowN X)
    have hlogN := low_logN_ub h1'
    have hq := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ X by linarith)
    nlinarith
  have hD : Real.log (smoothPart (lowN X / (lowM X + 1)) (lowN X))
      ≤ Real.log 4 * ((lowN X / (lowM X + 1) : ℕ) : ℝ)
        + Real.sqrt (lowN X) * X := by
    have hsmooth := log_smoothPart_le (high_two_le_Q hX)
      (Nat.div_le_self (lowN X) (lowM X + 1))
    have hth := chebyshevTheta_le_log_four_mul
      (Nat.cast_nonneg (lowN X / (lowM X + 1)) : (0:ℝ) ≤ _)
    have hsqrtlog : Real.sqrt (lowN X) * Real.log (lowN X)
        ≤ Real.sqrt (lowN X) * X :=
      mul_le_mul_of_nonneg_left (low_logN_ub h1') (Real.sqrt_nonneg _)
    linarith
  have hXN0 : (0:ℝ) ≤ X / (lowN X:ℝ) := by positivity
  have hstep : X / (lowN X:ℝ) * (Real.log ((harmonicSum (lowN X) : ℝ) + 1)
        + Real.log (smoothPart (lowN X / (lowM X + 1)) (lowN X)))
      ≤ X / (lowN X:ℝ) * (X + (Real.log 4 * ((lowN X / (lowM X + 1) : ℕ) : ℝ)
          + Real.sqrt (lowN X) * X)) := by
    apply mul_le_mul_of_nonneg_left _ hXN0
    linarith
  have hinvN : 1 / (lowN X:ℝ) ≤ 2 * Real.exp (-X) := by
    calc 1 / (lowN X:ℝ) ≤ 1 / (Real.exp X / 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hNexp
      _ = 2 * Real.exp (-X) := by
          rw [Real.exp_neg]
          field_simp
  -- piece 1: `X²/N ≤ 2X²e^{−X} ≤ X³e^{−X} ≤ exp(−0.7√X) ≤ 0.001/X`
  have hexp3X : X ^ 3 * Real.exp (-X) ≤ Real.exp (-(0.7 * Real.sqrt X)) := by
    rw [high_pow_eq_exp hX0 3, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpiece1 : X / (lowN X:ℝ) * X ≤ 0.001 / X := by
    have hid : X / (lowN X:ℝ) * X = X ^ 2 * (1 / (lowN X:ℝ)) := by ring
    have hchain : X ^ 2 * (1 / (lowN X:ℝ)) ≤ X ^ 2 * (2 * Real.exp (-X)) :=
      mul_le_mul_of_nonneg_left hinvN (by positivity)
    have h2X : X ^ 2 * (2 * Real.exp (-X)) ≤ X ^ 3 * Real.exp (-X) := by
      have hEpos := Real.exp_pos (-X)
      nlinarith [mul_nonneg (show (0:ℝ) ≤ X - 2 by linarith)
        (mul_pos (pow_pos hX0 2) hEpos).le]
    rw [hid]
    linarith
  -- piece 2: `X·log4/(M+1) ≤ 1.39·X^{−1.05} ≤ (1.39/22)/X ≤ 0.07/X`
  have hlog4 : Real.log 4 ≤ 1.3862943616 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_lt_d9]
  have hlog4pos : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hQle : ((lowN X / (lowM X + 1) : ℕ) : ℝ) ≤ (lowN X:ℝ) / ((lowM X:ℝ) + 1) := by
    have := Nat.cast_div_le (m := lowN X) (n := lowM X + 1) (α := ℝ)
    push_cast at this
    linarith
  have hpiece2 : X / (lowN X:ℝ)
      * (Real.log 4 * ((lowN X / (lowM X + 1) : ℕ) : ℝ)) ≤ 0.07 / X := by
    have hMpos : (0:ℝ) < (lowM X:ℝ) + 1 := by positivity
    have hchain : X / (lowN X:ℝ) * (Real.log 4 * ((lowN X / (lowM X + 1) : ℕ) : ℝ))
        ≤ X / (lowN X:ℝ) * (Real.log 4 * ((lowN X:ℝ) / ((lowM X:ℝ) + 1))) := by
      apply mul_le_mul_of_nonneg_left _ hXN0
      exact mul_le_mul_of_nonneg_left hQle hlog4pos
    have hid : X / (lowN X:ℝ) * (Real.log 4 * ((lowN X:ℝ) / ((lowM X:ℝ) + 1)))
        = X * Real.log 4 / ((lowM X:ℝ) + 1) := by
      field_simp
    have hrpow_pos : (0:ℝ) < X ^ (2.05:ℝ) := Real.rpow_pos_of_pos hX0 _
    have hXdiv : X * Real.log 4 / ((lowM X:ℝ) + 1)
        ≤ X * 1.3862943616 / X ^ (2.05:ℝ) := by
      apply div_le_div₀ (by positivity) _ hrpow_pos (high_rpow_lt_M_add_one X).le
      nlinarith
    have hrpow_exp : X * 1.3862943616 / X ^ (2.05:ℝ)
        = 1.3862943616 * Real.exp (Real.log X - 2.05 * Real.log X) := by
      rw [Real.rpow_def_of_pos hX0, Real.exp_sub, high_exp_log hX]
      rw [mul_comm (Real.log X) (2.05:ℝ)]
      ring
    have hexp105 : Real.exp (Real.log X - 2.05 * Real.log X) ≤ 1 / 22 * (1 / X) := by
      have hid2 : Real.log X - 2.05 * Real.log X
          = -(0.05 * Real.log X) + -(Real.log X) := by ring
      rw [hid2, Real.exp_add]
      have h22 : (22:ℝ) ≤ Real.exp (0.05 * Real.log X) := by
        have hmono : Real.exp 3.095 ≤ Real.exp (0.05 * Real.log X) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have h3 : (20.08:ℝ) ≤ Real.exp 3 := by
          calc (20.08:ℝ) ≤ (2.7182818283:ℝ) ^ (3:ℕ) := by norm_num
            _ ≤ Real.exp ((3:ℕ):ℝ) := low_exp_nat_lb 3
            _ = Real.exp 3 := by norm_num
        have h0095 : (1.0995:ℝ) ≤ Real.exp 0.095 := by
          nlinarith [Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.095 by norm_num)]
        have hsplit3 : Real.exp 3 * Real.exp 0.095 = Real.exp 3.095 := by
          rw [← Real.exp_add]
          norm_num
        nlinarith [Real.exp_pos 3, Real.exp_pos 0.095]
      have h1 : Real.exp (-(0.05 * Real.log X)) ≤ 1 / 22 := by
        have hmul : Real.exp (-(0.05 * Real.log X))
            * Real.exp (0.05 * Real.log X) = 1 := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        nlinarith [Real.exp_pos (-(0.05 * Real.log X))]
      have h2 : Real.exp (-(Real.log X)) = 1 / X := by
        rw [Real.exp_neg, high_exp_log hX, one_div]
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hfin : 1.3862943616 * Real.exp (Real.log X - 2.05 * Real.log X)
        ≤ 0.07 / X := by
      calc 1.3862943616 * Real.exp (Real.log X - 2.05 * Real.log X)
          ≤ 1.3862943616 * (1 / 22 * (1 / X)) := by
            apply mul_le_mul_of_nonneg_left hexp105 (by norm_num)
        _ ≤ 0.07 / X := by
            rw [div_eq_mul_one_div (0.07:ℝ) X]
            nlinarith [show (0:ℝ) ≤ 1 / X by positivity]
    linarith [hid ▸ hchain, hrpow_exp ▸ hXdiv]
  -- piece 3: `X²/√N ≤ 2X²e^{−X/2} ≤ exp(−0.7√X) ≤ 0.001/X`
  have hpiece3 : X / (lowN X:ℝ) * (Real.sqrt (lowN X) * X) ≤ 0.001 / X := by
    have hsqrtN_lb : Real.exp (X / 2) / 2 ≤ Real.sqrt (lowN X) := by
      have hexpsq : Real.exp (X / 2) * Real.exp (X / 2) = Real.exp X := by
        rw [← Real.exp_add]
        ring_nf
      have hsq : (Real.exp (X / 2) / 2) ^ 2 ≤ (lowN X:ℝ) := by
        nlinarith [Real.exp_pos (X / 2)]
      calc Real.exp (X / 2) / 2
          = Real.sqrt ((Real.exp (X / 2) / 2) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (lowN X) := Real.sqrt_le_sqrt hsq
    have hNs : Real.sqrt (lowN X) * Real.sqrt (lowN X) = (lowN X:ℝ) :=
      Real.mul_self_sqrt hNpos.le
    have hsqrtN_ub : Real.sqrt (lowN X) ≤ (lowN X:ℝ) * (2 * Real.exp (-(X / 2))) := by
      have hspos : (0:ℝ) < Real.sqrt (lowN X) := Real.sqrt_pos.mpr hNpos
      have h1 : Real.sqrt (lowN X) * (Real.exp (X / 2) / 2)
          ≤ Real.sqrt (lowN X) * Real.sqrt (lowN X) :=
        mul_le_mul_of_nonneg_left hsqrtN_lb hspos.le
      rw [hNs] at h1
      have hE := Real.exp_pos (X / 2)
      have h2 : Real.sqrt (lowN X) ≤ 2 * (lowN X:ℝ) / Real.exp (X / 2) := by
        rw [le_div_iff₀ hE]
        linarith
      calc Real.sqrt (lowN X) ≤ 2 * (lowN X:ℝ) / Real.exp (X / 2) := h2
        _ = (lowN X:ℝ) * (2 * Real.exp (-(X / 2))) := by
            rw [Real.exp_neg]
            field_simp
    have hchain : X / (lowN X:ℝ) * (Real.sqrt (lowN X) * X)
        ≤ X / (lowN X:ℝ) * ((lowN X:ℝ) * (2 * Real.exp (-(X / 2))) * X) := by
      apply mul_le_mul_of_nonneg_left _ hXN0
      exact mul_le_mul_of_nonneg_right hsqrtN_ub (by linarith)
    have hid : X / (lowN X:ℝ) * ((lowN X:ℝ) * (2 * Real.exp (-(X / 2))) * X)
        = 2 * X ^ 2 * Real.exp (-(X / 2)) := by
      field_simp
    have hexp3 : 2 * X ^ 2 * Real.exp (-(X / 2))
        ≤ Real.exp (-(0.7 * Real.sqrt X)) := by
      have h2X : 2 * X ^ 2 ≤ X ^ 3 := by nlinarith
      have hp : X ^ 3 * Real.exp (-(X / 2)) ≤ Real.exp (-(0.7 * Real.sqrt X)) := by
        rw [high_pow_eq_exp hX0 3, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      nlinarith [Real.exp_pos (-(X / 2))]
    linarith [hid ▸ hchain]
  have hexpand : X / (lowN X:ℝ) * (X + (Real.log 4 * ((lowN X / (lowM X + 1) : ℕ) : ℝ)
        + Real.sqrt (lowN X) * X))
      = X / (lowN X:ℝ) * X
        + X / (lowN X:ℝ) * (Real.log 4 * ((lowN X / (lowM X + 1) : ℕ) : ℝ))
        + X / (lowN X:ℝ) * (Real.sqrt (lowN X) * X) := by
    ring
  rw [hexpand] at hstep
  have hchain2 : X / (lowN X:ℝ) * (Real.log ((harmonicSum (lowN X) : ℝ) + 1)
      + Real.log (smoothPart (lowN X / (lowM X + 1)) (lowN X)))
      ≤ 0.001 / X + 0.07 / X + 0.001 / X := by linarith
  have hfin : (0.001:ℝ) / X + 0.07 / X + 0.001 / X ≤ 0.1 / X := by
    have h : (0.001:ℝ) / X + 0.07 / X + 0.001 / X = 0.072 / X := by ring
    rw [h]
    exact div_le_div_of_nonneg_right (by norm_num) hX0.le
  linarith

/-- The normalization bridge: `|F(e^X) − (X/N)·g(N)| ≤ 0.001/X`. -/
theorem high_bridge (hX : (8e26:ℝ) ≤ X) :
    |FReal (Real.exp X) - X / (lowN X:ℝ) * g (lowN X)| ≤ 0.001 / X := by
  have h := abs_FReal_exp_sub_div_floor (show (1:ℝ) ≤ X by linarith)
  have hX0 := high_X_pos hX
  have hbound : X * Real.log 2 / Real.exp X ≤ 0.001 / X := by
    have hid : X * Real.log 2 / Real.exp X = X * Real.log 2 * Real.exp (-X) := by
      rw [Real.exp_neg]
      ring
    have hstep : X * Real.log 2 * Real.exp (-X) ≤ X * Real.exp (-X) := by
      have hE := Real.exp_pos (-X)
      nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 - Real.log 2 by
        nlinarith [Real.log_two_lt_d9]) (mul_pos hX0 hE).le]
    have hXexp : X * Real.exp (-X) = Real.exp (Real.log X + -X) := by
      rw [Real.exp_add, high_exp_log hX]
    have hmono : Real.exp (Real.log X + -X) ≤ Real.exp (-(0.7 * Real.sqrt X)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [high_logX_le_sqrt hX, high_sqrt_lb hX, high_sqrt_sq hX]
    calc X * Real.log 2 / Real.exp X = X * Real.log 2 * Real.exp (-X) := hid
      _ ≤ X * Real.exp (-X) := hstep
      _ = Real.exp (Real.log X + -X) := hXexp
      _ ≤ Real.exp (-(0.7 * Real.sqrt X)) := hmono
      _ ≤ 0.001 / X := high_tiny_le hX
  exact le_trans h hbound

end HighCoreBridge

/-! ## The upper half of the master enclosure -/

/-- **Upper master bound**: `𝓡(X) ≤ (0.7003((log X+1)²/2+1) +
1.021(log X+2) + 0.2)/X` for `X ≥ 8·10²⁶`. -/
theorem high_averaging_upper {X : ℝ} (hX : (8e26:ℝ) ≤ X) :
    averagingError X
      ≤ (0.7003 * ((Real.log X + 1) ^ 2 / 2 + 1)
          + 1.021 * (Real.log X + 2) + 0.2) / X := by
  have h1' := high_le_low_window hX
  have hX0 := high_X_pos hX
  have hL := high_logX_lb hX
  have hbridge := high_bridge hX
  have hdec := (g_shell_decomposition (N := lowN X) (M := lowM X)
    (high_hQN hX) (high_hQ2 hX)).2
  have hcore := high_core hX
  have hsum := high_sum_upper hX
  have hpartial := low_partial_le_B (show (0:ℝ) ≤ X by linarith) (lowM X)
  have htiny := high_tiny_le hX
  have hXN0 : (0:ℝ) ≤ X / (lowN X:ℝ) :=
    div_nonneg (by linarith) (low_N_pos h1').le
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
  have hF : FReal (Real.exp X) ≤ X / (lowN X:ℝ) * g (lowN X) + 0.001 / X := by
    linarith [(abs_le.mp hbridge).2]
  have hcomb : 0.7003 * ((Real.log X + 1) ^ 2 / 2 + 1) / X
        + 1e-9 * (Real.log X + 2) / X
        + (1.02 * (Real.log X + 2) + 1e-6) / X
        + 0.001 / X + 0.1 / X + 0.001 / X
      ≤ (0.7003 * ((Real.log X + 1) ^ 2 / 2 + 1)
          + 1.021 * (Real.log X + 2) + 0.2) / X := by
    have hid : 0.7003 * ((Real.log X + 1) ^ 2 / 2 + 1) / X
          + 1e-9 * (Real.log X + 2) / X
          + (1.02 * (Real.log X + 2) + 1e-6) / X
          + 0.001 / X + 0.1 / X + 0.001 / X
        = (0.7003 * ((Real.log X + 1) ^ 2 / 2 + 1)
            + (1e-9 + 1.02) * (Real.log X + 2) + (1e-6 + 0.102)) / X := by
      ring
    rw [hid]
    apply div_le_div_of_nonneg_right _ hX0.le
    nlinarith
  rw [averagingError]
  rw [hexpand] at hmul
  linarith

/-! ## Per-shell lower bounds (eq. `explicit-collision`, high window) -/

section HighLowerShells

variable {X : ℝ}

/-- The collision multiplicity `highCollisionMult` satisfies the `hb`
hypothesis of `shell_collision_lower` (eq. `explicit-bm`). -/
theorem high_collision_hb (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m)
    (hmM : m ≤ lowM X) :
    Real.log ((((Finset.Icc 1 m).lcm id : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ))
        / Real.log ((lowN X : ℝ) / ((m : ℝ) + 1))
      ≤ (highCollisionMult X m : ℝ) := by
  have hcast : (highCollisionMult X m : ℝ)
      = ((⌊(Real.log 4 * m + Real.sqrt m * Real.log m
          + Real.log (1 + Real.log m)) / highLogDenom X⌋₊ : ℕ) : ℝ) + 1 := by
    rw [highCollisionMult]
    push_cast
    ring
  rw [hcast]
  exact collision_hb_of hm1 (high_logDenom_pos hX) (high_loga_ge_logDenom hX hmM)

/-- Cast bound for the collision multiplicity. -/
theorem high_collisionMult_cast_le (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m) :
    (highCollisionMult X m : ℝ)
      ≤ (Real.log 4 * m + Real.sqrt m * Real.log m
          + Real.log (1 + Real.log m)) / highLogDenom X + 1 := by
  have hcast : (highCollisionMult X m : ℝ)
      = ((⌊(Real.log 4 * m + Real.sqrt m * Real.log m
          + Real.log (1 + Real.log m)) / highLogDenom X⌋₊ : ℕ) : ℝ) + 1 := by
    rw [highCollisionMult]
    push_cast
    ring
  rw [hcast]
  exact collisionMult_cast_le_of (high_logDenom_pos hX) hm1

/-- Uniform absorption of the `√m·log m` layer: `√y·log y ≤ 0.01y + 32000`
for all `y ≥ 1` (below `4·10⁶` the product is at most `2000·16`; above,
`low_sqrt_mul_log_le` applies). -/
theorem high_sqrt_mul_log_le_uniform {y : ℝ} (hy : (1:ℝ) ≤ y) :
    Real.sqrt y * Real.log y ≤ 0.01 * y + 32000 := by
  rcases le_or_gt y (4 * 10 ^ 6 : ℝ) with hcase | hcase
  · have hy0 : (0:ℝ) < y := by linarith
    have hs : Real.sqrt y ≤ 2000 := by
      have h : y ≤ 2000 ^ 2 := by nlinarith
      calc Real.sqrt y ≤ Real.sqrt (2000 ^ 2) := Real.sqrt_le_sqrt h
        _ = 2000 := Real.sqrt_sq (by norm_num)
    have hlog : Real.log y ≤ 16 := by
      rw [Real.log_le_iff_le_exp hy0]
      linarith [low_exp_16_lb]
    have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    nlinarith [mul_le_mul hs hlog hlog0 (by norm_num : (0:ℝ) ≤ 2000)]
  · have h := low_sqrt_mul_log_le (le_of_lt hcase)
    linarith

/-- Regime-I multiplicity bound: `b_m ≤ 2.2` for `m ≤ A`. -/
theorem high_collisionMult_le_regime_I (hX : (8e26:ℝ) ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmA : m ≤ lowA X) :
    (highCollisionMult X m : ℝ) ≤ 2.2 := by
  have hX0 := high_X_pos hX
  have hcast := high_collisionMult_cast_le hX hm1
  have hDpos := high_logDenom_pos hX
  have hDlb := high_logDenom_lb hX
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
  have hmA' : (m:ℝ) ≤ 0.722 * X :=
    le_trans (Nat.cast_le.mpr hmA) (high_A_cast_ub hX)
  have hLs := high_logX_le_sqrt hX
  have hs := high_sqrt_lb hX
  have hss := high_sqrt_sq hX
  have hsqrtlog : Real.sqrt m * Real.log m ≤ 0.01 * (m:ℝ) + 32000 :=
    high_sqrt_mul_log_le_uniform hm1'
  have hlogm : Real.log (m:ℝ) ≤ Real.log X :=
    Real.log_le_log hm0 (by nlinarith)
  have hlogm0 : (0:ℝ) ≤ Real.log m := Real.log_nonneg hm1'
  have hlog1m : Real.log (1 + Real.log m) ≤ Real.log X := by
    have h2 : 1 + Real.log X ≤ X := by nlinarith
    exact Real.log_le_log (by linarith) (by linarith)
  have hlog4 : Real.log 4 ≤ 1.3862943616 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_lt_d9]
  have hWX : Real.log 4 * m + Real.sqrt m * Real.log m
      + Real.log (1 + Real.log m) ≤ 1.02 * X := by
    have hlog4m : Real.log 4 * (m:ℝ) ≤ 1.3862943616 * (m:ℝ) :=
      mul_le_mul_of_nonneg_right hlog4 hm0.le
    nlinarith [mul_nonneg (show (0:ℝ) ≤ Real.sqrt X - 2.8e13 by linarith)
      (Real.sqrt_nonneg X)]
  have hdiv : (Real.log 4 * m + Real.sqrt m * Real.log m
        + Real.log (1 + Real.log m)) / highLogDenom X
      ≤ 1.02 * X / (0.99 * X) :=
    div_le_div₀ (by positivity) hWX (by positivity) hDlb
  have hfin : 1.02 * X / (0.99 * X) ≤ 1.031 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **Per-shell collision lower bound** (eq. `collision-sum` on the high
window, with the deficit transfer of eq. `explicit-collision`). -/
theorem high_shell_collision (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m)
    (hmM : m ≤ lowM X) :
    min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
      - (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
            + 2 * X * highFksEps X)
          * Real.log (1 + 4 * (highCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
              * Real.exp (min ((m:ℝ) * Real.log 2) X - X))
      - 2 * X ^ 2 * highFksEps X
      ≤ X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m) := by
  have h1' := high_le_low_window hX
  have hX0 : (0:ℝ) < X := high_X_pos hX
  have hDpos := high_logDenom_pos hX
  have hDlb := high_logDenom_lb hX
  have hNpos := low_N_pos h1'
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hcm0 : (0:ℝ) < (m:ℝ) * ((m:ℝ) + 1) := by positivity
  set c : ℝ := ((shellPrimes (lowN X) m).card : ℝ) with hcdef
  set bR : ℝ := (highCollisionMult X m : ℝ) with hbRdef
  set Y : ℝ := Real.log ((lowN X:ℝ) / (m:ℝ)) with hYdef
  set Lg : ℝ := Real.log ((lowN X:ℝ) / ((m:ℝ) + 1)) with hLgdef
  have hYpos : (0:ℝ) < Y := high_logb_pos hX hm1 hmM
  have hYX : Y ≤ X := low_logb_le_X h1' hm1
  have hLgD : highLogDenom X ≤ Lg := high_loga_ge_logDenom hX hmM
  have hLgpos : (0:ℝ) < Lg := by linarith
  have hbR0 : (0:ℝ) ≤ bR := Nat.cast_nonneg _
  have hclow := high_shell_card_half_lb hX hm1 hmM
  have hPlow_pos : (0:ℝ) < (lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / (2 * X) := by
    positivity
  have hc_pos : (0:ℝ) < c := lt_of_lt_of_le hPlow_pos hclow
  have hcol := shell_collision_lower (N := lowN X) (m := m)
    (shellPrimes (lowN X) m) (high_shell_nonempty hX hm1 hmM)
    (fun p hp => (mem_shellPrimes.mp hp).2.2)
    (fun p hp => high_shell_prime_gt_m hX hmM hp)
    (fun p hp => low_shell_prime_cast_lb hp)
    (lt_of_lt_of_le (by norm_num) (high_shell_a_ge_two hX hmM))
    (highCollisionMult X m) (high_collision_hb hX hm1 hmM)
  have hS1 : (1:ℝ) ≤ ((S m : ℕ) : ℝ) := by exact_mod_cast one_le_S m
  have hgc : Real.log ((S m : ℕ) : ℝ) ≤ (m:ℝ) * Real.log 2 := g_le_mul_log_two m
  have htrans := low_deficit_transfer (P := c) (bR := bR)
    (S := ((S m : ℕ) : ℝ)) (Y := Y) (c₁ := (m:ℝ) * Real.log 2) (c₂ := X)
    hc_pos hS1 hbR0 hgc hYX
  have hg_eq : g m = Real.log ((S m : ℕ) : ℝ) := rfl
  rw [← hg_eq] at htrans
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
  have hmin0 : (0:ℝ) ≤ min (g m) Y := le_min (g_nonneg m) hYpos.le
  have hminX : min (g m) Y ≤ X := le_trans (min_le_right _ _) hYX
  -- positive part
  have hpos_part : min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)) - 2 * X ^ 2 * highFksEps X
      ≤ X / (lowN X:ℝ) * c * min (g m) Y := by
    have hclb := high_shell_card_lb_sharp hX hm1 hmM
    have hE : X / (lowN X:ℝ)
          * ((lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / Y
              - 2 * (lowN X:ℝ) * highFksEps X)
        ≤ X / (lowN X:ℝ) * c := mul_le_mul_of_nonneg_left hclb hXN0
    have hidE : X / (lowN X:ℝ)
          * ((lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / Y
              - 2 * (lowN X:ℝ) * highFksEps X)
        = X / Y * (1 / ((m:ℝ) * ((m:ℝ) + 1))) - 2 * X * highFksEps X := by
      field_simp
    rw [hidE] at hE
    have hmul2 : (X / Y * (1 / ((m:ℝ) * ((m:ℝ) + 1))) - 2 * X * highFksEps X)
          * min (g m) Y
        ≤ X / (lowN X:ℝ) * c * min (g m) Y :=
      mul_le_mul_of_nonneg_right hE hmin0
    have htransport := low_cap_transport_free hYpos hYX (g_nonneg m)
    have hexp2 : (X / Y * (1 / ((m:ℝ) * ((m:ℝ) + 1))) - 2 * X * highFksEps X)
          * min (g m) Y
        = X / Y * min (g m) Y * (1 / ((m:ℝ) * ((m:ℝ) + 1)))
          - 2 * X * highFksEps X * min (g m) Y := by
      ring
    have hjunk2 : 2 * X * highFksEps X * min (g m) Y
        ≤ 2 * X ^ 2 * highFksEps X := by
      have h2X0 : (0:ℝ) ≤ 2 * X * highFksEps X := by
        have := high_eps_nonneg X
        positivity
      calc 2 * X * highFksEps X * min (g m) Y ≤ 2 * X * highFksEps X * X :=
            mul_le_mul_of_nonneg_left hminX h2X0
        _ = 2 * X ^ 2 * highFksEps X := by ring
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
      ≤ (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X + 2 * X * highFksEps X)
          * Real.log (1 + 4 * bR * X * ((m:ℝ) * ((m:ℝ) + 1))
              * Real.exp (min ((m:ℝ) * Real.log 2) X - X)) := by
    have hcub := high_shell_card_ub hX hm1 hmM
    have hcoeff : X / (lowN X:ℝ) * c
        ≤ X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
          + 2 * X * highFksEps X := by
      have hE := mul_le_mul_of_nonneg_left hcub hXN0
      have hidE : X / (lowN X:ℝ)
            * ((lowN X:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) / Lg
                + 2 * (lowN X:ℝ) * highFksEps X)
          = X / Lg * (1 / ((m:ℝ) * ((m:ℝ) + 1))) + 2 * X * highFksEps X := by
        field_simp
      rw [hidE] at hE
      have hLgX : X / Lg ≤ X / highLogDenom X :=
        div_le_div_of_nonneg_left hX0.le hDpos hLgD
      have hmono : X / Lg * (1 / ((m:ℝ) * ((m:ℝ) + 1)))
          ≤ X / highLogDenom X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right hLgX (by positivity)
      have hidX : X / highLogDenom X * (1 / ((m:ℝ) * ((m:ℝ) + 1)))
          = X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X := by
        ring
      linarith [hidX ▸ hmono]
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
      linarith [hid3 ▸ hstep1, hid4 ▸ hstep2]
    have hcoeff0 : (0:ℝ) ≤ X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
        + 2 * X * highFksEps X := by
      have := high_eps_nonneg X
      positivity
    calc X / (lowN X:ℝ) * c
          * Real.log (1 + bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c)
        ≤ (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
              + 2 * X * highFksEps X)
            * Real.log (1 + bR * Real.exp (min ((m:ℝ) * Real.log 2) X) / c) :=
          mul_le_mul_of_nonneg_right hcoeff hdef_nonneg
      _ ≤ (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
              + 2 * X * highFksEps X)
            * Real.log (1 + 4 * bR * X * ((m:ℝ) * ((m:ℝ) + 1))
                * Real.exp (min ((m:ℝ) * Real.log 2) X - X)) :=
          mul_le_mul_of_nonneg_left hlog_arg hcoeff0
  linarith

set_option maxHeartbeats 1000000 in
/-- Per-shell lower bound, regime `m ≤ A`: the collision deficit carries
`e^{a*_m − X} ≤ e^{−X/2}` and is bounded by `9X³e^{−X/2}`. -/
theorem high_shell_lower_regime_I (hX : (8e26:ℝ) ≤ X) {m : ℕ} (hm1 : 1 ≤ m)
    (hmA : m ≤ lowA X) :
    min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
      - 9 * X ^ 3 * Real.exp (-(X / 2)) - 300 * X ^ 2 * highFksEps X
      ≤ X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m) := by
  have h1' := high_le_low_window hX
  have hmM : m ≤ lowM X := le_trans hmA (high_A_le_M hX)
  have hcore := high_shell_collision hX hm1 hmM
  have hX0 := high_X_pos hX
  have hDpos := high_logDenom_pos hX
  have hDlb := high_logDenom_lb hX
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
  have hcm0 : (0:ℝ) < (m:ℝ) * ((m:ℝ) + 1) := by positivity
  have hbR0 : (0:ℝ) ≤ (highCollisionMult X m : ℝ) := Nat.cast_nonneg _
  set U : ℝ := 4 * (highCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
      * Real.exp (min ((m:ℝ) * Real.log 2) X - X) with hUdef
  have hU0 : (0:ℝ) ≤ U := by positivity
  have hcoeff : X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
      + 2 * X * highFksEps X ≤ 1 := by
    have hinv2 : 1 / ((m:ℝ) * ((m:ℝ) + 1)) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have hnum : X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) ≤ X / 2 := by
      have := mul_le_mul_of_nonneg_left hinv2 hX0.le
      linarith
    have hdiv : X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
        ≤ X / 2 / highLogDenom X :=
      div_le_div_of_nonneg_right hnum hDpos.le
    have h06 : X / 2 / highLogDenom X ≤ 0.6 := by
      rw [div_le_iff₀ hDpos]
      nlinarith
    have hepsX : 2 * X * highFksEps X ≤ 0.4 := by
      have h1 : highFksEps X ≤ 0.001 / X :=
        le_trans (high_eps_le_tiny X) (high_tiny_le hX)
      have h2 : 2 * X * highFksEps X ≤ 2 * X * (0.001 / X) := by
        apply mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : 2 * X * (0.001 / X) = 0.002 := by
        field_simp
        norm_num
      linarith
    linarith
  have hb := high_collisionMult_le_regime_I hX hm1 hmA
  have hastar : min ((m:ℝ) * Real.log 2) X - X ≤ -(X / 2) := by
    have hmlog2 := low_A_mul_log2_le h1' hmA
    have : min ((m:ℝ) * Real.log 2) X ≤ X / 2 :=
      le_trans (min_le_left _ _) hmlog2
    linarith
  have hexp_a : Real.exp (min ((m:ℝ) * Real.log 2) X - X) ≤ Real.exp (-(X / 2)) :=
    Real.exp_le_exp.mpr hastar
  have hmm : (m:ℝ) * ((m:ℝ) + 1) ≤ X ^ 2 := by
    have hmA' : (m:ℝ) ≤ 0.722 * X :=
      le_trans (Nat.cast_le.mpr hmA) (high_A_cast_ub hX)
    nlinarith
  have hs2 : 4 * (highCollisionMult X m : ℝ) * X ≤ 8.8 * X := by nlinarith
  have hs3 : 4 * (highCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
      ≤ 8.8 * X * X ^ 2 :=
    mul_le_mul hs2 hmm hcm0.le (by positivity)
  have hUle : U ≤ 8.8 * X ^ 3 * Real.exp (-(X / 2)) := by
    rw [hUdef]
    calc 4 * (highCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
          * Real.exp (min ((m:ℝ) * Real.log 2) X - X)
        ≤ 8.8 * X * X ^ 2 * Real.exp (-(X / 2)) :=
          mul_le_mul hs3 hexp_a (Real.exp_pos _).le (by positivity)
      _ = 8.8 * X ^ 3 * Real.exp (-(X / 2)) := by ring
  have hlogU : Real.log (1 + U) ≤ U := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + U by linarith)
    linarith
  have hlogU0 : (0:ℝ) ≤ Real.log (1 + U) := Real.log_nonneg (by linarith)
  have hdef : (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
        + 2 * X * highFksEps X) * Real.log (1 + U)
      ≤ 9 * X ^ 3 * Real.exp (-(X / 2)) := by
    have hcoeff0 : (0:ℝ) ≤ X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
        + 2 * X * highFksEps X := by
      have := high_eps_nonneg X
      positivity
    calc (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
          + 2 * X * highFksEps X) * Real.log (1 + U)
        ≤ 1 * (8.8 * X ^ 3 * Real.exp (-(X / 2))) :=
          mul_le_mul hcoeff (le_trans hlogU hUle) hlogU0 (by norm_num)
      _ ≤ 9 * X ^ 3 * Real.exp (-(X / 2)) := by
          nlinarith [Real.exp_pos (-(X / 2)), pow_pos hX0 3]
  have hjunk : 2 * X ^ 2 * highFksEps X ≤ 300 * X ^ 2 * highFksEps X := by
    apply mul_le_mul_of_nonneg_right _ (high_eps_nonneg X)
    nlinarith
  linarith

/-- Regime-II multiplicity bound: `b_m ≤ 2.83·m/highLogDenom X` for
`m > A` (eq. `explicit-bm`). -/
theorem high_collisionMult_le_regime_II (hX : (8e26:ℝ) ≤ X) {m : ℕ}
    (hmA : lowA X < m) (hmM : m ≤ lowM X) :
    (highCollisionMult X m : ℝ) ≤ 2.83 * (m:ℝ) / highLogDenom X := by
  have h1' := high_le_low_window hX
  have hX0 := high_X_pos hX
  have hDpos := high_logDenom_pos hX
  have hDle := high_logDenom_le hX
  have hm1 : 1 ≤ m := by
    have := low_A_lb h1'
    omega
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
  have hcast := high_collisionMult_cast_le hX hm1
  have hmlb : 0.7 * X ≤ (m:ℝ) := by
    have h := high_A_cast_lb hX
    have hc : (lowA X:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hmA
    linarith
  have hs := high_sqrt_lb hX
  have hss := high_sqrt_sq hX
  have hLs := high_logX_le_sqrt hX
  have hsqrtlog : Real.sqrt m * Real.log m ≤ 0.011 * (m:ℝ) := by
    have h := high_sqrt_mul_log_le_uniform hm1'
    nlinarith [mul_nonneg (show (0:ℝ) ≤ Real.sqrt X - 2.8e13 by linarith)
      (Real.sqrt_nonneg X)]
  have hlogm : Real.log (m:ℝ) ≤ 3 * Real.log X + 0.7 := by
    have h := high_log_m_succ_le hX hmM
    have hmono : Real.log (m:ℝ) ≤ Real.log ((m:ℝ) + 1) :=
      Real.log_le_log hm0 (by linarith)
    linarith
  have hlog1m : Real.log (1 + Real.log m) ≤ 0.001 * (m:ℝ) := by
    have hlogm0 : (0:ℝ) ≤ Real.log m := Real.log_nonneg hm1'
    have h1 : Real.log (1 + Real.log m) ≤ 1 + Real.log m := by
      linarith [Real.log_le_sub_one_of_pos
        (show (0:ℝ) < 1 + Real.log m by linarith)]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ Real.sqrt X - 2.8e13 by linarith)
      (Real.sqrt_nonneg X)]
  have hlog4 : Real.log 4 ≤ 1.3862943616 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_lt_d9]
  have hone : 1 ≤ 1.3863 * (m:ℝ) / highLogDenom X := by
    have hgtA := low_gt_A_cast hmA
    rw [le_div_iff₀ hDpos]
    have hmul : Real.log 2 * (m:ℝ) ≤ 0.6931471808 * (m:ℝ) :=
      mul_le_mul_of_nonneg_right Real.log_two_lt_d9.le hm0.le
    nlinarith
  have hW : (Real.log 4 * m + Real.sqrt m * Real.log m
        + Real.log (1 + Real.log m)) / highLogDenom X
      ≤ 1.399 * (m:ℝ) / highLogDenom X := by
    apply div_le_div_of_nonneg_right _ hDpos.le
    have hlog4m : Real.log 4 * (m:ℝ) ≤ 1.3862943616 * (m:ℝ) :=
      mul_le_mul_of_nonneg_right hlog4 hm0.le
    nlinarith
  have hsum : 1.399 * (m:ℝ) / highLogDenom X + 1.3863 * (m:ℝ) / highLogDenom X
      = 2.7853 * (m:ℝ) / highLogDenom X := by
    ring
  have hfin : 2.7853 * (m:ℝ) / highLogDenom X ≤ 2.83 * (m:ℝ) / highLogDenom X := by
    apply div_le_div_of_nonneg_right _ hDpos.le
    nlinarith
  linarith

set_option maxHeartbeats 1000000 in
/-- Per-shell lower bound, regime `A < m ≤ M` (integral regime). -/
theorem high_shell_lower_regime_II (hX : (8e26:ℝ) ≤ X) {m : ℕ}
    (hmA : lowA X < m) (hmM : m ≤ lowM X) :
    min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
      - X / highLogDenom X * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
          / ((m:ℝ) * ((m:ℝ) + 1)))
      - 300 * X ^ 2 * highFksEps X
      ≤ X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m) := by
  have h1' := high_le_low_window hX
  have hm1 : 1 ≤ m := by
    have := low_A_lb h1'
    omega
  have hcore := high_shell_collision hX hm1 hmM
  have hX0 := high_X_pos hX
  have hDpos := high_logDenom_pos hX
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
  have hcm0 : (0:ℝ) < (m:ℝ) * ((m:ℝ) + 1) := by positivity
  have hbR0 : (0:ℝ) ≤ (highCollisionMult X m : ℝ) := Nat.cast_nonneg _
  have hlog1 : (0:ℝ) ≤ Real.log ((m:ℝ) + 1) := Real.log_nonneg (by linarith)
  set U : ℝ := 4 * (highCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
      * Real.exp (min ((m:ℝ) * Real.log 2) X - X) with hUdef
  have hU0 : (0:ℝ) ≤ U := by positivity
  have hbm := high_collisionMult_le_regime_II hX hmA hmM
  have hexp1 : Real.exp (min ((m:ℝ) * Real.log 2) X - X) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    apply Real.exp_le_exp.mpr
    have := min_le_right ((m:ℝ) * Real.log 2) X
    linarith
  have hUle : U ≤ 11.45 * ((m:ℝ) + 1) ^ 3 := by
    have hb4 : 4 * (highCollisionMult X m : ℝ)
        ≤ 11.32 * (m:ℝ) / highLogDenom X := by
      rw [show (11.32:ℝ) * (m:ℝ) / highLogDenom X
        = 4 * (2.83 * (m:ℝ) / highLogDenom X) by ring]
      linarith
    have hstep : 4 * (highCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
        ≤ 11.32 * (m:ℝ) / highLogDenom X * X * ((m:ℝ) * ((m:ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_right _ hcm0.le
      exact mul_le_mul_of_nonneg_right hb4 hX0.le
    have hid : 11.32 * (m:ℝ) / highLogDenom X * X * ((m:ℝ) * ((m:ℝ) + 1))
        = 11.32 * (X / highLogDenom X) * ((m:ℝ) * (m:ℝ) * ((m:ℝ) + 1)) := by
      ring
    have hXdiv := high_X_div_logDenom_ub hX
    have hcoef : 11.32 * (X / highLogDenom X) ≤ 11.45 := by nlinarith
    have hm3 : (m:ℝ) * (m:ℝ) * ((m:ℝ) + 1) ≤ ((m:ℝ) + 1) ^ 3 := by nlinarith
    have hfin : 11.32 * (X / highLogDenom X) * ((m:ℝ) * (m:ℝ) * ((m:ℝ) + 1))
        ≤ 11.45 * ((m:ℝ) + 1) ^ 3 := by
      apply mul_le_mul hcoef hm3 (by positivity) (by norm_num)
    have hUmid : U ≤ 4 * (highCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1)) := by
      rw [hUdef]
      calc 4 * (highCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1))
            * Real.exp (min ((m:ℝ) * Real.log 2) X - X)
          ≤ 4 * (highCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1)) * 1 := by
            apply mul_le_mul_of_nonneg_left hexp1 (by positivity)
        _ = 4 * (highCollisionMult X m : ℝ) * X * ((m:ℝ) * ((m:ℝ) + 1)) := by
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
  have hlogm1_ub : Real.log ((m:ℝ) + 1) ≤ 3 * Real.log X + 0.7 :=
    high_log_m_succ_le hX hmM
  have hRle : Real.log 12 + 3 * Real.log ((m:ℝ) + 1) ≤ X := by
    have hlog12u := low_log_12_ub
    have hs := high_sqrt_lb hX
    have hss := high_sqrt_sq hX
    have hLs := high_logX_le_sqrt hX
    nlinarith [mul_nonneg (show (0:ℝ) ≤ Real.sqrt X - 2.8e13 by linarith)
      (Real.sqrt_nonneg X)]
  have hlogU0 : (0:ℝ) ≤ Real.log (1 + U) := Real.log_nonneg (by linarith)
  have hR0 : (0:ℝ) ≤ Real.log 12 + 3 * Real.log ((m:ℝ) + 1) := by
    have : (0:ℝ) ≤ Real.log 12 := Real.log_nonneg (by norm_num)
    linarith
  have hdef : (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
        + 2 * X * highFksEps X) * Real.log (1 + U)
      ≤ X / highLogDenom X * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
          / ((m:ℝ) * ((m:ℝ) + 1)))
        + 298 * X ^ 2 * highFksEps X := by
    have hmain : (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
          + 2 * X * highFksEps X) * Real.log (1 + U)
        ≤ (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
            + 2 * X * highFksEps X)
            * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left hlog12
      have := high_eps_nonneg X
      positivity
    have hexpand : (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
          + 2 * X * highFksEps X)
          * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
        = X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
            * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
          + 2 * X * highFksEps X * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) := by
      ring
    have hid1 : X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
          * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
        = X / highLogDenom X * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
            / ((m:ℝ) * ((m:ℝ) + 1))) := by
      ring
    have hpiece2 : 2 * X * highFksEps X
          * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
        ≤ 298 * X ^ 2 * highFksEps X := by
      have h2X0 : (0:ℝ) ≤ 2 * X * highFksEps X := by
        have := high_eps_nonneg X
        positivity
      have hstep : 2 * X * highFksEps X
            * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
          ≤ 2 * X * highFksEps X * X := mul_le_mul_of_nonneg_left hRle h2X0
      have hfin : 2 * X * highFksEps X * X ≤ 298 * X ^ 2 * highFksEps X := by
        have := high_eps_nonneg X
        nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ X ^ 2)
          (high_eps_nonneg X)) (by norm_num : (0:ℝ) ≤ (296:ℝ))]
      linarith
    calc (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
          + 2 * X * highFksEps X) * Real.log (1 + U)
        ≤ (X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
            + 2 * X * highFksEps X)
            * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) := hmain
      _ = X * (1 / ((m:ℝ) * ((m:ℝ) + 1))) / highLogDenom X
            * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
          + 2 * X * highFksEps X * (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) :=
          hexpand
      _ ≤ X / highLogDenom X * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
            / ((m:ℝ) * ((m:ℝ) + 1)))
          + 298 * X ^ 2 * highFksEps X := by
          rw [← hid1]
          linarith
  linarith

end HighLowerShells

/-! ## Summing the lower per-shell bounds -/

section HighLowerSums

variable {X : ℝ}

/-- Total regime-I deficit: at most `A ≤ X` shells, each at most
`9X³e^{−X/2}`; total absorbed into `exp(−0.7√X)`. -/
theorem high_deficit_I_sum_le (hX : (8e26:ℝ) ≤ X) :
    ∑ _m ∈ Finset.Icc 1 (lowA X), 9 * X ^ 3 * Real.exp (-(X / 2))
      ≤ Real.exp (-(0.7 * Real.sqrt X)) := by
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hcast : ((lowA X + 1 - 1 : ℕ) : ℝ) = (lowA X : ℝ) := by simp
  rw [hcast]
  have hX0 := high_X_pos hX
  have hA : (lowA X : ℝ) ≤ X := le_trans (high_A_cast_ub hX) (by linarith)
  have hL := high_logX_le_sqrt hX
  have hs := high_sqrt_lb hX
  have hss := high_sqrt_sq hX
  have hp : X ^ 5 * Real.exp (-(X / 2)) ≤ Real.exp (-(0.7 * Real.sqrt X)) := by
    rw [high_pow_eq_exp hX0 5, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have h9 : (9:ℝ) ≤ X := by linarith
  calc (lowA X : ℝ) * (9 * X ^ 3 * Real.exp (-(X / 2)))
      ≤ X * (9 * X ^ 3 * Real.exp (-(X / 2))) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ = 9 * X ^ 4 * Real.exp (-(X / 2)) := by ring
    _ ≤ X ^ 5 * Real.exp (-(X / 2)) := by
        have hX4 : 9 * X ^ 4 ≤ X ^ 5 := by
          calc 9 * X ^ 4 ≤ X * X ^ 4 :=
                mul_le_mul_of_nonneg_right h9 (by positivity)
            _ = X ^ 5 := by ring
        exact mul_le_mul_of_nonneg_right hX4 (Real.exp_pos _).le
    _ ≤ Real.exp (-(0.7 * Real.sqrt X)) := hp

/-- Total regime-II deficit (paper: `< 6.5·10⁻²⁵`; realized as
`8.7(log X + 2)/X`). -/
theorem high_deficit_II_sum_le (hX : (8e26:ℝ) ≤ X) :
    ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
        X / highLogDenom X * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
          / ((m:ℝ) * ((m:ℝ) + 1)))
      ≤ 8.7 * (Real.log X + 2) / X := by
  have h1' := high_le_low_window hX
  have hX0 := high_X_pos hX
  have hXD := high_X_div_logDenom_ub hX
  have hL := high_logX_lb hX
  have hAlb := high_A_cast_lb hX
  rw [← Finset.mul_sum]
  have hlog12u := low_log_12_ub
  have hlog12l : (0:ℝ) ≤ Real.log 12 := Real.log_nonneg (by norm_num)
  have hterm : ∀ m ∈ Finset.Ioc (lowA X) (lowM X),
      (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ Real.log 12 * (1 / ((m:ℝ) * (m:ℝ)))
          + 6 * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1))) := by
    intro m hm
    have hm1 : 1 ≤ m := by
      have hmA := (Finset.mem_Ioc.mp hm).1
      have := low_A_lb h1'
      omega
    have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
    have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
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
        ≤ 6 * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1))) := by
      have hw : (1:ℝ) / ((m:ℝ) * ((m:ℝ) + 1)) ≤ 2 / (((m:ℝ) + 1) * ((m:ℝ) + 1)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc 3 * Real.log ((m:ℝ) + 1) / ((m:ℝ) * ((m:ℝ) + 1))
          = 3 * Real.log ((m:ℝ) + 1) * (1 / ((m:ℝ) * ((m:ℝ) + 1))) := by
            rw [mul_one_div]
        _ ≤ 3 * Real.log ((m:ℝ) + 1) * (2 / (((m:ℝ) + 1) * ((m:ℝ) + 1))) := by
            apply mul_le_mul_of_nonneg_left hw (by positivity)
        _ = 6 * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1))) := by
            field_simp
            ring
    rw [hsplit]
    linarith
  have hA1 : 1 ≤ lowA X := by
    have := low_A_lb h1'
    omega
  have hA3 : 3 ≤ lowA X := by
    have := low_A_lb h1'
    omega
  have hsum1 := sum_one_div_Ioc_le (lowA X) (lowM X) hA1
  have hsum2 := sum_log_div_sq_tail_le (lowA X) (lowM X) hA3
  have hlogA := high_log_A_add_one_ub hX
  have hinner : ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
      (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) / ((m:ℝ) * ((m:ℝ) + 1))
      ≤ Real.log 12 * (1 / (0.7 * X)) + 6 * ((Real.log X + 1) / (0.7 * X)) := by
    have hs1' : (1:ℝ) / (lowA X : ℝ) ≤ 1 / (0.7 * X) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hAlb
    have hs2' : (Real.log ((lowA X:ℝ) + 1) + 1) / ((lowA X:ℝ) + 1)
        ≤ (Real.log X + 1) / (0.7 * X) := by
      apply div_le_div₀ (by linarith) (by linarith) (by positivity) (by linarith)
    calc ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
          (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
            (Real.log 12 * (1 / ((m:ℝ) * (m:ℝ)))
              + 6 * (Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1)))) :=
          Finset.sum_le_sum hterm
      _ = Real.log 12 * ∑ m ∈ Finset.Ioc (lowA X) (lowM X), 1 / ((m:ℝ) * (m:ℝ))
          + 6 * ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
              Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * ((m:ℝ) + 1)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ Real.log 12 * (1 / (0.7 * X)) + 6 * ((Real.log X + 1) / (0.7 * X)) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ hlog12l
            linarith [hsum1, hs1']
          · apply mul_le_mul_of_nonneg_left _ (by norm_num)
            linarith [hsum2, hs2']
  have hinner0 : (0:ℝ) ≤ ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
      (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) / ((m:ℝ) * ((m:ℝ) + 1)) := by
    apply Finset.sum_nonneg
    intro m hm
    have hm1 : 1 ≤ m := by
      have hmA := (Finset.mem_Ioc.mp hm).1
      have := low_A_lb h1'
      omega
    have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
    have hL0 : (0:ℝ) ≤ Real.log ((m:ℝ) + 1) := Real.log_nonneg (by linarith)
    have : (0:ℝ) ≤ Real.log 12 + 3 * Real.log ((m:ℝ) + 1) := by linarith
    positivity
  calc X / highLogDenom X * ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
        (Real.log 12 + 3 * Real.log ((m:ℝ) + 1)) / ((m:ℝ) * ((m:ℝ) + 1))
      ≤ 1.011 * (Real.log 12 * (1 / (0.7 * X)) + 6 * ((Real.log X + 1) / (0.7 * X))) :=
        mul_le_mul hXD hinner hinner0 (by norm_num)
    _ = 1.011 * (Real.log 12 + 6 * (Real.log X + 1)) / 0.7 / X := by
        field_simp
    _ ≤ 8.7 * (Real.log X + 2) / X := by
        apply div_le_div_of_nonneg_right _ hX0.le
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 0.7)]
        nlinarith

/-- The full lower shell-sum estimate. -/
theorem high_sum_lower (hX : (8e26:ℝ) ≤ X) :
    (∑ m ∈ Finset.Icc 1 (lowM X), min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)))
        - (8.7 * (Real.log X + 2) / X + 2 * Real.exp (-(0.7 * Real.sqrt X)))
      ≤ X / (lowN X:ℝ)
        * ∑ m ∈ Finset.Icc 1 (lowM X),
            ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m) := by
  have hAM := high_A_le_M hX
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
        - 9 * X ^ 3 * Real.exp (-(X / 2)) - 300 * X ^ 2 * highFksEps X)
      ≤ ∑ m ∈ Finset.Icc 1 (lowA X),
          X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m) := by
    apply Finset.sum_le_sum
    intro m hm
    have hmem := Finset.mem_Icc.mp hm
    exact high_shell_lower_regime_I hX hmem.1 hmem.2
  have hheadIeq : ∑ m ∈ Finset.Icc 1 (lowA X),
      (min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
        - 9 * X ^ 3 * Real.exp (-(X / 2)) - 300 * X ^ 2 * highFksEps X)
      = (∑ m ∈ Finset.Icc 1 (lowA X), min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)))
        - (∑ _m ∈ Finset.Icc 1 (lowA X), 9 * X ^ 3 * Real.exp (-(X / 2)))
        - ∑ _m ∈ Finset.Icc 1 (lowA X), 300 * X ^ 2 * highFksEps X := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hheadI := hheadIeq ▸ hheadI0
  have htailII0 : ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
      (min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
        - X / highLogDenom X * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
            / ((m:ℝ) * ((m:ℝ) + 1)))
        - 300 * X ^ 2 * highFksEps X)
      ≤ ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
          X / (lowN X:ℝ) * ∑ p ∈ shellPrimes (lowN X) m, Real.log (sigma p m) := by
    apply Finset.sum_le_sum
    intro m hm
    have hmem := Finset.mem_Ioc.mp hm
    exact high_shell_lower_regime_II hX hmem.1 hmem.2
  have htailIIeq : ∑ m ∈ Finset.Ioc (lowA X) (lowM X),
      (min (g m) X / ((m:ℝ) * ((m:ℝ) + 1))
        - X / highLogDenom X * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
            / ((m:ℝ) * ((m:ℝ) + 1)))
        - 300 * X ^ 2 * highFksEps X)
      = (∑ m ∈ Finset.Ioc (lowA X) (lowM X), min (g m) X / ((m:ℝ) * ((m:ℝ) + 1)))
        - (∑ m ∈ Finset.Ioc (lowA X) (lowM X),
            X / highLogDenom X * ((Real.log 12 + 3 * Real.log ((m:ℝ) + 1))
              / ((m:ℝ) * ((m:ℝ) + 1))))
        - ∑ _m ∈ Finset.Ioc (lowA X) (lowM X), 300 * X ^ 2 * highFksEps X := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have htailII := htailIIeq ▸ htailII0
  have hdefI := high_deficit_I_sum_le hX
  have hdefII := high_deficit_II_sum_le hX
  have hjunk : (∑ _m ∈ Finset.Icc 1 (lowA X), 300 * X ^ 2 * highFksEps X)
      + (∑ _m ∈ Finset.Ioc (lowA X) (lowM X), 300 * X ^ 2 * highFksEps X)
      ≤ Real.exp (-(0.7 * Real.sqrt X)) := by
    rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, Nat.card_Ioc,
      nsmul_eq_mul, nsmul_eq_mul]
    have hcast : ((lowA X + 1 - 1 : ℕ) : ℝ) + ((lowM X - lowA X : ℕ) : ℝ)
        = (lowM X : ℝ) := by
      rw [Nat.cast_sub hAM]
      simp
    calc ((lowA X + 1 - 1 : ℕ) : ℝ) * (300 * X ^ 2 * highFksEps X)
          + ((lowM X - lowA X : ℕ) : ℝ) * (300 * X ^ 2 * highFksEps X)
        = (lowM X : ℝ) * (300 * X ^ 2 * highFksEps X) := by
          rw [← add_mul, hcast]
      _ ≤ Real.exp (-(0.7 * Real.sqrt X)) := high_junk_total_le hX
  linarith

end HighLowerSums

/-! ## The lower half of the master enclosure, and the two final bounds -/

/-- The omitted `𝓑`-tail: `X/(M+1) ≤ X^{−1.05} ≤ 0.1/X`. -/
theorem high_B_tail_le {X : ℝ} (hX : (8e26:ℝ) ≤ X) :
    X / ((lowM X:ℝ) + 1) ≤ 0.1 / X := by
  have hX0 := high_X_pos hX
  have hL := high_logX_lb hX
  have hrpow_pos : (0:ℝ) < X ^ (2.05:ℝ) := Real.rpow_pos_of_pos hX0 _
  have h1 : X / ((lowM X:ℝ) + 1) ≤ X / X ^ (2.05:ℝ) :=
    div_le_div_of_nonneg_left hX0.le hrpow_pos (high_rpow_lt_M_add_one X).le
  have hid : X / X ^ (2.05:ℝ) = Real.exp (Real.log X - 2.05 * Real.log X) := by
    rw [Real.rpow_def_of_pos hX0, Real.exp_sub, high_exp_log hX,
      mul_comm (Real.log X) (2.05:ℝ)]
  have hexp105 : Real.exp (Real.log X - 2.05 * Real.log X) ≤ 1 / 22 * (1 / X) := by
    have hid2 : Real.log X - 2.05 * Real.log X
        = -(0.05 * Real.log X) + -(Real.log X) := by ring
    rw [hid2, Real.exp_add]
    have h22 : (22:ℝ) ≤ Real.exp (0.05 * Real.log X) := by
      have hmono : Real.exp 3.095 ≤ Real.exp (0.05 * Real.log X) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h3 : (20.08:ℝ) ≤ Real.exp 3 := by
        calc (20.08:ℝ) ≤ (2.7182818283:ℝ) ^ (3:ℕ) := by norm_num
          _ ≤ Real.exp ((3:ℕ):ℝ) := low_exp_nat_lb 3
          _ = Real.exp 3 := by norm_num
      have h0095 : (1.0995:ℝ) ≤ Real.exp 0.095 := by
        nlinarith [Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.095 by norm_num)]
      have hsplit3 : Real.exp 3 * Real.exp 0.095 = Real.exp 3.095 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith [Real.exp_pos 3, Real.exp_pos 0.095]
    have hexp05 : Real.exp (-(0.05 * Real.log X)) ≤ 1 / 22 := by
      have hmul : Real.exp (-(0.05 * Real.log X))
          * Real.exp (0.05 * Real.log X) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      nlinarith [Real.exp_pos (-(0.05 * Real.log X))]
    have hexpL : Real.exp (-(Real.log X)) = 1 / X := by
      rw [Real.exp_neg, high_exp_log hX, one_div]
    rw [hexpL]
    exact mul_le_mul_of_nonneg_right hexp05 (by positivity)
  have hfin : 1 / 22 * (1 / X) ≤ 0.1 / X := by
    rw [div_eq_mul_one_div (0.1:ℝ) X]
    nlinarith [show (0:ℝ) ≤ 1 / X by positivity]
  linarith [hid ▸ h1]

/-- **Lower master bound**: `𝓡(X) ≥ −(8.7(log X+2) + 0.2)/X` for
`X ≥ 8·10²⁶`. -/
theorem high_averaging_lower {X : ℝ} (hX : (8e26:ℝ) ≤ X) :
    -((8.7 * (Real.log X + 2) + 0.2) / X) ≤ averagingError X := by
  have h1' := high_le_low_window hX
  have hX0 := high_X_pos hX
  have hL := high_logX_lb hX
  have hbridge := high_bridge hX
  have hdec := (g_shell_decomposition (N := lowN X) (M := lowM X)
    (high_hQN hX) (high_hQ2 hX)).1
  have hsum := high_sum_lower hX
  have hBle := low_B_le_partial_add_tail (X := X) (lowM X)
  have hBtail := high_B_tail_le hX
  have htiny := high_tiny_le hX
  have hXN0 : (0:ℝ) ≤ X / (lowN X:ℝ) :=
    div_nonneg (by linarith) (low_N_pos h1').le
  have hmul := mul_le_mul_of_nonneg_left hdec hXN0
  have hF : X / (lowN X:ℝ) * g (lowN X) - 0.001 / X ≤ FReal (Real.exp X) := by
    linarith [(abs_le.mp hbridge).1]
  have hcomb : 8.7 * (Real.log X + 2) / X + 2 * (0.001 / X) + 0.001 / X + 0.1 / X
      ≤ (8.7 * (Real.log X + 2) + 0.2) / X := by
    have hid : 8.7 * (Real.log X + 2) / X + 2 * (0.001 / X) + 0.001 / X + 0.1 / X
        = (8.7 * (Real.log X + 2) + 0.103) / X := by
      ring
    rw [hid]
    apply div_le_div_of_nonneg_right _ hX0.le
    linarith
  rw [averagingError]
  linarith

/-- **High-interval averaging error, symbolic form**
(`cor:explicit-high-averaging`, eq. `explicit-high-averaging`, first half):
`|𝓡(X)| < (log X + 2)²/X` for `X ≥ 8·10²⁶`. -/
theorem explicit_high_averaging {X : ℝ} (hX : (8e26:ℝ) ≤ X) :
    |averagingError X| < (Real.log X + 2) ^ 2 / X := by
  have hX0 := high_X_pos hX
  have hL := high_logX_lb hX
  have hupper := high_averaging_upper hX
  have hlower := high_averaging_lower hX
  rw [abs_lt]
  constructor
  · have hnum : 8.7 * (Real.log X + 2) + 0.2 < (Real.log X + 2) ^ 2 := by
      nlinarith
    have hdiv : (8.7 * (Real.log X + 2) + 0.2) / X < (Real.log X + 2) ^ 2 / X := by
      rw [div_lt_div_iff₀ hX0 hX0]
      nlinarith [mul_lt_mul_of_pos_right hnum hX0]
    linarith
  · have hnum : 0.7003 * ((Real.log X + 1) ^ 2 / 2 + 1)
        + 1.021 * (Real.log X + 2) + 0.2 < (Real.log X + 2) ^ 2 := by
      nlinarith [sq_nonneg (Real.log X)]
    have hdiv : (0.7003 * ((Real.log X + 1) ^ 2 / 2 + 1)
          + 1.021 * (Real.log X + 2) + 0.2) / X < (Real.log X + 2) ^ 2 / X := by
      rw [div_lt_div_iff₀ hX0 hX0]
      nlinarith [mul_lt_mul_of_pos_right hnum hX0]
    linarith

/-- **High-interval averaging error, numeric form**
(`cor:explicit-high-averaging`, eq. `explicit-high-averaging`, second half):
`|𝓡(X)| < 2·10⁻²⁴` for `X ≥ 8·10²⁶`.  (The realized enclosure is
`|𝓡(X)| < 1.94·10⁻²⁴`.) -/
theorem explicit_high_averaging_small {X : ℝ} (hX : (8e26:ℝ) ≤ X) :
    |averagingError X| < 2e-24 := by
  have hX0 := high_X_pos hX
  have hL := high_logX_lb hX
  have hupper := high_averaging_upper hX
  have hlower := high_averaging_lower hX
  have hpolysq := high_poly_sq hL
  have hpolylin := high_poly_lin hL
  rw [high_exp_log hX] at hpolysq hpolylin
  have hub : (0.7003 * ((Real.log X + 1) ^ 2 / 2 + 1)
      + 1.021 * (Real.log X + 2) + 0.2) / X < 2e-24 := by
    rw [div_lt_iff₀ hX0]
    linarith
  have hlb : (8.7 * (Real.log X + 2) + 0.2) / X < 2e-24 := by
    rw [div_lt_iff₀ hX0]
    linarith
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

/-! ## The high-interval bound for `ρ` (`cor:explicit-high-rho`)

The manuscript's proof of `cor:explicit-high-rho` applies
eq. `threshold-displacement` at `x = E_{s−1}(u)`.  Here the displacement
identity is derived inline in `high_rho_abs_lt` (write `a = e^x`,
`n_* = m_*(a)`, `z = log n_*`, `δ = g(n_*) − a ∈ (0, log 2]`; then
`ρ(x) = (x/z)𝓡(z) + ((x/z)𝓑(z) − 𝓑(x)) − xδ/n_*`). -/

section HighRho

/-- `𝓑(x) ≤ log 2·(log x + 2.4)` for `x ≥ 8·10²⁶` (paper:
`𝓑(x) < log 2·(log x + 2)`, split at `⌊x/log 2⌋`; the realized additive
constant is `2.4`, amply inside the corollary's factor-`10` headroom). -/
theorem high_B_le {x : ℝ} (hx : (8e26:ℝ) ≤ x) :
    B x ≤ Real.log 2 * (Real.log x + 2.4) := by
  have hx0 : (0:ℝ) < x := by linarith
  have hK1 : 1 ≤ ⌊x / Real.log 2⌋₊ := by
    apply Nat.le_floor
    rw [le_div_iff₀ low_log2_pos]
    push_cast
    nlinarith [Real.log_two_lt_d9]
  have hKle : ((⌊x / Real.log 2⌋₊ : ℕ) : ℝ) ≤ x / Real.log 2 :=
    Nat.floor_le (by positivity)
  have hKgt : x / Real.log 2 < ((⌊x / Real.log 2⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hBle := low_B_le_partial_add_tail (X := x) ⌊x / Real.log 2⌋₊
  have hpartial : ∑ m ∈ Finset.Icc 1 ⌊x / Real.log 2⌋₊,
      min (g m) x / ((m:ℝ) * ((m:ℝ) + 1))
      ≤ Real.log 2 * (1 + Real.log ((⌊x / Real.log 2⌋₊ : ℕ) : ℝ)) := by
    have hterm : ∀ m ∈ Finset.Icc 1 ⌊x / Real.log 2⌋₊,
        min (g m) x / ((m:ℝ) * ((m:ℝ) + 1)) ≤ Real.log 2 * (1 / (m:ℝ)) := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
      have hg : min (g m) x ≤ (m:ℝ) * Real.log 2 :=
        le_trans (min_le_left _ _) (g_le_mul_log_two m)
      calc min (g m) x / ((m:ℝ) * ((m:ℝ) + 1))
          ≤ (m:ℝ) * Real.log 2 / ((m:ℝ) * ((m:ℝ) + 1)) :=
            div_le_div_of_nonneg_right hg (by positivity)
        _ = Real.log 2 * (1 / ((m:ℝ) + 1)) := by
            field_simp
        _ ≤ Real.log 2 * (1 / (m:ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ low_log2_pos.le
            apply div_le_div_of_nonneg_left (by norm_num) hm0 (by linarith)
    calc ∑ m ∈ Finset.Icc 1 ⌊x / Real.log 2⌋₊,
          min (g m) x / ((m:ℝ) * ((m:ℝ) + 1))
        ≤ ∑ m ∈ Finset.Icc 1 ⌊x / Real.log 2⌋₊, Real.log 2 * (1 / (m:ℝ)) :=
          Finset.sum_le_sum hterm
      _ = Real.log 2 * ∑ m ∈ Finset.Icc 1 ⌊x / Real.log 2⌋₊, 1 / (m:ℝ) := by
          rw [← Finset.mul_sum]
      _ ≤ Real.log 2 * (1 + Real.log ((⌊x / Real.log 2⌋₊ : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_one_div_le_log _) low_log2_pos.le
  have hlogK : Real.log ((⌊x / Real.log 2⌋₊ : ℕ) : ℝ) ≤ Real.log x + 0.37 := by
    have hK0 : (0:ℝ) < ((⌊x / Real.log 2⌋₊ : ℕ) : ℝ) := by exact_mod_cast hK1
    have h1 : Real.log ((⌊x / Real.log 2⌋₊ : ℕ) : ℝ)
        ≤ Real.log (x / Real.log 2) := Real.log_le_log hK0 hKle
    rw [Real.log_div hx0.ne' low_log2_pos.ne'] at h1
    have hexp037 : (1.445:ℝ) ≤ Real.exp 0.37 := by
      have h0185 : (1.2021125:ℝ) ≤ Real.exp 0.185 := by
        nlinarith [Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.185 by norm_num)]
      have hsq : Real.exp 0.185 ^ (2:ℕ) = Real.exp 0.37 := by
        rw [← Real.exp_nat_mul]
        norm_num
      nlinarith [Real.exp_pos (0.185:ℝ)]
    have hlow : Real.exp (-0.37:ℝ) ≤ Real.log 2 := by
      have hmul : Real.exp (-0.37:ℝ) * Real.exp (0.37:ℝ) = 1 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith [Real.exp_pos (-0.37:ℝ), Real.log_two_gt_d9]
    have h037 : -0.37 ≤ Real.log (Real.log 2) := by
      have h := Real.log_le_log (Real.exp_pos _) hlow
      rw [Real.log_exp] at h
      exact h
    linarith
  have htail : x / (((⌊x / Real.log 2⌋₊ : ℕ) : ℝ) + 1) ≤ Real.log 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h := (div_lt_iff₀ low_log2_pos).mp hKgt
    nlinarith
  calc B x ≤ (∑ m ∈ Finset.Icc 1 ⌊x / Real.log 2⌋₊,
        min (g m) x / ((m:ℝ) * ((m:ℝ) + 1)))
        + x / (((⌊x / Real.log 2⌋₊ : ℕ) : ℝ) + 1) := hBle
    _ ≤ Real.log 2 * (1 + Real.log ((⌊x / Real.log 2⌋₊ : ℕ) : ℝ)) + Real.log 2 := by
        linarith
    _ ≤ Real.log 2 * (Real.log x + 2.4) := by
        nlinarith [low_log2_pos, hlogK]

theorem high_B_nonneg {x : ℝ} (hx0 : 0 ≤ x) : 0 ≤ B x := by
  rw [B]
  exact tsum_nonneg fun m => low_BTerm_nonneg hx0 m

/-- Log-Lipschitz-type increment bound (paper:
`𝓑(z) − 𝓑(x) ≤ (log 2)·log(z/x)`; realized in the linearized form
`≤ log 2·(z − x)/x` via the chord bound and `m_*(x) > x/log 2`). -/
theorem high_B_sub_le {x z : ℝ} (hx : (8e26:ℝ) ≤ x) (hxz : x ≤ z) :
    B z - B x ≤ Real.log 2 * (z - x) / x := by
  have hx0 : (0:ℝ) < x := by linarith
  have h1 := B_sub_le_div_mStar (show (0:ℝ) ≤ x by linarith) hxz
  have hm := mStar_lower x
  have h2 : (z - x) / (mStar x : ℝ) ≤ (z - x) / (x / Real.log 2) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) hm.le
  have h3 : (z - x) / (x / Real.log 2) = Real.log 2 * (z - x) / x := by
    field_simp
  linarith [h3 ▸ h2]

set_option maxHeartbeats 1000000 in
/-- **Depth-free high-interval bound for `ρ`** (the substance of
`cor:explicit-high-rho`): `|ρ(x)| < 10·(log x)²/x` for `x ≥ 8·10²⁶`, via
eq. `threshold-displacement` and `explicit_high_averaging` at
`z = log m_*(e^x)`.  (The realized total is `< 2.5·(log x)²/x`; the paper's
constant `10` leaves ample headroom.) -/
theorem high_rho_abs_lt {x : ℝ} (hx : (8e26:ℝ) ≤ x) :
    |rho x| < 10 * (Real.log x ^ 2 / x) := by
  have hx0 : (0:ℝ) < x := by linarith
  have hlam : (61.9:ℝ) ≤ Real.log x := high_logX_lb hx
  have hxs := high_logX_le_sqrt hx
  have hs := high_sqrt_lb hx
  have hss := high_sqrt_sq hx
  have ht0 : (0:ℝ) < Real.exp x := Real.exp_pos x
  have ht9 : Real.exp (9 * 10 ^ 6 : ℝ) ≤ Real.exp x :=
    Real.exp_le_exp.mpr (by linarith)
  have hn_lb : Real.exp x / Real.log 2 < ((mStar (Real.exp x) : ℕ) : ℝ) :=
    mStar_lower (Real.exp x)
  have hn_ub : ((mStar (Real.exp x) : ℕ) : ℝ)
      < 4 * Real.exp x * Real.log (2 * Real.exp x) :=
    mStar_upper_explicit ht9
  have hn_pos : (0:ℝ) < ((mStar (Real.exp x) : ℕ) : ℝ) :=
    lt_trans (by positivity) hn_lb
  have hnt : Real.exp x < ((mStar (Real.exp x) : ℕ) : ℝ) := by
    have hlog2lt1 : Real.log 2 < 1 := by nlinarith [Real.log_two_lt_d9]
    have hstep : Real.exp x < Real.exp x / Real.log 2 := by
      rw [lt_div_iff₀ low_log2_pos]
      nlinarith
    linarith
  have hxz : x ≤ Real.log ((mStar (Real.exp x) : ℕ) : ℝ) := by
    have h := Real.log_le_log ht0 hnt.le
    rwa [Real.log_exp] at h
  have hz8 : (8e26:ℝ) ≤ Real.log ((mStar (Real.exp x) : ℕ) : ℝ) :=
    le_trans hx hxz
  have hz0 : (0:ℝ) < Real.log ((mStar (Real.exp x) : ℕ) : ℝ) := by linarith
  -- `z ≤ x + log x + 2`
  have hz_ub : Real.log ((mStar (Real.exp x) : ℕ) : ℝ) ≤ x + Real.log x + 2 := by
    have hlog2t : Real.log (2 * Real.exp x) = Real.log 2 + x := by
      rw [Real.log_mul (by norm_num) ht0.ne', Real.log_exp]
    have hlog2tpos : (0:ℝ) < Real.log (2 * Real.exp x) := by
      rw [hlog2t]
      linarith [low_log2_pos]
    have h1 : Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
        ≤ Real.log (4 * Real.exp x * Real.log (2 * Real.exp x)) :=
      Real.log_le_log hn_pos hn_ub.le
    have h2 : Real.log (4 * Real.exp x * Real.log (2 * Real.exp x))
        = Real.log 4 + x + Real.log (Real.log (2 * Real.exp x)) := by
      rw [Real.log_mul (by positivity) hlog2tpos.ne',
        Real.log_mul (by norm_num) ht0.ne', Real.log_exp]
    have h3 : Real.log (Real.log (2 * Real.exp x)) ≤ Real.log x + 0.1 := by
      rw [hlog2t]
      have h4 : Real.log 2 + x ≤ 1.1 * x := by
        nlinarith [Real.log_two_lt_d9]
      have h5 : Real.log (Real.log 2 + x) ≤ Real.log (1.1 * x) :=
        Real.log_le_log (by linarith [low_log2_pos]) h4
      have h6 : Real.log (1.1 * x) = Real.log 1.1 + Real.log x :=
        Real.log_mul (by norm_num) hx0.ne'
      have h7 : Real.log 1.1 ≤ 0.1 := by
        nlinarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 1.1 by norm_num)]
      linarith
    have hlog4 : Real.log 4 ≤ 1.3862943616 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
        norm_num
      linarith [Real.log_two_lt_d9]
    linarith [h2 ▸ h1]
  -- `δ ∈ (0, log 2]`
  have hdelta_pos : Real.exp x < g (mStar (Real.exp x)) := lt_g_mStar (Real.exp x)
  have hdelta_ub : g (mStar (Real.exp x)) ≤ Real.exp x + Real.log 2 := by
    have h1 : g (mStar (Real.exp x) - 1) ≤ Real.exp x := g_mStar_sub_one_le ht0.le
    have hn1 : 1 ≤ mStar (Real.exp x) := mStar_pos ht0.le
    have hs' := S_succ_le_two_mul (mStar (Real.exp x) - 1)
    have hn1' : mStar (Real.exp x) - 1 + 1 = mStar (Real.exp x) := by omega
    rw [hn1'] at hs'
    have hSpos : (0:ℝ) < ((S (mStar (Real.exp x) - 1) : ℕ) : ℝ) := by
      exact_mod_cast S_pos (mStar (Real.exp x) - 1)
    have hlogstep : Real.log ((S (mStar (Real.exp x)) : ℕ) : ℝ)
        ≤ Real.log (2 * ((S (mStar (Real.exp x) - 1) : ℕ) : ℝ)) := by
      apply Real.log_le_log (by exact_mod_cast S_pos (mStar (Real.exp x)))
      exact_mod_cast hs'
    rw [Real.log_mul (by norm_num) hSpos.ne'] at hlogstep
    have hg1 : g (mStar (Real.exp x)) = Real.log ((S (mStar (Real.exp x)) : ℕ) : ℝ) := rfl
    have hg2 : g (mStar (Real.exp x) - 1)
        = Real.log ((S (mStar (Real.exp x) - 1) : ℕ) : ℝ) := rfl
    rw [hg1]
    rw [hg2] at h1
    linarith
  -- the displacement identity
  have hexpz : Real.exp (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))
      = ((mStar (Real.exp x) : ℕ) : ℝ) := Real.exp_log hn_pos
  have hRz : averagingError (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))
      = Real.log ((mStar (Real.exp x) : ℕ) : ℝ) / ((mStar (Real.exp x) : ℕ) : ℝ)
          * g (mStar (Real.exp x))
        - B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) := by
    rw [averagingError, hexpz, FReal, Nat.floor_natCast]
  have hrho_id : rho x
      = x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
          * averagingError (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))
        + (x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
            * B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) - B x)
        - x * (g (mStar (Real.exp x)) - Real.exp x)
            / ((mStar (Real.exp x) : ℕ) : ℝ) := by
    rw [rho, hRz]
    field_simp
    ring
  -- piece 1
  have hxz_le_one : x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hz0]
    exact hxz
  have hxz0 : (0:ℝ) ≤ x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ) := by positivity
  have hRz_bound := explicit_high_averaging hz8
  have hlogz : Real.log (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))
      ≤ Real.log x + 0.7 := by
    have h2x : Real.log ((mStar (Real.exp x) : ℕ) : ℝ) ≤ 2 * x := by nlinarith
    calc Real.log (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))
        ≤ Real.log (2 * x) := Real.log_le_log hz0 h2x
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ Real.log x + 0.7 := by nlinarith [Real.log_two_lt_d9]
  have hpiece1 : x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
      * |averagingError (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))|
      < (Real.log x + 3) ^ 2 / x := by
    have h2 : (Real.log (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) + 2) ^ 2
        ≤ (Real.log x + 3) ^ 2 := by
      have hlz0 : (0:ℝ) ≤ Real.log (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) :=
        Real.log_nonneg (by linarith)
      nlinarith
    have h3 : (Real.log (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) + 2) ^ 2
          / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
        ≤ (Real.log x + 3) ^ 2 / x :=
      div_le_div₀ (by positivity) h2 hx0 hxz
    have h4 : x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
        * |averagingError (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))|
        ≤ |averagingError (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))| := by
      nlinarith [abs_nonneg (averagingError (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))),
        mul_nonneg (sub_nonneg.mpr hxz_le_one)
          (abs_nonneg (averagingError (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))))]
    linarith
  -- piece 2
  have hzx_ub : Real.log ((mStar (Real.exp x) : ℕ) : ℝ) - x ≤ Real.log x + 2 := by
    linarith
  have hBz_sub := high_B_sub_le hx hxz
  have hBx_ub := high_B_le hx
  have hBx0 : 0 ≤ B x := high_B_nonneg (by linarith)
  have hBmono : B x ≤ B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) := B_mono hxz
  have hpiece2 : |x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
        * B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) - B x|
      ≤ Real.log 2 * (Real.log x + 2) / x
        + (Real.log x + 2) / x * (Real.log 2 * (Real.log x + 2.4)) := by
    have hid : x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
          * B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) - B x
        = x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
            * (B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) - B x)
          - (1 - x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) * B x := by
      ring
    have h1 : x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
          * (B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) - B x)
        ≤ Real.log 2 * (Real.log x + 2) / x := by
      have hBzx0 : 0 ≤ B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) - B x := by
        linarith
      have hstep : x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
            * (B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) - B x)
          ≤ B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) - B x := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hxz_le_one) hBzx0]
      have hstep2 : Real.log 2 * (Real.log ((mStar (Real.exp x) : ℕ) : ℝ) - x) / x
          ≤ Real.log 2 * (Real.log x + 2) / x := by
        apply div_le_div_of_nonneg_right _ hx0.le
        nlinarith [low_log2_pos]
      linarith
    have h2 : (1 - x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) * B x
        ≤ (Real.log x + 2) / x * (Real.log 2 * (Real.log x + 2.4)) := by
      have hfrac : 1 - x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
          ≤ (Real.log x + 2) / x := by
        have hid2 : 1 - x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
            = (Real.log ((mStar (Real.exp x) : ℕ) : ℝ) - x)
              / Real.log ((mStar (Real.exp x) : ℕ) : ℝ) := by
          field_simp
        rw [hid2]
        calc (Real.log ((mStar (Real.exp x) : ℕ) : ℝ) - x)
              / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
            ≤ (Real.log ((mStar (Real.exp x) : ℕ) : ℝ) - x) / x :=
              div_le_div_of_nonneg_left (by linarith) hx0 hxz
          _ ≤ (Real.log x + 2) / x :=
              div_le_div_of_nonneg_right hzx_ub hx0.le
      have hfrac0 : 0 ≤ 1 - x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ) := by
        linarith
      exact mul_le_mul hfrac hBx_ub hBx0 (div_nonneg (by linarith) hx0.le)
    have hp1 : 0 ≤ x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
        * (B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) - B x) := by
      have hBzx0 : 0 ≤ B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) - B x := by
        linarith
      positivity
    have hp2 : 0 ≤ (1 - x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) * B x := by
      have hfrac0 : 0 ≤ 1 - x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ) := by
        linarith
      positivity
    rw [hid, abs_le]
    constructor <;> linarith
  -- piece 3
  have hpiece3 : x * (g (mStar (Real.exp x)) - Real.exp x)
      / ((mStar (Real.exp x) : ℕ) : ℝ) ≤ 1 / x := by
    have hdelta0 : 0 ≤ g (mStar (Real.exp x)) - Real.exp x := by linarith
    have h1 : x * (g (mStar (Real.exp x)) - Real.exp x)
        / ((mStar (Real.exp x) : ℕ) : ℝ) ≤ x / ((mStar (Real.exp x) : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hn_pos.le
      have hd1 : g (mStar (Real.exp x)) - Real.exp x ≤ 1 := by
        nlinarith [Real.log_two_lt_d9]
      nlinarith
    have h2 : x / ((mStar (Real.exp x) : ℕ) : ℝ) ≤ x / Real.exp x :=
      div_le_div_of_nonneg_left hx0.le ht0 hnt.le
    have h3 : x / Real.exp x ≤ 1 / x := by
      rw [div_le_div_iff₀ ht0 hx0]
      have hq : x / 4 + 1 ≤ Real.exp (x / 4) := Real.add_one_le_exp _
      have hp4 : Real.exp (x / 4) ^ (4:ℕ) = Real.exp x := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      have hx4 : (x / 4 : ℝ) ^ (4:ℕ) ≤ Real.exp (x / 4) ^ (4:ℕ) :=
        pow_le_pow_left₀ (by positivity) (by linarith) 4
      have h256 : (256:ℝ) ≤ x ^ 2 := by nlinarith
      have hkey : 256 * x ^ 2 ≤ x ^ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_right h256 (sq_nonneg x)
      have hid4 : (x / 4 : ℝ) ^ (4:ℕ) = x ^ 2 * x ^ 2 / 256 := by ring
      nlinarith [hp4 ▸ hx4]
    calc x * (g (mStar (Real.exp x)) - Real.exp x)
        / ((mStar (Real.exp x) : ℕ) : ℝ)
        ≤ x / ((mStar (Real.exp x) : ℕ) : ℝ) := h1
      _ ≤ x / Real.exp x := h2
      _ ≤ 1 / x := h3
  have hpiece3_0 : 0 ≤ x * (g (mStar (Real.exp x)) - Real.exp x)
      / ((mStar (Real.exp x) : ℕ) : ℝ) := by
    have hdelta0 : 0 ≤ g (mStar (Real.exp x)) - Real.exp x := by linarith
    positivity
  -- assemble
  have habs3 : |rho x| ≤ x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
        * |averagingError (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))|
      + |x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
          * B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) - B x|
      + x * (g (mStar (Real.exp x)) - Real.exp x)
          / ((mStar (Real.exp x) : ℕ) : ℝ) := by
    rw [hrho_id]
    have h1 : |x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
        * averagingError (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))|
        = x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
          * |averagingError (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))| := by
      rw [abs_mul, abs_of_nonneg hxz0]
    have t1 := abs_add_le
      (x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
        * averagingError (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)))
      (x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
        * B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) - B x)
    have t2 := abs_add_le
      (x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
          * averagingError (Real.log ((mStar (Real.exp x) : ℕ) : ℝ))
        + (x / Real.log ((mStar (Real.exp x) : ℕ) : ℝ)
            * B (Real.log ((mStar (Real.exp x) : ℕ) : ℝ)) - B x))
      (-(x * (g (mStar (Real.exp x)) - Real.exp x)
          / ((mStar (Real.exp x) : ℕ) : ℝ)))
    rw [← sub_eq_add_neg, abs_neg,
      abs_of_nonneg hpiece3_0] at t2
    linarith [h1 ▸ t1]
  have hfinal : (Real.log x + 3) ^ 2 / x
      + (Real.log 2 * (Real.log x + 2) / x
          + (Real.log x + 2) / x * (Real.log 2 * (Real.log x + 2.4)))
      + 1 / x
      ≤ 10 * (Real.log x ^ 2 / x) := by
    have hid : (Real.log x + 3) ^ 2 / x
        + (Real.log 2 * (Real.log x + 2) / x
            + (Real.log x + 2) / x * (Real.log 2 * (Real.log x + 2.4)))
        + 1 / x
        = ((Real.log x + 3) ^ 2 + Real.log 2 * (Real.log x + 2)
            + (Real.log x + 2) * Real.log 2 * (Real.log x + 2.4) + 1) / x := by
      ring
    have hid2 : 10 * (Real.log x ^ 2 / x) = 10 * Real.log x ^ 2 / x := by
      ring
    rw [hid, hid2]
    apply div_le_div_of_nonneg_right _ hx0.le
    nlinarith [Real.log_two_lt_d9, low_log2_pos, sq_nonneg (Real.log x),
      mul_nonneg (show (0:ℝ) ≤ Real.log x + 2 by linarith)
        (show (0:ℝ) ≤ Real.log x + 2.4 by linarith)]
  linarith

/-- **High-interval bound for `ρ`** (`cor:explicit-high-rho`,
eq. `explicit-high-rho`): in the notation of eq. `a-rho`, if
`E_{s−1}(u) ≥ 8·10²⁶` then `|ρ_s(u)| < 10·E_{s−2}(u)²/E_{s−1}(u)`.

Hypothesis packaging: `2 ≤ s` is needed only for the `ℕ`-subtraction identity
`E_{s−1}(u) = exp(E_{s−2}(u))`; no hypothesis on `u` is needed beyond `hbig`. -/
theorem rhoDepth_lt_of_big {s : ℕ} (hs : 2 ≤ s) {u : ℝ}
    (hbig : (8e26:ℝ) ≤ E (s - 1) u) :
    |rhoDepth s u| < 10 * (E (s - 2) u ^ 2 / E (s - 1) u) := by
  have hE : E (s - 1) u = Real.exp (E (s - 2) u) := by
    conv_lhs => rw [show s - 1 = (s - 2) + 1 by omega, E_succ]
  have hlog : Real.log (E (s - 1) u) = E (s - 2) u := by
    rw [hE, Real.log_exp]
  have h := high_rho_abs_lt hbig
  rw [hlog] at h
  exact h

end HighRho

end Erdos320
