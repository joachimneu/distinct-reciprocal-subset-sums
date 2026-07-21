import Erdos320.Lemmas.ShellDecomposition
import Erdos320.Lemmas.ExpFloor
import Erdos320.Lemmas.ShellCounts
import Erdos320.Lemmas.IteratedExpBounds
import Erdos320.Lemmas.LogSumBounds
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Standing parameter choices for `prop:averaging-relation`

The proof of `prop:averaging-relation` opens with the standing parameter
choices
```
N = ⌊e^X⌋,   M = ⌊X³⌋,   Q = ⌊N/(M+1)⌋,
```
and asserts that "for large `X` the hypotheses of
`prop:large-prime-decomposition` hold".  This file makes those choices and
their basic consequences explicit, as shared plumbing for the upper and lower
halves of the averaging relation:

* `shellCutoff` — the paper's `M = ⌊X³⌋`;
* growth facts making the hypotheses of `g_shell_decomposition` checkable
  (`averaging_hQN`, `averaging_hQ2`) and two-sided real bounds on the
  `ℕ`-division `Q` (`Q_real_lower`, `Q_real_upper`, `two_le_Q`, `Q_le_N`);
* shell-endpoint alignment (`shellPrimes_card_eq` — the shell count is an
  exact difference of `primePi` values at *real* endpoints, so the FKS input
  applies verbatim) and logarithmic bounds on the primes in a shell
  (`shell_prime_le_log`, `shell_prime_log_ge`, `shell_prime_gt_half_exp`,
  `one_lt_shell_ratio`);
* the paper's `Σ_{m ≤ X³} |ε_m| = o(X⁻²)` for the FKS endpoint errors, made
  explicit as `fks_shell_total_le` (total normalized FKS error `≤ 1/X²`),
  via the unconditional decay bound `fksError_le_simple`;
* the smooth-core estimate: the paper's "the core term is harmless after
  multiplication by `X/N`" becomes `core_normalized_le` (normalized fibre
  error plus `log 𝔇_Q` is `≤ 3/X²`).

**Threshold convention.**  Every `X`-dependent statement in this file uses the
single explicit threshold `(10:ℝ)^7 ≤ X`.  The binding constraint is the FKS
error total `fks_shell_total_le`, whose crude-but-fully-explicit route needs
`e^{0.4√X} ≥ 480·X⁴` (comfortably true from `X ≥ 4·10⁵` on; at `X = 10⁷` the
margin is astronomical); every other lemma here would already hold at far
smaller thresholds (mostly `X ≥ 50` or so), so the uniform `X₀ = 10⁷` is
chosen for a single, simple standing hypothesis, not because any individual
estimate is tight.  The paper's statements are asymptotic ("for large `X`"),
so a large explicit threshold is faithful.

**Constant conventions (all documented deviations are *weaker-side* slack,
never a strengthening of the paper's claims):**

* `Q_real_lower` certifies `Q ≥ e^X/(4X³)` (the `ℕ`-floor of the division
  costs less than a factor `2` on top of `N ≥ e^X − 1`, `M+1 ≤ 2X³`);
* `Q_real_upper` certifies `Q ≤ e^X/X³` with constant `1` (using `N ≤ e^X`
  and `M + 1 ≥ X³`);
* `shell_prime_log_ge` uses the slack `2` (the true loss is
  `log 2 + o(1) < 0.7`);
* `fksError_le_simple` absorbs the `√(log t)` factor at the global maximum of
  `s·e^{−0.0476 s}`, namely `1/(0.0476·e) < 7.73 < 8`, giving the
  unconditional `𝓔(t) ≤ 80·t·e^{−0.8·√(log t)}` (paper: the same absorption
  with `≪`-constants);
* `core_normalized_le` lands at `3/X²`: the `θ(Q)`-term contributes exactly
  `2.8/X²` through `θ(Q) ≤ (log 4)·Q ≤ 1.4·Q` and `X/N ≤ 2X·e^{−X}`, and the
  fibre and higher-layer terms are exponentially negligible (`≤ 0.2/X²`).
-/

namespace Erdos320

/-- The paper's shell cutoff `M = ⌊X³⌋` (`prop:averaging-relation`).
Standing conventions for this file and its consumers:
`N := ⌊Real.exp X⌋₊`, `M := shellCutoff X`, and `Q := N / (M + 1)` with `/`
the `ℕ`-division (so `Q = ⌊N/(M+1)⌋`, the paper's `Q`). -/
noncomputable def shellCutoff (X : ℝ) : ℕ := ⌊X ^ 3⌋₊

/-- `M ≥ 1` once `X ≥ 1`. -/
theorem one_le_shellCutoff {X : ℝ} (hX : 1 ≤ X) : 1 ≤ shellCutoff X := by
  simp only [shellCutoff]
  exact Nat.le_floor (by exact_mod_cast (one_le_pow₀ hX : (1 : ℝ) ≤ X ^ 3))

/-- `M ≤ X³` as real numbers (floor bound). -/
theorem shellCutoff_cast_le {X : ℝ} (hX : 0 ≤ X) : ((shellCutoff X : ℕ) : ℝ) ≤ X ^ 3 := by
  simp only [shellCutoff]
  exact Nat.floor_le (by positivity)

/-- `X³ < M + 1` as real numbers (floor bound), i.e. `M + 1 ≥ X³`. -/
theorem cube_lt_shellCutoff_add_one (X : ℝ) : X ^ 3 < ((shellCutoff X : ℕ) : ℝ) + 1 := by
  simp only [shellCutoff]
  exact Nat.lt_floor_add_one (X ^ 3)

/-! ## Shared elementary facts

These small facts are re-used verbatim by both halves of the averaging
relation (`AveragingUpper`, `AveragingLower`); they are hoisted here so each
is proved exactly once. -/

/-- `N/(m+1) ≤ N/m` for `N ≥ 0`, `m > 0` — the shell endpoints are ordered. -/
theorem div_add_one_le_div {N : ℝ} (hN : 0 ≤ N) {m : ℝ} (hm : 0 < m) :
    N / (m + 1) ≤ N / m := by
  have h1 := one_div_le_one_div_of_le hm (by linarith : m ≤ m + 1)
  calc N / (m + 1) = N * (1 / (m + 1)) := by ring
    _ ≤ N * (1 / m) := mul_le_mul_of_nonneg_left h1 hN
    _ = N / m := by ring

/-- The shell length identity `N/m − N/(m+1) = N/(m(m+1))` (paper's
`x_m − y_m = N/[m(m+1)]`). -/
theorem shell_endpoint_gap {N m : ℝ} (hm : 0 < m) :
    N / m - N / (m + 1) = N / (m * (m + 1)) := by
  have h1 : m ≠ 0 := hm.ne'
  have h2 : m + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- `Real.log 2 ≤ 1` (the tangent-line bound `log x ≤ x − 1` at `x = 2`). -/
theorem log_two_le_one : Real.log 2 ≤ 1 := by
  linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]

/-- `Real.log 4 ≤ 1.4` (via `log 4 = 2·log 2` and `log 2 < 0.694`). -/
theorem log_four_le : Real.log 4 ≤ 1.4 := by
  linarith [Real.log_four_eq, Real.log_two_lt_d9]

/-- `16 ≤ log X` for `X ≥ 10⁷` (since `e¹⁶ < 8.9·10⁶ < 10⁷`); the numeric
anchor that absorbs all sub-leading `1/X`-type errors into `(log X)²/X`. -/
theorem sixteen_le_log {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) : (16 : ℝ) ≤ Real.log X := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX
  rw [Real.le_log_iff_exp_le hX0]
  have h1 : Real.exp 1 ^ (16 : ℕ) = Real.exp 16 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h2 : Real.exp 1 ^ (16 : ℕ) ≤ (2.7182818286 : ℝ) ^ (16 : ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 16
  have h3 : (2.7182818286 : ℝ) ^ (16 : ℕ) ≤ (10 : ℝ) ^ 7 := by norm_num
  linarith [h1 ▸ h2, h3, hX]

/-- `e^X = e^{X/2}·e^{X/2}`. -/
theorem exp_eq_exp_half_mul (X : ℝ) :
    Real.exp X = Real.exp (X / 2) * Real.exp (X / 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- `log(e^X/2/y) = X − log 2 − log y` for `y > 0`. -/
theorem log_exp_div_two_div {y : ℝ} (hy : 0 < y) (X : ℝ) :
    Real.log (Real.exp X / 2 / y) = X - Real.log 2 - Real.log y := by
  rw [Real.log_div (by positivity : (0 : ℝ) < Real.exp X / 2).ne' hy.ne',
    Real.log_div (Real.exp_pos X).ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp]

/-- Uniform bound on a shell index: `m + 1 ≤ 2X³` for `m ≤ M = ⌊X³⌋`,
`X ≥ 1` (from `m ≤ X³` and `X³ ≥ 1`). -/
theorem shell_index_add_one_le {X : ℝ} (hX1 : 1 ≤ X) {m : ℕ}
    (hm : m ≤ shellCutoff X) :
    (m : ℝ) + 1 ≤ 2 * X ^ 3 := by
  have hX0 : (0 : ℝ) < X := by linarith
  have h1 : (m : ℝ) ≤ ((shellCutoff X : ℕ) : ℝ) := Nat.cast_le.mpr hm
  have h2 : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ hX1
  linarith [shellCutoff_cast_le hX0.le]

/-- Uniform logarithmic bound over the shell indices: `log(m+1) ≤ log 2 + 3·log X`
for `m ≤ M = ⌊X³⌋`, `X ≥ 1` (from `m + 1 ≤ 2X³`). -/
theorem shell_log_add_one_le {X : ℝ} (hX1 : 1 ≤ X) {m : ℕ}
    (hm : m ≤ shellCutoff X) :
    Real.log ((m : ℝ) + 1) ≤ Real.log 2 + 3 * Real.log X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have h1 : (m : ℝ) + 1 ≤ 2 * X ^ 3 := shell_index_add_one_le hX1 hm
  have h2 : Real.log ((m : ℝ) + 1) ≤ Real.log (2 * X ^ 3) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
  push_cast at h2
  linarith

/-- The normalization bridge `X/⌊e^X⌋ ≤ 2X/e^X` for `X ≥ 1` (from
`⌊e^X⌋ ≥ e^X/2`). -/
theorem div_expFloor_le {X : ℝ} (hX1 : 1 ≤ X) :
    X / (⌊Real.exp X⌋₊ : ℝ) ≤ 2 * X / Real.exp X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hN0 : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) := by exact_mod_cast one_le_expFloor hX1
  have hNge : Real.exp X / 2 ≤ (⌊Real.exp X⌋₊ : ℝ) := exp_div_two_le_expFloor hX1
  rw [div_le_div_iff₀ hN0 (Real.exp_pos X)]
  nlinarith [mul_le_mul_of_nonneg_left hNge (by linarith : (0 : ℝ) ≤ 2 * X)]

/-! ## Elementary exponential-growth estimates

All are single-Taylor-term consequences of `pow_div_factorial_le_exp`; the
`10⁷` threshold makes every margin enormous (see the module docstring). -/

/-- `64·X⁶ < e^X` for `X ≥ 10⁷` (via `e^X ≥ X¹⁰/10!`, so it suffices that
`X⁴ > 64·10! = 232 243 200`, amply true).  This single polynomial-vs-`exp`
comparison feeds all the `Q`-size estimates below. -/
theorem exp_gt_poly {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) : 64 * X ^ 6 < Real.exp X := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX
  have h := pow_div_factorial_le_exp hX0.le 10
  have hfac : ((Nat.factorial 10 : ℕ) : ℝ) = 3628800 := by norm_num
  rw [hfac] at h
  have hX4 : (10 : ℝ) ^ 28 ≤ X ^ 4 := by
    calc (10 : ℝ) ^ 28 = ((10 : ℝ) ^ 7) ^ 4 := by norm_num
      _ ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX 4
  have h6 : (0 : ℝ) < X ^ 6 := by positivity
  have hkey : 64 * X ^ 6 < X ^ 10 / 3628800 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3628800)]
    nlinarith [mul_le_mul_of_nonneg_left hX4 h6.le]
  linarith

/-- `30·X⁴ ≤ e^{X/2}` for `X ≥ 10⁷` (via `e^{X/2} ≥ (X/2)⁹/9!`, so it
suffices that `X⁵ ≥ 30·9!·2⁹ ≈ 5.6·10⁹`).  This is the workhorse behind the
shell-ratio lower bound and the smooth-core error absorption. -/
theorem poly_le_exp_half {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    30 * X ^ 4 ≤ Real.exp (X / 2) := by
  have hX0 : (0 : ℝ) ≤ X := le_trans (by norm_num) hX
  have h := pow_div_factorial_le_exp (by positivity : (0 : ℝ) ≤ X / 2) 9
  have hfac : ((Nat.factorial 9 : ℕ) : ℝ) = 362880 := by norm_num
  rw [hfac] at h
  have hX5 : (10 : ℝ) ^ 35 ≤ X ^ 5 := by
    calc (10 : ℝ) ^ 35 = ((10 : ℝ) ^ 7) ^ 5 := by norm_num
      _ ≤ X ^ 5 := pow_le_pow_left₀ (by norm_num) hX 5
  have h4nn : (0 : ℝ) ≤ X ^ 4 := by positivity
  have hkey : 30 * X ^ 4 ≤ (X / 2) ^ 9 / 362880 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 362880),
      show ((X / 2) : ℝ) ^ 9 = X ^ 9 / 512 by ring,
      le_div_iff₀ (by norm_num : (0 : ℝ) < 512)]
    nlinarith [mul_le_mul_of_nonneg_left hX5 h4nn]
  linarith

/-- `480·X⁴ ≤ e^{0.4·√X}` for `X ≥ 10⁷` (via `e^{0.4s} ≥ (0.4s)¹⁶/16!` at
`s = √X`, so it suffices that `X⁴ ≥ 480·16!/0.4¹⁶ ≈ 2.34·10²²`, and
`X⁴ ≥ 10²⁸`).  This is the explicit form of the paper's
`Σ|ε_m| ≪ X^{3/2}·log X·e^{−0.8√X} = o(X⁻²)` domination
(eq. `prime-shell-sum`). -/
theorem poly_le_exp_sqrt {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    480 * X ^ 4 ≤ Real.exp (0.4 * Real.sqrt X) := by
  have hX0 : (0 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hs0 : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg X
  have h := pow_div_factorial_le_exp (by positivity : (0 : ℝ) ≤ 0.4 * Real.sqrt X) 16
  have hfac : ((Nat.factorial 16 : ℕ) : ℝ) = 20922789888000 := by norm_num
  rw [hfac] at h
  have h16 : Real.sqrt X ^ 16 = X ^ 8 := by
    rw [show (16 : ℕ) = 2 * 8 from rfl, pow_mul, Real.sq_sqrt hX0]
  have hpow : (0.4 * Real.sqrt X) ^ 16 = 0.4 ^ 16 * X ^ 8 := by
    rw [mul_pow, h16]
  have hX4 : (10 : ℝ) ^ 28 ≤ X ^ 4 := by
    calc (10 : ℝ) ^ 28 = ((10 : ℝ) ^ 7) ^ 4 := by norm_num
      _ ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX 4
  have h4nn : (0 : ℝ) ≤ X ^ 4 := by positivity
  have hkey : 480 * X ^ 4 ≤ (0.4 * Real.sqrt X) ^ 16 / 20922789888000 := by
    rw [hpow, le_div_iff₀ (by norm_num : (0 : ℝ) < 20922789888000)]
    have hc : (0.4 : ℝ) ^ 16 = 65536 / 152587890625 := by norm_num
    rw [hc]
    nlinarith [mul_le_mul_of_nonneg_left hX4 h4nn]
  linarith

/-- The tangent-line bound `e·x ≤ eˣ` for every real `x` (equality at
`x = 1`); a one-step consequence of `1 + y ≤ e^y` at `y = x − 1`. -/
theorem exp_one_mul_le_exp (x : ℝ) : Real.exp 1 * x ≤ Real.exp x := by
  have h := Real.add_one_le_exp (x - 1)
  have h2 : Real.exp x = Real.exp 1 * Real.exp (x - 1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp 1 * (x - 1 + 1) ≤ Real.exp 1 * Real.exp (x - 1) :=
    mul_le_mul_of_nonneg_left h (Real.exp_pos 1).le
  rw [h2]
  calc Real.exp 1 * x = Real.exp 1 * (x - 1 + 1) := by ring
    _ ≤ Real.exp 1 * Real.exp (x - 1) := h3

/-! ## Basic facts about `Q = ⌊N/(M+1)⌋` -/

/-- The hypothesis `Q < N` of `g_shell_decomposition` for the standing
parameters (`prop:averaging-relation`: "For large `X` the hypotheses of
`prop:large-prime-decomposition` hold"). -/
theorem averaging_hQN {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    ⌊Real.exp X⌋₊ / (shellCutoff X + 1) < ⌊Real.exp X⌋₊ := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hN1 : 1 ≤ ⌊Real.exp X⌋₊ := one_le_expFloor hX1
  have hM1 : 1 ≤ shellCutoff X := one_le_shellCutoff hX1
  exact Nat.div_lt_self (by omega) (by omega)

/-- `Q ≤ N` for the standing parameters (`ℕ`-division shrinks). -/
theorem Q_le_N (X : ℝ) : ⌊Real.exp X⌋₊ / (shellCutoff X + 1) ≤ ⌊Real.exp X⌋₊ :=
  Nat.div_le_self _ _

/-- **Real lower bound on `Q`**: `e^X/(4X³) ≤ Q` for `X ≥ 10⁷`.  The
constant `4` absorbs both the floor in `N = ⌊e^X⌋ ≥ e^X − 1`, the bound
`M + 1 ≤ X³ + 1 ≤ 2X³`, and the `−1` lost to the `ℕ`-division floor
(`Q > N/(M+1) − 1`); the absorption uses `e^X ≥ 4X³ + 2`, which
`exp_gt_poly` gives with huge slack. -/
theorem Q_real_lower {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    Real.exp X / (4 * X ^ 3) ≤ ((⌊Real.exp X⌋₊ / (shellCutoff X + 1) : ℕ) : ℝ) := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hpoly := exp_gt_poly hX
  have hX3 : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ hX1
  have hX6 : X ^ 3 ≤ X ^ 6 := by
    nlinarith [mul_nonneg (pow_nonneg hX0.le 3) (sub_nonneg.mpr hX3)]
  have hNlow : Real.exp X - 1 ≤ (⌊Real.exp X⌋₊ : ℝ) := by
    linarith [Nat.sub_one_lt_floor (Real.exp X)]
  have hMhigh : ((shellCutoff X : ℕ) : ℝ) + 1 ≤ 2 * X ^ 3 :=
    shell_index_add_one_le hX1 le_rfl
  set Qr : ℝ := ((⌊Real.exp X⌋₊ / (shellCutoff X + 1) : ℕ) : ℝ) with hQr
  have hQ0 : (0 : ℝ) ≤ Qr := Nat.cast_nonneg _
  -- `ℕ`-division loses less than one: `N < (Q+1)·(M+1)`
  have hQdiv : (⌊Real.exp X⌋₊ : ℝ) < (Qr + 1) * (((shellCutoff X : ℕ) : ℝ) + 1) := by
    have h2 : ⌊Real.exp X⌋₊
        < (⌊Real.exp X⌋₊ / (shellCutoff X + 1) + 1) * (shellCutoff X + 1) := by
      have h4 : ⌊Real.exp X⌋₊ % (shellCutoff X + 1) < shellCutoff X + 1 :=
        Nat.mod_lt _ (Nat.succ_pos _)
      calc ⌊Real.exp X⌋₊
          = (shellCutoff X + 1) * (⌊Real.exp X⌋₊ / (shellCutoff X + 1))
              + ⌊Real.exp X⌋₊ % (shellCutoff X + 1) := (Nat.div_add_mod _ _).symm
        _ < (shellCutoff X + 1) * (⌊Real.exp X⌋₊ / (shellCutoff X + 1))
              + (shellCutoff X + 1) := Nat.add_lt_add_left h4 _
        _ = (⌊Real.exp X⌋₊ / (shellCutoff X + 1) + 1) * (shellCutoff X + 1) := by ring
    rw [hQr]
    exact_mod_cast h2
  have h5 : Real.exp X - 1 < (Qr + 1) * (2 * X ^ 3) := by
    calc Real.exp X - 1 ≤ (⌊Real.exp X⌋₊ : ℝ) := hNlow
      _ < (Qr + 1) * (((shellCutoff X : ℕ) : ℝ) + 1) := hQdiv
      _ ≤ (Qr + 1) * (2 * X ^ 3) := mul_le_mul_of_nonneg_left hMhigh (by linarith)
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * X ^ 3)]
  nlinarith [h5, hpoly, hX3, hX6]

/-- **Real upper bound on `Q`**: `Q ≤ e^X/X³` for `X ≥ 10⁷` — with constant
`1` (sharper than the task-sheet's provisional `2`), from `N ≤ e^X` and
`M + 1 > X³`. -/
theorem Q_real_upper {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    ((⌊Real.exp X⌋₊ / (shellCutoff X + 1) : ℕ) : ℝ) ≤ Real.exp X / X ^ 3 := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX
  have h1 : ((⌊Real.exp X⌋₊ / (shellCutoff X + 1) : ℕ) : ℝ)
      ≤ (⌊Real.exp X⌋₊ : ℝ) / (((shellCutoff X : ℕ) : ℝ) + 1) := by
    have h := Nat.cast_div_le (α := ℝ) (m := ⌊Real.exp X⌋₊) (n := shellCutoff X + 1)
    push_cast at h
    exact h
  calc ((⌊Real.exp X⌋₊ / (shellCutoff X + 1) : ℕ) : ℝ)
      ≤ (⌊Real.exp X⌋₊ : ℝ) / (((shellCutoff X : ℕ) : ℝ) + 1) := h1
    _ ≤ Real.exp X / X ^ 3 :=
        div_le_div₀ (Real.exp_pos X).le (expFloor_le_exp X) (pow_pos hX0 3)
          (le_of_lt (cube_lt_shellCutoff_add_one X))

/-- `2 ≤ Q` for `X ≥ 10⁷` (needed by `log_smoothPart_le`). -/
theorem two_le_Q {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    2 ≤ ⌊Real.exp X⌋₊ / (shellCutoff X + 1) := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hQ := Q_real_lower hX
  have hpoly := exp_gt_poly hX
  have hX3 : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ hX1
  have hX6 : X ^ 3 ≤ X ^ 6 := by
    nlinarith [mul_nonneg (pow_nonneg hX0.le 3) (sub_nonneg.mpr hX3)]
  have h2 : (2 : ℝ) ≤ Real.exp X / (4 * X ^ 3) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h3 : ((2 : ℕ) : ℝ) ≤ ((⌊Real.exp X⌋₊ / (shellCutoff X + 1) : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h3

/-- The hypothesis `N < Q²` of `g_shell_decomposition` for the standing
parameters: `⌊e^X⌋ < ⌊N/(M+1)⌋²`, from `Q ≥ e^X/(4X³)` and `e^X > 16X⁶`. -/
theorem averaging_hQ2 {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    ⌊Real.exp X⌋₊ < ⌊Real.exp X⌋₊ / (shellCutoff X + 1)
      * (⌊Real.exp X⌋₊ / (shellCutoff X + 1)) := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hQ := Q_real_lower hX
  have hpoly := exp_gt_poly hX
  have hX3 : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ hX1
  have hX6 : X ^ 3 ≤ X ^ 6 := by
    nlinarith [mul_nonneg (pow_nonneg hX0.le 3) (sub_nonneg.mpr hX3)]
  have h16 : 16 * X ^ 6 < Real.exp X := by nlinarith
  have hq0 : (0 : ℝ) ≤ Real.exp X / (4 * X ^ 3) := by positivity
  have hsq : Real.exp X / (4 * X ^ 3) * (Real.exp X / (4 * X ^ 3))
      ≤ ((⌊Real.exp X⌋₊ / (shellCutoff X + 1) : ℕ) : ℝ)
        * ((⌊Real.exp X⌋₊ / (shellCutoff X + 1) : ℕ) : ℝ) :=
    mul_le_mul hQ hQ hq0 (le_trans hq0 hQ)
  have hbig : Real.exp X < Real.exp X / (4 * X ^ 3) * (Real.exp X / (4 * X ^ 3)) := by
    rw [div_mul_div_comm, lt_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left h16 (Real.exp_pos X)]
  have hkey : (⌊Real.exp X⌋₊ : ℝ)
      < ((⌊Real.exp X⌋₊ / (shellCutoff X + 1) : ℕ) : ℝ)
        * ((⌊Real.exp X⌋₊ / (shellCutoff X + 1) : ℕ) : ℝ) := by
    linarith [expFloor_le_exp X]
  exact_mod_cast hkey

/-! ## Shell endpoints: real bounds and `primePi` alignment -/

/-- `e^{X/2} ≤ N/(m+1)` (real division) for every shell index `m ≤ M`,
`X ≥ 10⁷`: the shells of `prop:averaging-relation` live entirely above
`e^{X/2}`.  (Route: `N/(m+1) ≥ (e^X/2)/(2X³) = e^X/(4X³)` and
`4X³ ≤ e^{X/2}` via `poly_le_exp_half`.) -/
theorem half_exp_le_shell_ratio {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm : m ≤ shellCutoff X) :
    Real.exp (X / 2) ≤ (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1) := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hN : Real.exp X / 2 ≤ (⌊Real.exp X⌋₊ : ℝ) := exp_div_two_le_expFloor hX1
  have hmR : (m : ℝ) + 1 ≤ 2 * X ^ 3 := shell_index_add_one_le hX1 hm
  have hW := poly_le_exp_half hX
  have h4X3 : 4 * X ^ 3 ≤ Real.exp (X / 2) := by
    nlinarith [mul_nonneg (pow_nonneg hX0.le 3) (sub_nonneg.mpr hX1),
      pow_nonneg hX0.le 3]
  have hstep : Real.exp (X / 2) ≤ Real.exp X / 2 / (2 * X ^ 3) := by
    rw [div_div, le_div_iff₀ (by positivity)]
    have hEW : Real.exp X = Real.exp (X / 2) * Real.exp (X / 2) := exp_eq_exp_half_mul X
    nlinarith [mul_le_mul_of_nonneg_left h4X3 (Real.exp_pos (X / 2)).le, hEW]
  calc Real.exp (X / 2) ≤ Real.exp X / 2 / (2 * X ^ 3) := hstep
    _ ≤ (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1) :=
        div_le_div₀ (Nat.cast_nonneg _) hN (by positivity) hmR

/-- `1 < N/(m+1)` (real division) for every shell index `m ≤ M`, `X ≥ 10⁷`
(the `hbig` precondition of the shell-collision lower bound). -/
theorem one_lt_shell_ratio {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm : m ≤ shellCutoff X) :
    (1 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX
  have h := half_exp_le_shell_ratio hX hm
  have h2 : (1 : ℝ) < Real.exp (X / 2) := by
    have h3 := Real.add_one_le_exp (X / 2)
    linarith
  linarith

/-- `2 ≤ N/(m+1)` for shells `m ≤ M` at `X ≥ 10⁷` (the `2 ≤ a` hypothesis of
the FKS interval estimates). -/
theorem two_le_shell_ratio {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm : m ≤ shellCutoff X) :
    (2 : ℝ) ≤ (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1) := by
  have hX' : (10000000 : ℝ) ≤ X := le_trans (by norm_num) hX
  have h1 := half_exp_le_shell_ratio hX hm
  have h2 : (2 : ℝ) ≤ Real.exp (X / 2) := by
    linarith [Real.add_one_le_exp (X / 2)]
  linarith

/-- A prime of the `m`-th shell exceeds the *real* ratio `N/(m+1)` (not just
the `ℕ`-division floor): from `p ≥ ⌊N/(m+1)⌋ + 1` and
`N < (⌊N/(m+1)⌋ + 1)·(m+1)`.  Slightly stronger than the `− 1` slop the
paper carries. -/
theorem shell_ratio_lt_shell_prime {N m p : ℕ} (hp : p ∈ shellPrimes N m) :
    (N : ℝ) / ((m : ℝ) + 1) < (p : ℝ) := by
  obtain ⟨hlo, -, -⟩ := mem_shellPrimes.mp hp
  have h1 : N < p * (m + 1) := by
    have h4 : N % (m + 1) < m + 1 := Nat.mod_lt _ (Nat.succ_pos _)
    have h2 : N < (N / (m + 1) + 1) * (m + 1) := by
      calc N = (m + 1) * (N / (m + 1)) + N % (m + 1) := (Nat.div_add_mod _ _).symm
        _ < (m + 1) * (N / (m + 1)) + (m + 1) := Nat.add_lt_add_left h4 _
        _ = (N / (m + 1) + 1) * (m + 1) := by ring
    calc N < (N / (m + 1) + 1) * (m + 1) := h2
      _ ≤ p * (m + 1) := Nat.mul_le_mul hlo le_rfl
  have hcast : (N : ℝ) < (p : ℝ) * ((m : ℝ) + 1) := by exact_mod_cast h1
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
  exact hcast

/-- Every prime of a shell with index `m ≤ M` is at least `e^{X/2}`
(`X ≥ 10⁷`) — the size precondition for the collision estimates on the
shells of `prop:averaging-relation`. -/
theorem shell_prime_gt_half_exp {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m p : ℕ}
    (hm : m ≤ shellCutoff X) (hp : p ∈ shellPrimes ⌊Real.exp X⌋₊ m) :
    Real.exp (X / 2) ≤ (p : ℝ) :=
  le_of_lt (lt_of_le_of_lt (half_exp_le_shell_ratio hX hm)
    (shell_ratio_lt_shell_prime hp))

/-- Upper logarithmic bound on a shell prime: `log p ≤ X − log m` for
`p` in the `m`-th shell of `N = ⌊e^X⌋` (`m ≥ 1`); exact form of the paper's
`log p = X − log m + O(…)` upper half in eq. `prime-shell-sum`.  Holds for
every real `X` (no threshold needed: `p·m ≤ N ≤ e^X`). -/
theorem shell_prime_le_log {X : ℝ} {m p : ℕ} (hm : 1 ≤ m)
    (hp : p ∈ shellPrimes ⌊Real.exp X⌋₊ m) :
    Real.log p ≤ X - Real.log m := by
  obtain ⟨-, hple, hprime⟩ := mem_shellPrimes.mp hp
  have hpm : p * m ≤ ⌊Real.exp X⌋₊ := (Nat.le_div_iff_mul_le hm).mp hple
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcast : (p : ℝ) * (m : ℝ) ≤ Real.exp X := by
    calc (p : ℝ) * (m : ℝ) = ((p * m : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊Real.exp X⌋₊ : ℝ) := Nat.cast_le.mpr hpm
      _ ≤ Real.exp X := expFloor_le_exp X
  have hlog : Real.log ((p : ℝ) * (m : ℝ)) ≤ X := by
    rw [← Real.log_exp X]
    exact Real.log_le_log (by positivity) hcast
  rw [Real.log_mul hp0.ne' hm0.ne'] at hlog
  linarith

/-- Lower logarithmic bound on a shell prime: `X − log(m+1) − 2 ≤ log p` for
`p` in the `m`-th shell of `N = ⌊e^X⌋`, `X ≥ 10⁷`.  The slack `2` is
generous: the argument gives `X − log(m+1) − log 2` (from
`p > N/(m+1) ≥ e^X/(2(m+1))`), and `log 2 < 0.7`; we certify the paper's
`log p = X + O(log(m+1))` with the round constant `2`. -/
theorem shell_prime_log_ge {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m p : ℕ}
    (hp : p ∈ shellPrimes ⌊Real.exp X⌋₊ m) :
    X - Real.log ((m : ℝ) + 1) - 2 ≤ Real.log p := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hratio := shell_ratio_lt_shell_prime hp
  have hN : Real.exp X / 2 ≤ (⌊Real.exp X⌋₊ : ℝ) := exp_div_two_le_expFloor hX1
  have hlow : Real.exp X / 2 / ((m : ℝ) + 1) ≤ (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1) :=
    div_le_div₀ (Nat.cast_nonneg _) hN (by positivity) le_rfl
  have hlogp : Real.log (Real.exp X / 2 / ((m : ℝ) + 1)) ≤ Real.log p :=
    Real.log_le_log (by positivity) (le_of_lt (lt_of_le_of_lt hlow hratio))
  have hsplit : Real.log (Real.exp X / 2 / ((m : ℝ) + 1))
      = X - Real.log 2 - Real.log ((m : ℝ) + 1) :=
    log_exp_div_two_div (by positivity) X
  rw [hsplit] at hlogp
  linarith [log_two_le_one]

/-- **Shell-endpoint alignment** (`ℕ`-subtraction form): the size of the
`m`-th shell of `N` is exactly `π(N/m) − π(N/(m+1))` with `π = primePi`
evaluated at the *real* points `N/m` and `N/(m+1)` — the `ℕ`-division
endpoints of `shellPrimes` and the real endpoints of the paper's
`P_m = π(x_m) − π(y_m)` (eq. `prime-shell-sum`) agree because
`⌊(N:ℝ)/m⌋ = ⌊N/m⌋` (`Nat.floor_div_natCast`). -/
theorem shellPrimes_card_eq (N : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    (shellPrimes N m).card
      = primePi ((N : ℝ) / (m : ℝ)) - primePi ((N : ℝ) / ((m : ℝ) + 1)) := by
  have hfloor1 : primePi ((N : ℝ) / (m : ℝ))
      = ((Finset.range (N / m + 1)).filter Nat.Prime).card := by
    rw [primePi, Nat.floor_div_natCast, Nat.floor_natCast, Nat.primeCounting,
      Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hfloor2 : primePi ((N : ℝ) / ((m : ℝ) + 1))
      = ((Finset.range (N / (m + 1) + 1)).filter Nat.Prime).card := by
    have hcast : (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, primePi, Nat.floor_div_natCast, Nat.floor_natCast, Nat.primeCounting,
      Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hdivle : N / (m + 1) ≤ N / m := Nat.div_le_div_left (by omega) (by omega)
  have hsplit : (Finset.range (N / m + 1)).filter Nat.Prime
      = ((Finset.range (N / (m + 1) + 1)).filter Nat.Prime) ∪ shellPrimes N m := by
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
    simp only [shellPrimes, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hk1 hk2
    omega
  rw [hfloor1, hfloor2, hsplit, Finset.card_union_of_disjoint hdisj]
  omega

/-- **Shell-endpoint alignment** (real-subtraction form): the cast shell
count is the real difference of `primePi` values (well-defined since
`primePi` is monotone).  The form the FKS interval estimates
(`abs_primeInterval_sub_Li`, `primeInterval_lower/upper`) consume directly. -/
theorem shellPrimes_card_cast_eq (N : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ((shellPrimes N m).card : ℝ)
      = (primePi ((N : ℝ) / (m : ℝ)) : ℝ) - (primePi ((N : ℝ) / ((m : ℝ) + 1)) : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hdiv : (N : ℝ) / ((m : ℝ) + 1) ≤ (N : ℝ) / (m : ℝ) :=
    div_add_one_le_div (Nat.cast_nonneg N) hm0
  rw [shellPrimes_card_eq N hm, Nat.cast_sub (primePi_mono hdiv)]

/-! ## Explicit decay of the FKS endpoint errors over the shells -/

/-- The global maximum bound `s·e^{−0.0476·s} ≤ 8` for `s ≥ 0` (true max:
`1/(0.0476·e) < 7.73`, attained at `s = 1/0.0476`).  Unconditional — no
largeness assumption on `s` — via the tangent-line bound `e·x ≤ eˣ`. -/
theorem mul_exp_neg_le_eight {s : ℝ} (hs : 0 ≤ s) :
    s * Real.exp (-(0.0476 * s)) ≤ 8 := by
  have h1 := exp_one_mul_le_exp (0.0476 * s)
  have he := Real.exp_one_gt_d9
  have h4 : s ≤ 8 * Real.exp (0.0476 * s) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he.le) hs]
  calc s * Real.exp (-(0.0476 * s))
      ≤ 8 * Real.exp (0.0476 * s) * Real.exp (-(0.0476 * s)) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = 8 := by
        rw [mul_assoc, ← Real.exp_add,
          show (0.0476 * s + -(0.0476 * s) : ℝ) = 0 by ring, Real.exp_zero, mul_one]

/-- **Unconditional FKS-error decay**: `𝓔(t) ≤ 80·t·e^{−0.8·√(log t)}` for
every `t ≥ 0`.  The `√(log t)` factor of `fksError` is absorbed at the
*global* maximum of `s·e^{−0.0476 s}` (`mul_exp_neg_le_eight`), so — unlike
`fksError_le_of_log_ge`, whose threshold `log t ≥ 4·10⁶` is unusable at
`X₀ = 10⁷` where the shells only guarantee `log t ≥ X/2` — no largeness of
`t` is needed at all.  (`9.2211·8 = 73.77 ≤ 80`.) -/
theorem fksError_le_simple {t : ℝ} (ht : 0 ≤ t) :
    fksError t ≤ 80 * t * Real.exp (-0.8 * Real.sqrt (Real.log t)) := by
  have hs : (0 : ℝ) ≤ Real.sqrt (Real.log t) := Real.sqrt_nonneg _
  have hsplit : Real.exp (-0.8476 * Real.sqrt (Real.log t))
      = Real.exp (-(0.0476 * Real.sqrt (Real.log t)))
        * Real.exp (-0.8 * Real.sqrt (Real.log t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hkey := mul_exp_neg_le_eight hs
  have h9t : (0 : ℝ) ≤ 9.2211 * t := by linarith
  have hfk : fksError t = 9.2211 * t * Real.sqrt (Real.log t)
      * Real.exp (-0.8476 * Real.sqrt (Real.log t)) := rfl
  calc fksError t
      = 9.2211 * t
          * (Real.sqrt (Real.log t) * Real.exp (-(0.0476 * Real.sqrt (Real.log t))))
          * Real.exp (-0.8 * Real.sqrt (Real.log t)) := by
        rw [hfk, hsplit]; ring
    _ ≤ 9.2211 * t * 8 * Real.exp (-0.8 * Real.sqrt (Real.log t)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hkey h9t
    _ ≤ 80 * t * Real.exp (-0.8 * Real.sqrt (Real.log t)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        nlinarith

/-- FKS-error decay at points above `e^{X/2}` (`X ≥ 0`):
`𝓔(t) ≤ 80·t·e^{−0.4·√X}` whenever `e^{X/2} ≤ t` — the form in which the
shell endpoints `N/m, N/(m+1)` are fed into the `Σ|ε_m|` estimate
(`log t ≥ X/2` gives `√(log t) ≥ √X/2`, so `0.8·√(log t) ≥ 0.4·√X`). -/
theorem fksError_le_of_half_exp_le {X t : ℝ} (hX : 0 ≤ X) (ht : Real.exp (X / 2) ≤ t) :
    fksError t ≤ 80 * t * Real.exp (-0.4 * Real.sqrt X) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos _) ht
  have hlogt : X / 2 ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos (X / 2)) ht
    rwa [Real.log_exp] at h
  have hsqrt : Real.sqrt X / 2 ≤ Real.sqrt (Real.log t) := by
    have h2 : (Real.sqrt X / 2) ^ 2 ≤ Real.log t := by
      rw [div_pow, Real.sq_sqrt hX]
      norm_num
      linarith
    calc Real.sqrt X / 2 = Real.sqrt ((Real.sqrt X / 2) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Real.log t) := Real.sqrt_le_sqrt h2
  have hexp : Real.exp (-0.8 * Real.sqrt (Real.log t)) ≤ Real.exp (-0.4 * Real.sqrt X) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hsqrt]
  calc fksError t ≤ 80 * t * Real.exp (-0.8 * Real.sqrt (Real.log t)) :=
        fksError_le_simple ht0.le
    _ ≤ 80 * t * Real.exp (-0.4 * Real.sqrt X) :=
        mul_le_mul_of_nonneg_left hexp (by linarith : (0 : ℝ) ≤ 80 * t)

/-- **Total normalized FKS endpoint error over the shells**: the explicit
form of the paper's `Σ_{m ≤ X³} |ε_m| = o(X⁻²)` (eq. `prime-shell-sum`,
`prop:averaging-relation`), with `o(X⁻²)` certified as `≤ 1/X²` for
`X ≥ 10⁷`.  Route: every shell endpoint is `≥ e^{X/2}`
(`half_exp_le_shell_ratio`), so each error is `≤ 80·(N/m)·e^{−0.4√X}`
(`fksError_le_of_half_exp_le`); summing `Σ 1/m ≤ 1 + log M ≤ 3X`
(`sum_one_div_le_log`) and normalizing by `X/N` leaves
`480·X²·e^{−0.4√X} ≤ 1/X²` (`poly_le_exp_sqrt`). -/
theorem fks_shell_total_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    X / (⌊Real.exp X⌋₊ : ℝ) *
        ∑ m ∈ Finset.Icc 1 (shellCutoff X),
          (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))
      ≤ 1 / X ^ 2 := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hN1 : 1 ≤ ⌊Real.exp X⌋₊ := one_le_expFloor hX1
  have hNR : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) := by exact_mod_cast hN1
  have hE0 : (0 : ℝ) < Real.exp (-0.4 * Real.sqrt X) := Real.exp_pos _
  -- termwise bound: both endpoint errors of shell `m` are `≤ 80·(N/m)·e^{−0.4√X}`
  have hterm : ∀ m ∈ Finset.Icc 1 (shellCutoff X),
      fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
          + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
        ≤ 160 * ((⌊Real.exp X⌋₊ : ℝ) * ((1 : ℝ) / (m : ℝ)))
            * Real.exp (-0.4 * Real.sqrt X) := by
    intro m hm
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hr2 : Real.exp (X / 2) ≤ (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1) :=
      half_exp_le_shell_ratio hX hmM
    have hle : (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1) ≤ (⌊Real.exp X⌋₊ : ℝ) / (m : ℝ) :=
      div_add_one_le_div (Nat.cast_nonneg _) hm0
    have hr1 : Real.exp (X / 2) ≤ (⌊Real.exp X⌋₊ : ℝ) / (m : ℝ) := hr2.trans hle
    have h1 := fksError_le_of_half_exp_le hX0.le hr1
    have h2 := fksError_le_of_half_exp_le hX0.le hr2
    have h3 : 80 * ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)) * Real.exp (-0.4 * Real.sqrt X)
        ≤ 80 * ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ)) * Real.exp (-0.4 * Real.sqrt X) :=
      mul_le_mul_of_nonneg_right (by linarith) hE0.le
    calc fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
          + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
        ≤ 80 * ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ)) * Real.exp (-0.4 * Real.sqrt X)
            + 80 * ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ)) * Real.exp (-0.4 * Real.sqrt X) := by
          linarith
      _ = 160 * ((⌊Real.exp X⌋₊ : ℝ) * ((1 : ℝ) / (m : ℝ)))
            * Real.exp (-0.4 * Real.sqrt X) := by
          rw [show (⌊Real.exp X⌋₊ : ℝ) / (m : ℝ)
            = (⌊Real.exp X⌋₊ : ℝ) * ((1 : ℝ) / (m : ℝ)) by ring]
          ring
  -- sum the termwise bounds and pull out the constants
  have hsum1 : ∑ m ∈ Finset.Icc 1 (shellCutoff X),
      (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
        + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))
        ≤ 160 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X)
            * ∑ m ∈ Finset.Icc 1 (shellCutoff X), (1 : ℝ) / (m : ℝ) := by
    calc ∑ m ∈ Finset.Icc 1 (shellCutoff X),
        (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
          + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))
        ≤ ∑ m ∈ Finset.Icc 1 (shellCutoff X),
            160 * ((⌊Real.exp X⌋₊ : ℝ) * ((1 : ℝ) / (m : ℝ)))
              * Real.exp (-0.4 * Real.sqrt X) := Finset.sum_le_sum hterm
      _ = 160 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X)
            * ∑ m ∈ Finset.Icc 1 (shellCutoff X), (1 : ℝ) / (m : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
  -- `Σ 1/m ≤ 1 + log M ≤ 3X`
  have hlogM : 1 + Real.log ((shellCutoff X : ℕ) : ℝ) ≤ 3 * X := by
    have hM1 : 1 ≤ shellCutoff X := one_le_shellCutoff hX1
    have hM0 : (0 : ℝ) < ((shellCutoff X : ℕ) : ℝ) := by exact_mod_cast hM1
    have h1 : Real.log ((shellCutoff X : ℕ) : ℝ) ≤ Real.log (X ^ 3) :=
      Real.log_le_log hM0 (shellCutoff_cast_le hX0.le)
    rw [Real.log_pow] at h1
    push_cast at h1
    have h2 : Real.log X ≤ X - 1 := Real.log_le_sub_one_of_pos hX0
    linarith
  have hpos160 : (0 : ℝ) ≤ 160 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X) := by
    positivity
  have hsum2 : ∑ m ∈ Finset.Icc 1 (shellCutoff X),
      (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
        + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))
        ≤ 160 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X) * (3 * X) := by
    calc ∑ m ∈ Finset.Icc 1 (shellCutoff X),
        (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
          + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))
        ≤ 160 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X)
            * ∑ m ∈ Finset.Icc 1 (shellCutoff X), (1 : ℝ) / (m : ℝ) := hsum1
      _ ≤ 160 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X)
            * (1 + Real.log ((shellCutoff X : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_one_div_le_log (shellCutoff X)) hpos160
      _ ≤ 160 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X) * (3 * X) :=
          mul_le_mul_of_nonneg_left hlogM hpos160
  -- normalize by `X/N` and close with `480·X⁴ ≤ e^{0.4√X}`
  have hXNnn : (0 : ℝ) ≤ X / (⌊Real.exp X⌋₊ : ℝ) := by positivity
  have hEq : X / (⌊Real.exp X⌋₊ : ℝ)
      * (160 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X) * (3 * X))
      = 480 * X ^ 2 * Real.exp (-0.4 * Real.sqrt X) := by
    field_simp
    ring
  have hdom := poly_le_exp_sqrt hX
  have hfin : 480 * X ^ 2 * Real.exp (-0.4 * Real.sqrt X) ≤ 1 / X ^ 2 := by
    rw [le_div_iff₀ (pow_pos hX0 2)]
    have hprodE : Real.exp (-0.4 * Real.sqrt X) * Real.exp (0.4 * Real.sqrt X) = 1 := by
      rw [← Real.exp_add, show (-0.4 * Real.sqrt X + 0.4 * Real.sqrt X : ℝ) = 0 by ring,
        Real.exp_zero]
    nlinarith [mul_le_mul_of_nonneg_right hdom hE0.le, hprodE]
  calc X / (⌊Real.exp X⌋₊ : ℝ) *
      ∑ m ∈ Finset.Icc 1 (shellCutoff X),
        (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
          + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))
      ≤ X / (⌊Real.exp X⌋₊ : ℝ)
          * (160 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X) * (3 * X)) :=
        mul_le_mul_of_nonneg_left hsum2 hXNnn
    _ = 480 * X ^ 2 * Real.exp (-0.4 * Real.sqrt X) := hEq
    _ ≤ 1 / X ^ 2 := hfin

/-! ## The smooth-core term is harmless after normalization -/

/-- **Normalized smooth-core bound**: the paper's "The core term is harmless
after multiplication by `X/N`" (`prop:averaging-relation`, after
eq. `shell-sum`), made explicit: for `X ≥ 10⁷` the entire upper-bound error
of `g_shell_decomposition` — the fibre factor `log(H_N + 1)` plus the
smooth-part factor `log 𝔇_Q` — is at most `3/X²` after multiplication by
`X/N`.  The `3` decomposes as `2.8` from `ϑ(Q) ≤ (log 4)·Q ≤ 1.4·e^X/X³`
(with `X/N ≤ 2X·e^{−X}`) plus `0.2` covering both the fibre term
(`log(H+1) ≤ 1 + X`) and the higher prime-power layers (`√N·log N ≤
e^{X/2}·X`), which are exponentially negligible. -/
theorem core_normalized_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    X / (⌊Real.exp X⌋₊ : ℝ) *
        (Real.log ((harmonicSum ⌊Real.exp X⌋₊ : ℝ) + 1)
          + Real.log (smoothPart (⌊Real.exp X⌋₊ / (shellCutoff X + 1)) ⌊Real.exp X⌋₊))
      ≤ 3 / X ^ 2 := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hN1 : 1 ≤ ⌊Real.exp X⌋₊ := one_le_expFloor hX1
  have hNle : (⌊Real.exp X⌋₊ : ℝ) ≤ Real.exp X := expFloor_le_exp X
  have hQ2 : 2 ≤ ⌊Real.exp X⌋₊ / (shellCutoff X + 1) := two_le_Q hX
  have hQN : ⌊Real.exp X⌋₊ / (shellCutoff X + 1) ≤ ⌊Real.exp X⌋₊ := Q_le_N X
  -- fibre factor: `log(H_N + 1) ≤ H_N ≤ 1 + log N ≤ 1 + X`
  have hH0 : (0 : ℝ) ≤ ((harmonicSum ⌊Real.exp X⌋₊ : ℚ) : ℝ) := by
    exact_mod_cast harmonicSum_nonneg ⌊Real.exp X⌋₊
  have hHle := harmonicSum_le_one_add_log ⌊Real.exp X⌋₊
  have hlogN : Real.log ⌊Real.exp X⌋₊ ≤ X := log_expFloor_le hX1
  have hL1 : Real.log ((harmonicSum ⌊Real.exp X⌋₊ : ℝ) + 1) ≤ 1 + X := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < ((harmonicSum ⌊Real.exp X⌋₊ : ℚ) : ℝ) + 1 by linarith)
    linarith
  -- smooth-part factor: `log 𝔇_Q ≤ ϑ(Q) + √N·log N ≤ 1.4·e^X/X³ + e^{X/2}·X`
  have hsmooth := log_smoothPart_le hQ2 hQN
  have htheta : chebyshevTheta ((⌊Real.exp X⌋₊ / (shellCutoff X + 1) : ℕ) : ℝ)
      ≤ 1.4 * (Real.exp X / X ^ 3) := by
    have h1 := chebyshevTheta_le_log_four_mul
      (x := ((⌊Real.exp X⌋₊ / (shellCutoff X + 1) : ℕ) : ℝ)) (Nat.cast_nonneg _)
    have hlog4 : Real.log 4 ≤ 1.4 := log_four_le
    have h3 := Q_real_upper hX
    have hQ0 : (0 : ℝ) ≤ ((⌊Real.exp X⌋₊ / (shellCutoff X + 1) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog4) hQ0]
  have hsqrtN : Real.sqrt (⌊Real.exp X⌋₊ : ℝ) * Real.log (⌊Real.exp X⌋₊ : ℝ)
      ≤ Real.exp (X / 2) * X := by
    have h1 : Real.sqrt (⌊Real.exp X⌋₊ : ℝ) ≤ Real.exp (X / 2) := by
      rw [Real.exp_half]
      exact Real.sqrt_le_sqrt hNle
    have h2 : (0 : ℝ) ≤ Real.log (⌊Real.exp X⌋₊ : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN1)
    exact mul_le_mul h1 hlogN h2 (Real.exp_pos _).le
  have hL2 : Real.log (smoothPart (⌊Real.exp X⌋₊ / (shellCutoff X + 1)) ⌊Real.exp X⌋₊)
      ≤ 1.4 * (Real.exp X / X ^ 3) + Real.exp (X / 2) * X :=
    hsmooth.trans (add_le_add htheta hsqrtN)
  have hsum : Real.log ((harmonicSum ⌊Real.exp X⌋₊ : ℝ) + 1)
      + Real.log (smoothPart (⌊Real.exp X⌋₊ / (shellCutoff X + 1)) ⌊Real.exp X⌋₊)
      ≤ (1 + X) + (1.4 * (Real.exp X / X ^ 3) + Real.exp (X / 2) * X) :=
    add_le_add hL1 hL2
  -- normalize: `X/N ≤ 2X/e^X`, then everything closes against `e^{X/2} ≥ 30X⁴`
  have hXN : X / (⌊Real.exp X⌋₊ : ℝ) ≤ 2 * X / Real.exp X := div_expFloor_le hX1
  have hXNnn : (0 : ℝ) ≤ X / (⌊Real.exp X⌋₊ : ℝ) := by positivity
  have hB0 : (0 : ℝ) ≤ (1 + X) + (1.4 * (Real.exp X / X ^ 3) + Real.exp (X / 2) * X) := by
    have hd : (0 : ℝ) ≤ Real.exp X / X ^ 3 :=
      div_nonneg (Real.exp_pos X).le (pow_pos hX0 3).le
    have hw : (0 : ℝ) ≤ Real.exp (X / 2) * X := mul_nonneg (Real.exp_pos _).le hX0.le
    linarith
  have hfinal : 2 * X / Real.exp X
      * ((1 + X) + (1.4 * (Real.exp X / X ^ 3) + Real.exp (X / 2) * X)) ≤ 3 / X ^ 2 := by
    have hW := poly_le_exp_half hX
    have hW0 : (0 : ℝ) < Real.exp (X / 2) := Real.exp_pos _
    have hEW : Real.exp X = Real.exp (X / 2) * Real.exp (X / 2) := exp_eq_exp_half_mul X
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (Real.exp_pos X) (pow_pos hX0 2)]
    have hexpand : 2 * X * ((1 + X) + (1.4 * (Real.exp X / X ^ 3) + Real.exp (X / 2) * X))
        * X ^ 2
        = 2 * X ^ 3 * (1 + X) + 2.8 * Real.exp X + 2 * Real.exp (X / 2) * X ^ 4 := by
      field_simp
      ring
    rw [hexpand, hEW]
    have p1 : (0 : ℝ) ≤ (Real.exp (X / 2) - 30 * X ^ 4) * Real.exp (X / 2) :=
      mul_nonneg (by linarith) hW0.le
    have p2 : (0 : ℝ) ≤ (Real.exp (X / 2) - 30 * X ^ 4) * X ^ 4 :=
      mul_nonneg (by linarith) (by positivity)
    have q1 : (1 : ℝ) ≤ X ^ 4 := one_le_pow₀ hX1
    have q2 : X ^ 3 ≤ X ^ 4 := by
      nlinarith [mul_nonneg (pow_nonneg hX0.le 3) (sub_nonneg.mpr hX1)]
    have q3 : X ^ 4 ≤ X ^ 8 := by
      nlinarith [mul_nonneg (pow_nonneg hX0.le 4) (sub_nonneg.mpr q1)]
    nlinarith [p1, p2, q1, q2, q3, pow_nonneg hX0.le 3]
  calc X / (⌊Real.exp X⌋₊ : ℝ) *
      (Real.log ((harmonicSum ⌊Real.exp X⌋₊ : ℝ) + 1)
        + Real.log (smoothPart (⌊Real.exp X⌋₊ / (shellCutoff X + 1)) ⌊Real.exp X⌋₊))
      ≤ X / (⌊Real.exp X⌋₊ : ℝ)
          * ((1 + X) + (1.4 * (Real.exp X / X ^ 3) + Real.exp (X / 2) * X)) :=
        mul_le_mul_of_nonneg_left hsum hXNnn
    _ ≤ 2 * X / Real.exp X
          * ((1 + X) + (1.4 * (Real.exp X / X ^ 3) + Real.exp (X / 2) * X)) :=
        mul_le_mul_of_nonneg_right hXN hB0
    _ ≤ 3 / X ^ 2 := hfinal

end Erdos320
