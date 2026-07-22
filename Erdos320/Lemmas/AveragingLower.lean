import Erdos320.Lemmas.AveragingSetup
import Erdos320.Lemmas.CollisionLower
import Erdos320.Lemmas.BSlopes

/-!
# Lower half of the averaging relation (`prop:averaging-relation`)

The manuscript's Proposition "Asymptotic averaging relation" states
`|𝓡(X)| ≪ (log X)²/X` for `𝓡(X) := F(e^X) − 𝓑(X)`.  This file proves the
**lower** half — the reverse of eq. `shell-upper` — in fully explicit form:

```
𝓑(X) − F(e^X) ≤ 4·(log X)²/X        for X ≥ 10⁷,
```

equivalently `−4·(log X)²/X ≤ 𝓡(X)` (`neg_le_averagingError`).

Following the paper, with `N = ⌊e^X⌋`, `M = ⌊X³⌋`:

* `𝓑(X)` is cut at the shell cutoff: the tail `Σ_{m>M} min(g(m),X)/(m(m+1))
  ≤ X/(M+1) ≤ 1/X²` (`avgLow_B_le_capped_sum`; paper: "Also
  `Σ_{m>M} … ≤ X/(M+1)`").
* Each shell `1 ≤ m ≤ M` is bounded below through the average collision bound
  (eq. `collision-sum`): the collision multiplicity is realized by the
  explicit integer `avgLow_bChoice X m = ⌊2·W_m/X⌋ + 1` with
  `W_m = (log 4)m + √m·log m + log(1+log m)` dominating `log(L_m·H_m)`
  (paper: `b_m ≤ log(L_mH_m)/log(N/(m+1)) ≪ m/X`).
* The bracket of eq. `collision-sum` is transported to the capped value
  `a_m = min(g(m), X)` (`avgLow_capped_deficit_transfer`; paper: "The bracket
  in eq. `collision-sum` is at least `a_m − ℓ_m`").
* The FKS shell-count estimates (`primeInterval_lower/upper`) convert the
  prime count `P_m` into the weight `1/(m(m+1))`, the lower count multiplying
  the positive capped term and the upper count multiplying the loss `ℓ_m`
  (paper: "The lower count is applied to the positive first term and the
  upper count to the loss").
* The loss is split at `m ≈ X/(4 log 2)` (paper: "If `m ≤ X/(4log2)`, the
  logarithmic loss … is `O(e^{−X/2})`.  If `X/(4log2) < m ≤ X²` … the loss
  from the capped value is `O(log(m+1))`"):
  - **small-`m` regime** (`avgLow_deficit_small`): `S(m) ≤ 2^m ≤ e^{X/4}`
    makes the loss per shell at most `4·e^{X/4}`, exponentially negligible
    after normalization by `X/N ≤ 2X·e^{−X}`;
  - **large-`m` regime** (`avgLow_deficit_le_large`): `P_m/b_m ≥
    N/(18(m+1)³)` gives `ℓ_m ≤ 3·log(m+1) + 5`, and
    `Σ_{m>X/(4log2)} (6log(m+1)+10)/(m(m+1)) ≤ 3(log X)²/X` by the integral
    tail bounds of `LogSumBounds`.

**Explicit-constant ledger** (each is *weaker-side* slack, never a
strengthening; total budget `4·(log X)²/X`):
`1/X²` (𝓑-tail) + `2/X` (two copies of the FKS error total
`fks_shell_total_le`, one per count application) + `1/X²` (small-`m` losses)
+ `3(log X)²/X` (large-`m` losses) + `1/X²` (normalization bridge
`F(e^X) ↔ (X/N)g(N)`); at `X ≥ 10⁷` one has `log X ≥ 16`, so everything
below `(log X)²/X` is absorbed into the fourth `(log X)²/X`.
-/

namespace Erdos320

/-! ## Elementary numeric groundwork -/

/-- `640·X⁷ ≤ e^{0.4·√X}` for `X ≥ 10⁷` (via `e^{0.4s} ≥ (0.4s)²⁸/28!` at
`s = √X`, so it suffices that `X⁷ ≥ 640·28!/0.4²⁸ ≈ 2.71·10⁴³`, while
`X⁷ ≥ 10⁴⁹`).  This dominates the FKS endpoint errors by the *smallest*
shell weight `1/(m(m+1)) ≥ 1/(2X⁶)`, which is how the paper's
`P_m ≍ N/(Xm(m+1))` (proof of `prop:averaging-relation`) is certified for
every shell `m ≤ X³` at once. -/
theorem avgLow_poly7_le_exp_sqrt {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    640 * X ^ 7 ≤ Real.exp (0.4 * Real.sqrt X) := by
  have hX0 : (0 : ℝ) ≤ X := le_trans (by norm_num) hX
  have h := pow_div_factorial_le_exp
    (by positivity : (0 : ℝ) ≤ 0.4 * Real.sqrt X) 28
  have hfac : ((Nat.factorial 28 : ℕ) : ℝ) = 304888344611713860501504000000 := by
    norm_num [Nat.factorial]
  rw [hfac] at h
  have h28 : Real.sqrt X ^ 28 = X ^ 14 := by
    rw [show (28 : ℕ) = 2 * 14 from rfl, pow_mul, Real.sq_sqrt hX0]
  have hpow : (0.4 * Real.sqrt X) ^ 28 = 0.4 ^ 28 * X ^ 14 := by
    rw [mul_pow, h28]
  have hX7 : (10 : ℝ) ^ 49 ≤ X ^ 7 := by
    calc (10 : ℝ) ^ 49 = ((10 : ℝ) ^ 7) ^ 7 := by norm_num
      _ ≤ X ^ 7 := pow_le_pow_left₀ (by norm_num) hX 7
  have h7nn : (0 : ℝ) ≤ X ^ 7 := by positivity
  have hkey : 640 * X ^ 7
      ≤ (0.4 * Real.sqrt X) ^ 28 / 304888344611713860501504000000 := by
    rw [hpow, le_div_iff₀ (by norm_num : (0 : ℝ) < 304888344611713860501504000000)]
    have hc : (0.4 : ℝ) ^ 28 = 268435456 / 37252902984619140625 := by norm_num
    rw [hc, show X ^ 14 = X ^ 7 * X ^ 7 by ring]
    nlinarith [mul_le_mul_of_nonneg_left hX7 h7nn]
  linarith

/-- `16 ≤ log X` for `X ≥ 10⁷` (since `e¹⁶ < 8.9·10⁶ < 10⁷`).  The numeric
anchor that absorbs all sub-leading `1/X`-type errors into `(log X)²/X`. -/
theorem avgLow_sixteen_le_log {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    (16 : ℝ) ≤ Real.log X :=
  sixteen_le_log hX

/-- `log X ≤ √X` for `X ≥ 1` (via `e·log √X ≤ √X` and `e ≥ 2`). -/
theorem avgLow_log_le_sqrt {X : ℝ} (hX : 1 ≤ X) : Real.log X ≤ Real.sqrt X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt X := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hX
  have hs0 : (0 : ℝ) < Real.sqrt X := by linarith
  have hlog : Real.log X = 2 * Real.log (Real.sqrt X) := by
    rw [Real.log_sqrt hX0.le]; ring
  have h1 : Real.exp 1 * Real.log (Real.sqrt X) ≤ Real.sqrt X := by
    calc Real.exp 1 * Real.log (Real.sqrt X)
        ≤ Real.exp (Real.log (Real.sqrt X)) := exp_one_mul_le_exp _
      _ = Real.sqrt X := Real.exp_log hs0
  have hlognn : 0 ≤ Real.log (Real.sqrt X) := Real.log_nonneg hs1
  nlinarith [Real.exp_one_gt_d9]

/-- `√X ≤ X/3000` for `X ≥ 10⁷` (since `√X ≥ 3000`). -/
theorem avgLow_sqrt_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    Real.sqrt X ≤ X / 3000 := by
  have hX0 : (0 : ℝ) ≤ X := le_trans (by norm_num) hX
  have h3000 : (3000 : ℝ) ≤ Real.sqrt X := by
    rw [show (3000 : ℝ) = Real.sqrt (3000 ^ 2) by
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3000)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hmul : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3000)]
  nlinarith [Real.sqrt_nonneg X]

/-- The large-`m` per-shell loss bound `3·log(m+1) + 5` never exceeds the cap
`X` itself, for shells `m ≤ M = ⌊X³⌋` (`X ≥ 10⁷`).  This is what lets the
FKS-error portion of the loss be absorbed by `X · (FKS total)`. -/
theorem avgLow_deficit_bound_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hmM : m ≤ shellCutoff X) :
    3 * Real.log ((m : ℝ) + 1) + 5 ≤ X := by
  have hX' : (10000000 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hlog := shell_log_add_one_le hX1 hmM
  have hls := avgLow_log_le_sqrt hX1
  have hsd := avgLow_sqrt_le hX
  linarith [log_two_le_one]

/-! ## The explicit collision multiplicity `b_m` -/

/-- The explicit numerator-span majorant `W_m = (log 4)·m + √m·log m +
log(1 + log m)` of `log(L_m·H_m)` (`log_lcm_mul_harmonicSum_le`); the
quantity the paper's `b_m ≪ m/X` (proof of eq. `collision-sum`) is measured
against. -/
noncomputable def avgLow_spanBound (m : ℕ) : ℝ :=
  Real.log 4 * m + Real.sqrt m * Real.log m + Real.log (1 + Real.log m)

theorem avgLow_spanBound_nonneg {m : ℕ} (hm : 1 ≤ m) : 0 ≤ avgLow_spanBound m := by
  unfold avgLow_spanBound
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have h3 : 0 ≤ Real.log (1 + Real.log (m : ℝ)) := Real.log_nonneg (by linarith)
  have hs : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have h1 : 0 ≤ Real.log 4 * (m : ℝ) := mul_nonneg h4 (by linarith)
  have h2 : 0 ≤ Real.sqrt (m : ℝ) * Real.log (m : ℝ) := mul_nonneg hs hlm
  linarith

/-- `W_m ≤ 3m` for `m ≥ 1`: `log 4 ≤ 1.4`, `√m·log m ≤ 2m/e ≤ 0.75m`, and
`log(1+log m) ≤ log(2m) ≤ 2m/e ≤ 0.75m` (tangent-line bound `e·y ≤ e^y`). -/
theorem avgLow_spanBound_le {m : ℕ} (hm : 1 ≤ m) : avgLow_spanBound m ≤ 3 * m := by
  unfold avgLow_spanBound
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hm1
  have hs0 : (0 : ℝ) < Real.sqrt (m : ℝ) := by linarith
  have hss : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
    Real.mul_self_sqrt hm0.le
  have he := Real.exp_one_gt_d9
  have hlog4 : Real.log 4 ≤ 1.4 := log_four_le
  have hlogsq : Real.log (m : ℝ) = 2 * Real.log (Real.sqrt (m : ℝ)) := by
    rw [Real.log_sqrt hm0.le]; ring
  have hLs : Real.exp 1 * Real.log (Real.sqrt (m : ℝ)) ≤ Real.sqrt (m : ℝ) := by
    calc Real.exp 1 * Real.log (Real.sqrt (m : ℝ))
        ≤ Real.exp (Real.log (Real.sqrt (m : ℝ))) := exp_one_mul_le_exp _
      _ = Real.sqrt (m : ℝ) := Real.exp_log hs0
  have hLsnn : 0 ≤ Real.log (Real.sqrt (m : ℝ)) := Real.log_nonneg hs1
  have h2 : Real.sqrt (m : ℝ) * Real.log (m : ℝ) ≤ 0.75 * (m : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hLs hs0.le,
      mul_nonneg hs0.le hLsnn]
  have hlmnn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have h3 : Real.log (1 + Real.log (m : ℝ)) ≤ 0.75 * (m : ℝ) := by
    have hlm_le : Real.log (m : ℝ) ≤ (m : ℝ) - 1 := Real.log_le_sub_one_of_pos hm0
    have hmono : Real.log (1 + Real.log (m : ℝ)) ≤ Real.log (2 * (m : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    have hL2 : Real.exp 1 * Real.log (2 * (m : ℝ)) ≤ 2 * (m : ℝ) := by
      calc Real.exp 1 * Real.log (2 * (m : ℝ))
          ≤ Real.exp (Real.log (2 * (m : ℝ))) := exp_one_mul_le_exp _
        _ = 2 * (m : ℝ) := Real.exp_log (by linarith)
    have hlog2m_nn : 0 ≤ Real.log (2 * (m : ℝ)) := Real.log_nonneg (by linarith)
    nlinarith
  have h1 : Real.log 4 * (m : ℝ) ≤ 1.4 * (m : ℝ) := by nlinarith
  linarith

/-- The explicit collision multiplicity `b_m := ⌊2·W_m/X⌋ + 1`, an integer
dominating the paper's `log(L_m·H_m)/log(N/(m+1))` (proof of
eq. `collision-sum`) since the shell ratio is at least `e^{X/2}`. -/
noncomputable def avgLow_bChoice (X : ℝ) (m : ℕ) : ℕ :=
  ⌊2 * avgLow_spanBound m / X⌋₊ + 1

theorem avgLow_one_le_bChoice (X : ℝ) (m : ℕ) : 1 ≤ avgLow_bChoice X m :=
  Nat.le_add_left 1 _

/-- The multiplicity is genuinely of size `O(m/X)`, made explicit as
`b_m ≤ 6m/X + 1` (paper: `b_m ≪ m/X`). -/
theorem avgLow_bChoice_le {X : ℝ} (hX0 : 0 < X) {m : ℕ} (hm : 1 ≤ m) :
    (avgLow_bChoice X m : ℝ) ≤ 6 * m / X + 1 := by
  unfold avgLow_bChoice
  push_cast
  have hW0 := avgLow_spanBound_nonneg hm
  have h1 : (⌊2 * avgLow_spanBound m / X⌋₊ : ℝ) ≤ 2 * avgLow_spanBound m / X :=
    Nat.floor_le (by positivity)
  have h2 : 2 * avgLow_spanBound m / X ≤ 6 * m / X := by
    rw [div_le_div_iff₀ hX0 hX0]
    nlinarith [mul_le_mul_of_nonneg_right (avgLow_spanBound_le hm) hX0.le]
  linarith

/-- `avgLow_bChoice` satisfies the hypothesis `hb` of
`shell_collision_lower`: it dominates `log(L_m·H_m)/log(N/(m+1))`.  Uses
`log(L_m·H_m) ≤ W_m` (`log_lcm_mul_harmonicSum_le` with the harmonic bound
`H_m ≤ 1 + log m`) and `log(N/(m+1)) ≥ X/2` (`half_exp_le_shell_ratio`). -/
theorem avgLow_bChoice_spec {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X) :
    Real.log ((((Finset.Icc 1 m).lcm id : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ))
        / Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
      ≤ (avgLow_bChoice X m : ℝ) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX
  have hnum_le : Real.log ((((Finset.Icc 1 m).lcm id : ℕ) : ℝ)
      * ((harmonicSum m : ℚ) : ℝ)) ≤ avgLow_spanBound m := by
    have h := log_lcm_mul_harmonicSum_le hm1 (harmonicSum_le_one_add_log m)
    unfold avgLow_spanBound
    linarith
  have hnum_nn : 0 ≤ Real.log ((((Finset.Icc 1 m).lcm id : ℕ) : ℝ)
      * ((harmonicSum m : ℚ) : ℝ)) := by
    apply Real.log_nonneg
    have hL : (1 : ℝ) ≤ (((Finset.Icc 1 m).lcm id : ℕ) : ℝ) := by
      exact_mod_cast lcm_Icc_pos m
    have hH : (1 : ℝ) ≤ ((harmonicSum m : ℚ) : ℝ) := by
      exact_mod_cast one_le_harmonicSum hm1
    nlinarith
  have hden : X / 2 ≤ Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)) := by
    calc X / 2 = Real.log (Real.exp (X / 2)) := (Real.log_exp _).symm
      _ ≤ Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)) :=
          Real.log_le_log (Real.exp_pos _) (half_exp_le_shell_ratio hX hmM)
  have hW0 : 0 ≤ avgLow_spanBound m := hnum_nn.trans hnum_le
  have hdiv : Real.log ((((Finset.Icc 1 m).lcm id : ℕ) : ℝ)
        * ((harmonicSum m : ℚ) : ℝ))
        / Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
      ≤ avgLow_spanBound m / (X / 2) :=
    div_le_div₀ hW0 hnum_le (by positivity) hden
  have heq : avgLow_spanBound m / (X / 2) = 2 * avgLow_spanBound m / X := by
    field_simp
  have hfl : 2 * avgLow_spanBound m / X
      < (⌊2 * avgLow_spanBound m / X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  unfold avgLow_bChoice
  push_cast
  rw [heq] at hdiv
  linarith

/-! ## Shell endpoint geometry -/

/-- `2 ≤ N/(m+1)` for shells `m ≤ M` at `X ≥ 10⁷` (the `2 ≤ a` hypothesis of
the FKS interval estimates). -/
theorem avgLow_two_le_shell_lo {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hmM : m ≤ shellCutoff X) :
    (2 : ℝ) ≤ (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1) :=
  two_le_shell_ratio hX hmM

/-- The lower shell endpoint is below the upper one: `N/(m+1) ≤ N/m`. -/
theorem avgLow_shell_lo_le_hi {N m : ℕ} (hm : 1 ≤ m) :
    (N : ℝ) / ((m : ℝ) + 1) ≤ (N : ℝ) / (m : ℝ) :=
  div_add_one_le_div (Nat.cast_nonneg N) (by exact_mod_cast hm)

/-- The shell length identity `N/m − N/(m+1) = N/(m(m+1))` — the paper's
`x_m − y_m = N/[m(m+1)]` (proof of `prop:averaging-relation`). -/
theorem avgLow_shell_gap {N m : ℕ} (hm : 1 ≤ m) :
    (N : ℝ) / (m : ℝ) - (N : ℝ) / ((m : ℝ) + 1)
      = (N : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) :=
  shell_endpoint_gap (by exact_mod_cast hm)

/-- `log(N/m) ≤ X` — the upper shell endpoint stays below `e^X`. -/
theorem avgLow_log_hi_le {X : ℝ} (hX1 : 1 ≤ X) {m : ℕ} (hm : 1 ≤ m) :
    Real.log ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ)) ≤ X := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) := by
    exact_mod_cast one_le_expFloor hX1
  have h1 : (⌊Real.exp X⌋₊ : ℝ) / (m : ℝ) ≤ Real.exp X := by
    calc (⌊Real.exp X⌋₊ : ℝ) / (m : ℝ) ≤ (⌊Real.exp X⌋₊ : ℝ) :=
          div_le_self hN0.le hm1
      _ ≤ Real.exp X := expFloor_le_exp X
  calc Real.log ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
      ≤ Real.log (Real.exp X) := Real.log_le_log (div_pos hN0 hm0) h1
    _ = X := Real.log_exp X

/-- `0 < log(N/m)` for shells `m ≤ M` at `X ≥ 10⁷`. -/
theorem avgLow_log_hi_pos {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X) :
    0 < Real.log ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ)) := by
  apply Real.log_pos
  have h1 := one_lt_shell_ratio hX hmM
  have h2 := avgLow_shell_lo_le_hi (N := ⌊Real.exp X⌋₊) hm1
  linarith

/-- `X/2 ≤ log(N/(m+1))` for shells `m ≤ M` at `X ≥ 10⁷`. -/
theorem avgLow_log_lo_ge {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hmM : m ≤ shellCutoff X) :
    X / 2 ≤ Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)) := by
  calc X / 2 = Real.log (Real.exp (X / 2)) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos _) (half_exp_le_shell_ratio hX hmM)

/-! ## FKS endpoint errors are dominated by the shell weight -/

/-- **Per-shell FKS-error domination**: for every shell `1 ≤ m ≤ M` at
`X ≥ 10⁷`, the two FKS endpoint errors together are at most *half* of the
normalized main term `N/(m(m+1))/X`, i.e. `≤ N/(m(m+1))/(2X)`.  This is the
paper's `P_m ≍ N/(Xm(m+1))` (proof of `prop:averaging-relation`) in explicit
per-shell form, via `𝓔(t) ≤ 80·t·e^{−0.4√X}` above `e^{X/2}` and
`640·X⁷ ≤ e^{0.4√X}`. -/
theorem avgLow_fks_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X) :
    fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
        + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
      ≤ (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / (2 * X) := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hN1 : (1 : ℝ) ≤ (⌊Real.exp X⌋₊ : ℝ) := by
    exact_mod_cast one_le_expFloor hX1
  have hN0 : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) := by linarith
  have hlo := half_exp_le_shell_ratio hX hmM
  have hhi : Real.exp (X / 2) ≤ (⌊Real.exp X⌋₊ : ℝ) / (m : ℝ) :=
    hlo.trans (avgLow_shell_lo_le_hi hm1)
  have hE0 : (0 : ℝ) < Real.exp (-0.4 * Real.sqrt X) := Real.exp_pos _
  have hhiN : (⌊Real.exp X⌋₊ : ℝ) / (m : ℝ) ≤ (⌊Real.exp X⌋₊ : ℝ) :=
    div_le_self hN0.le hm1'
  have hloN : (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1) ≤ (⌊Real.exp X⌋₊ : ℝ) :=
    div_le_self hN0.le (by linarith)
  have h1 : fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
      ≤ 80 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X) := by
    calc fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
        ≤ 80 * ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ)) * Real.exp (-0.4 * Real.sqrt X) :=
          fksError_le_of_half_exp_le hX0.le hhi
      _ ≤ 80 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X) := by
          apply mul_le_mul_of_nonneg_right _ hE0.le
          linarith
  have h2 : fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
      ≤ 80 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X) := by
    calc fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
        ≤ 80 * ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
            * Real.exp (-0.4 * Real.sqrt X) :=
          fksError_le_of_half_exp_le hX0.le hlo
      _ ≤ 80 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X) := by
          apply mul_le_mul_of_nonneg_right _ hE0.le
          linarith
  have hmm : (m : ℝ) * ((m : ℝ) + 1) ≤ 2 * X ^ 6 := by
    have hmc : (m : ℝ) ≤ X ^ 3 :=
      le_trans (Nat.cast_le.mpr hmM) (shellCutoff_cast_le hX0.le)
    have hX3 : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ hX1
    nlinarith
  have h640 := avgLow_poly7_le_exp_sqrt hX
  have hEE : Real.exp (-0.4 * Real.sqrt X) * Real.exp (0.4 * Real.sqrt X) = 1 := by
    rw [← Real.exp_add,
      show -0.4 * Real.sqrt X + 0.4 * Real.sqrt X = 0 by ring, Real.exp_zero]
  have hkey : 160 * Real.exp (-0.4 * Real.sqrt X)
      * ((m : ℝ) * ((m : ℝ) + 1)) * (2 * X) ≤ 1 := by
    have hstep : 160 * ((m : ℝ) * ((m : ℝ) + 1)) * (2 * X) ≤ 640 * X ^ 7 := by
      nlinarith [mul_le_mul_of_nonneg_left hmm
        (by linarith : (0 : ℝ) ≤ 320 * X)]
    calc 160 * Real.exp (-0.4 * Real.sqrt X) * ((m : ℝ) * ((m : ℝ) + 1)) * (2 * X)
        = Real.exp (-0.4 * Real.sqrt X)
            * (160 * ((m : ℝ) * ((m : ℝ) + 1)) * (2 * X)) := by ring
      _ ≤ Real.exp (-0.4 * Real.sqrt X) * (640 * X ^ 7) :=
          mul_le_mul_of_nonneg_left hstep hE0.le
      _ ≤ Real.exp (-0.4 * Real.sqrt X) * Real.exp (0.4 * Real.sqrt X) :=
          mul_le_mul_of_nonneg_left h640 hE0.le
      _ = 1 := hEE
  have hfinal : 160 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X)
      ≤ (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / (2 * X) := by
    rw [div_div, le_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) * ((m : ℝ) + 1) * (2 * X))]
    calc 160 * (⌊Real.exp X⌋₊ : ℝ) * Real.exp (-0.4 * Real.sqrt X)
          * ((m : ℝ) * ((m : ℝ) + 1) * (2 * X))
        = (⌊Real.exp X⌋₊ : ℝ) * (160 * Real.exp (-0.4 * Real.sqrt X)
            * ((m : ℝ) * ((m : ℝ) + 1)) * (2 * X)) := by ring
      _ ≤ (⌊Real.exp X⌋₊ : ℝ) * 1 := mul_le_mul_of_nonneg_left hkey hN0.le
      _ = (⌊Real.exp X⌋₊ : ℝ) := mul_one _
  linarith

/-! ## Explicit shell counts -/

/-- Lower shell count: `N/(m(m+1))/X − (FKS errors) ≤ P_m` — the lower half
of the paper's eq. `prime-shell-sum`, with `log x_m ≤ X` absorbed into the
main term (this is where the *lower* bound only needs the common cap `X`,
so no cap transport is required on this side). -/
theorem avgLow_card_lower {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X) :
    (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / X
        - (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
          + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))
      ≤ ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hcard := shellPrimes_card_cast_eq ⌊Real.exp X⌋₊ hm1
  have hlow := primeInterval_lower (avgLow_two_le_shell_lo hX hmM)
    (avgLow_shell_lo_le_hi (N := ⌊Real.exp X⌋₊) hm1)
  rw [← hcard] at hlow
  rw [avgLow_shell_gap (N := ⌊Real.exp X⌋₊) hm1] at hlow
  have hG0 : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) := by
    have hN0 : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) := by
      exact_mod_cast one_le_expFloor hX1
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    positivity
  have hlog_pos := avgLow_log_hi_pos hX hm1 hmM
  have hlogle := avgLow_log_hi_le hX1 hm1
  have h2 : (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / X
      ≤ (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1))
          / Real.log ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ)) := by
    rw [div_le_div_iff₀ hX0 hlog_pos]
    nlinarith [mul_le_mul_of_nonneg_left hlogle hG0.le]
  linarith

/-- `N/(m(m+1))/(2X) ≤ P_m`: the FKS errors eat at most half the main term
(via `avgLow_fks_le`). -/
theorem avgLow_card_ge {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X) :
    (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / (2 * X)
      ≤ ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX
  have h1 := avgLow_card_lower hX hm1 hmM
  have h2 := avgLow_fks_le hX hm1 hmM
  have hG : (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / X
      - (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / (2 * X)
      = (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / (2 * X) := by
    field_simp
    ring
  linarith

/-- Every shell `1 ≤ m ≤ M` is nonempty at `X ≥ 10⁷` (its count exceeds the
strictly positive `N/(m(m+1))/(2X)`), so the collision bound applies to every
shell with no empty-shell case split. -/
theorem avgLow_shell_nonempty {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X) :
    (shellPrimes ⌊Real.exp X⌋₊ m).Nonempty := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hN0 : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) := by
    exact_mod_cast one_le_expFloor hX1
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hG0 : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / (2 * X) := by
    positivity
  have h := avgLow_card_ge hX hm1 hmM
  have hpos : (0 : ℝ) < ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) :=
    lt_of_lt_of_le hG0 h
  have hcard : 0 < (shellPrimes ⌊Real.exp X⌋₊ m).card := by exact_mod_cast hpos
  exact Finset.card_pos.mp hcard

/-- Upper shell count: `P_m ≤ 2·(N/(m(m+1)))/X + (FKS errors)` — the upper
half of eq. `prime-shell-sum` with `log y_m ≥ X/2`; this is the count applied
to the collision *loss* (paper: "the upper count to the loss"). -/
theorem avgLow_card_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X) :
    ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)
      ≤ 2 * ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1))) / X
        + (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
          + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))) := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hcard := shellPrimes_card_cast_eq ⌊Real.exp X⌋₊ hm1
  have hup := primeInterval_upper (avgLow_two_le_shell_lo hX hmM)
    (avgLow_shell_lo_le_hi (N := ⌊Real.exp X⌋₊) hm1)
  rw [← hcard] at hup
  rw [avgLow_shell_gap (N := ⌊Real.exp X⌋₊) hm1] at hup
  have hG0 : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) := by
    have hN0 : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) := by
      exact_mod_cast one_le_expFloor hX1
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    positivity
  have hloglo := avgLow_log_lo_ge hX hmM
  have hloglo_pos : (0 : ℝ) < Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)) := by
    linarith
  have h2 : (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1))
        / Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
      ≤ 2 * ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1))) / X := by
    rw [div_le_div_iff₀ hloglo_pos hX0]
    nlinarith [mul_le_mul_of_nonneg_left hloglo hG0.le]
  linarith

/-! ## The collision bound with the capped bracket -/

/-- Monotonicity of `u ↦ u − log(1 + β·e^u)` for `β ≥ 0` (equivalently
`u − log(1+βe^u) = −log(e^{−u} + β)`); the engine behind the paper's
"the same inequality and the identity … give the claim because
`e^{X−g(m)} < 1`" (proof of `prop:averaging-relation`). -/
theorem avgLow_sub_log_exp_mono {β u v : ℝ} (hβ : 0 ≤ β) (huv : u ≤ v) :
    u - Real.log (1 + β * Real.exp u) ≤ v - Real.log (1 + β * Real.exp v) := by
  have hkey : ∀ w : ℝ,
      Real.log (1 + β * Real.exp w) = Real.log (Real.exp (-w) + β) + w := by
    intro w
    have hpos : (0 : ℝ) < 1 + β * Real.exp w := by positivity
    have hid : Real.exp (-w) + β = (1 + β * Real.exp w) * Real.exp (-w) := by
      rw [add_mul, one_mul, mul_assoc, ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, mul_one]
    rw [hid, Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [hkey u, hkey v]
  have h2 : Real.log (Real.exp (-v) + β) ≤ Real.log (Real.exp (-u) + β) := by
    apply Real.log_le_log (by positivity)
    have hexp : Real.exp (-v) ≤ Real.exp (-u) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  linarith

/-- **Capped bracket transfer** (paper, proof of `prop:averaging-relation`:
"The bracket in eq. `collision-sum` is at least `a_m − ℓ_m`"): for `P > 0`,
`S ≥ 1`, `b ≥ 0`,
```
min(log S, Y) − log(1 + b·e^{min(log S, Y)}/P) ≤ log S − log(1 + b(S−1)/P).
```
When `log S ≤ Y` this is `e^{log S} = S ≥ S − 1`; when `log S > Y` it is
`avgLow_sub_log_exp_mono` (the paper's `e^{X−g(m)} < 1` identity). -/
theorem avgLow_capped_deficit_transfer {P bR S Y : ℝ} (hP : 0 < P)
    (hS : 1 ≤ S) (hb : 0 ≤ bR) :
    min (Real.log S) Y - Real.log (1 + bR * Real.exp (min (Real.log S) Y) / P)
      ≤ Real.log S - Real.log (1 + bR * (S - 1) / P) := by
  have hS0 : (0 : ℝ) < S := by linarith
  have hexpS : Real.exp (Real.log S) = S := Real.exp_log hS0
  have hlogle : Real.log (1 + bR * (S - 1) / P) ≤ Real.log (1 + bR * S / P) := by
    have h0 : (0 : ℝ) < 1 + bR * (S - 1) / P := by
      have hnn : 0 ≤ bR * (S - 1) / P :=
        div_nonneg (mul_nonneg hb (by linarith)) hP.le
      linarith
    apply Real.log_le_log h0
    have hd : bR * S / P - bR * (S - 1) / P = bR / P := by ring
    have hnn2 : 0 ≤ bR / P := div_nonneg hb hP.le
    linarith
  rcases min_cases (Real.log S) Y with ⟨hmin, _⟩ | ⟨hmin, hlt⟩
  · rw [hmin, hexpS]
    linarith
  · rw [hmin]
    have hmono := avgLow_sub_log_exp_mono (β := bR / P)
      (div_nonneg hb hP.le) hlt.le
    rw [show bR / P * Real.exp Y = bR * Real.exp Y / P by ring,
      show bR / P * Real.exp (Real.log S) = bR * Real.exp (Real.log S) / P by ring,
      hexpS] at hmono
    linarith

/-- The per-shell collision loss
`ℓ_m = log(1 + b_m·e^{a_m}/P_m)` with `a_m = min(g(m), X)` — the paper's
`ℓ_m` in the proof of `prop:averaging-relation`. -/
noncomputable def avgLow_shellDeficit (X : ℝ) (m : ℕ) : ℝ :=
  Real.log (1 + (avgLow_bChoice X m : ℝ) * Real.exp (min (g m) X)
    / ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ))

/-- **Capped shellwise collision lower bound**: eq. `collision-sum` with the
bracket transported to the capped value,
`P_m·(min(g(m), X) − ℓ_m) ≤ Σ_{p ∈ shell m} log σ_p(m)`. -/
theorem avgLow_shell_collision {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X) :
    ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)
        * (min (g m) X - avgLow_shellDeficit X m)
      ≤ ∑ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, Real.log (sigma p m) := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hne := avgLow_shell_nonempty hX hm1 hmM
  have hprime : ∀ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, Nat.Prime p :=
    fun p hp => (mem_shellPrimes.mp hp).2.2
  have hlarge : ∀ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, m < p := by
    intro p hp
    have h1 := shell_prime_gt_half_exp hX hmM hp
    have hm3 : (m : ℝ) ≤ X ^ 3 :=
      le_trans (Nat.cast_le.mpr hmM) (shellCutoff_cast_le hX0.le)
    have h30 := poly_le_exp_half hX
    have hmp : (m : ℝ) < (p : ℝ) := by
      nlinarith [one_le_pow₀ hX1 (n := 3),
        mul_pos (pow_pos hX0 3) (by linarith : (0 : ℝ) < 30 * X - 1)]
    exact_mod_cast hmp
  have hshell : ∀ p ∈ shellPrimes ⌊Real.exp X⌋₊ m,
      ((⌊Real.exp X⌋₊ : ℕ) : ℝ) / ((m : ℝ) + 1) < (p : ℝ) :=
    fun _p hp => shell_ratio_lt_shell_prime hp
  have hbig := one_lt_shell_ratio hX hmM
  have hb := avgLow_bChoice_spec hX hm1 hmM
  have hcol := shell_collision_lower (shellPrimes ⌊Real.exp X⌋₊ m) hne hprime
    hlarge hshell hbig (avgLow_bChoice X m) hb
  have hPC : (0 : ℝ) < ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hS1 : (1 : ℝ) ≤ ((S m : ℕ) : ℝ) := by exact_mod_cast one_le_S m
  have hb0 : (0 : ℝ) ≤ ((avgLow_bChoice X m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hbr := avgLow_capped_deficit_transfer (Y := X) hPC hS1 hb0
  have hgS : g m = Real.log ((S m : ℕ) : ℝ) := rfl
  rw [← hgS] at hbr
  calc ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)
        * (min (g m) X - avgLow_shellDeficit X m)
      ≤ ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)
          * (g m - Real.log (1 + (avgLow_bChoice X m : ℝ)
              * (((S m : ℕ) : ℝ) - 1)
              / ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ))) :=
        mul_le_mul_of_nonneg_left hbr hPC.le
    _ ≤ ∑ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, Real.log (sigma p m) := hcol

/-! ## The two loss regimes -/

/-- **Small-`m` regime** (paper: "If `m ≤ X/(4log2)`, the logarithmic loss in
eq. `collision-sum` is `O(e^{−X/2})`"): for `m·log 2 ≤ X/4` the whole shell
loss is at most `4·e^{X/4}` *before* normalization, since `b_m ≤ 4` and
`e^{a_m} ≤ S(m) ≤ 2^m ≤ e^{X/4}`. -/
theorem avgLow_deficit_small {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X)
    (hreg : (m : ℝ) * Real.log 2 ≤ X / 4) :
    ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * avgLow_shellDeficit X m
      ≤ 4 * Real.exp (X / 4) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX
  have hPC : (0 : ℝ) < ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (avgLow_shell_nonempty hX hm1 hmM)
  have ht0 : 0 ≤ (avgLow_bChoice X m : ℝ) * Real.exp (min (g m) X)
      / ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) := by positivity
  have hlog : avgLow_shellDeficit X m
      ≤ (avgLow_bChoice X m : ℝ) * Real.exp (min (g m) X)
          / ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) := by
    unfold avgLow_shellDeficit
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + (avgLow_bChoice X m : ℝ) * Real.exp (min (g m) X)
        / ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) by linarith)
    linarith
  have hb4 : (avgLow_bChoice X m : ℝ) ≤ 4 := by
    have h1 := avgLow_bChoice_le hX0 hm1
    have hm2 : 2 * (m : ℝ) ≤ X := by
      nlinarith [Real.log_two_gt_d9, Nat.cast_nonneg (α := ℝ) m]
    have h6 : 6 * (m : ℝ) / X ≤ 3 := by
      rw [div_le_iff₀ hX0]
      linarith
    linarith
  have hexp : Real.exp (min (g m) X) ≤ Real.exp (X / 4) := by
    apply Real.exp_le_exp.mpr
    calc min (g m) X ≤ g m := min_le_left _ _
      _ ≤ (m : ℝ) * Real.log 2 := g_le_mul_log_two m
      _ ≤ X / 4 := hreg
  calc ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * avgLow_shellDeficit X m
      ≤ ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)
          * ((avgLow_bChoice X m : ℝ) * Real.exp (min (g m) X)
            / ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog hPC.le
    _ = (avgLow_bChoice X m : ℝ) * Real.exp (min (g m) X) := by
        field_simp
    _ ≤ 4 * Real.exp (X / 4) :=
        mul_le_mul hb4 hexp (Real.exp_pos _).le (by norm_num)

/-- `log(1+t) ≤ log 2 + max(0, log t)` for `t > 0` (split at `t = 1`).  Turns
the collision loss into the paper's "elementary inequality
`g − log(1+be^g/P) ≥ min(g, log(P/b)) − log 2`". -/
theorem avgLow_log_one_add_le {t : ℝ} (ht : 0 < t) :
    Real.log (1 + t) ≤ Real.log 2 + max 0 (Real.log t) := by
  rcases le_or_gt t 1 with h | h
  · have h1 : Real.log (1 + t) ≤ Real.log 2 :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : (0 : ℝ) ≤ max 0 (Real.log t) := le_max_left _ _
    linarith
  · have h1 : Real.log (1 + t) ≤ Real.log (2 * t) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht.ne'] at h1
    have h2 : Real.log t ≤ max 0 (Real.log t) := le_max_right _ _
    linarith

/-- **Large-`m` regime** (paper: "If `X/(4log2) < m ≤ X²` … the loss from the
capped value is `O(log(m+1))` in this range"): for `m·log 2 > X/4` the
per-shell loss satisfies `ℓ_m ≤ 3·log(m+1) + 5`, via `P_m/b_m ≥ N/(18(m+1)³)`
hence `log(P_m/b_m) ≥ X − 3log(m+1) − 4` (the paper's
`log(P_m/b_m) ≥ X − 3log(m+1) − O(1)`). -/
theorem avgLow_deficit_le_large {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X)
    (hreg : X / 4 < (m : ℝ) * Real.log 2) :
    avgLow_shellDeficit X m ≤ 3 * Real.log ((m : ℝ) + 1) + 5 := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hN1 : (1 : ℝ) ≤ (⌊Real.exp X⌋₊ : ℝ) := by
    exact_mod_cast one_le_expFloor hX1
  have hN0 : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) := by linarith
  have hPC : (0 : ℝ) < ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (avgLow_shell_nonempty hX hm1 hmM)
  have hb1 : (1 : ℝ) ≤ (avgLow_bChoice X m : ℝ) := by
    exact_mod_cast avgLow_one_le_bChoice X m
  have hb0 : (0 : ℝ) < (avgLow_bChoice X m : ℝ) := by linarith
  -- `b ≤ 9m/X` in this regime (the `+1` of `bChoice` is absorbed)
  have hb9 : (avgLow_bChoice X m : ℝ) ≤ 9 * (m : ℝ) / X := by
    have h1 := avgLow_bChoice_le hX0 hm1
    have h3 : X < 3 * (m : ℝ) := by
      nlinarith [Real.log_two_lt_d9,
        mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le
          (by positivity : (0 : ℝ) ≤ 4 * (m : ℝ))]
    have h1m : (1 : ℝ) ≤ 3 * (m : ℝ) / X := by
      rw [le_div_iff₀ hX0]; linarith
    have hsplit : 9 * (m : ℝ) / X - 6 * (m : ℝ) / X = 3 * (m : ℝ) / X := by ring
    linarith
  -- `P/b ≥ N/(18(m+1)³)`
  have hcard := avgLow_card_ge hX hm1 hmM
  have hPB1 : (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / (2 * X)
        / (9 * (m : ℝ) / X)
      ≤ ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) / (avgLow_bChoice X m : ℝ) :=
    div_le_div₀ hPC.le hcard hb0 hb9
  have hPB2 : (⌊Real.exp X⌋₊ : ℝ) / (18 * ((m : ℝ) + 1) ^ 3)
      ≤ (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / (2 * X)
        / (9 * (m : ℝ) / X) := by
    have heq : (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / (2 * X)
          / (9 * (m : ℝ) / X)
        = (⌊Real.exp X⌋₊ : ℝ) / (18 * (m : ℝ) * (m : ℝ) * ((m : ℝ) + 1)) := by
      field_simp
      ring
    rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (m : ℝ) * (m : ℝ) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq
      (by positivity : (0 : ℝ) ≤ (⌊Real.exp X⌋₊ : ℝ) * (18 * ((m : ℝ) + 1)))]
  have hPB : (⌊Real.exp X⌋₊ : ℝ) / (18 * ((m : ℝ) + 1) ^ 3)
      ≤ ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) / (avgLow_bChoice X m : ℝ) :=
    le_trans hPB2 hPB1
  have hPBpos : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) / (18 * ((m : ℝ) + 1) ^ 3) := by
    positivity
  -- `log(P/b) ≥ X − 4 − 3log(m+1)`
  have hlogPB : X - 4 - 3 * Real.log ((m : ℝ) + 1)
      ≤ Real.log (((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)
          / (avgLow_bChoice X m : ℝ)) := by
    have h1 : Real.log ((⌊Real.exp X⌋₊ : ℝ) / (18 * ((m : ℝ) + 1) ^ 3))
        ≤ Real.log (((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)
            / (avgLow_bChoice X m : ℝ)) :=
      Real.log_le_log hPBpos hPB
    have h2 : Real.log ((⌊Real.exp X⌋₊ : ℝ) / (18 * ((m : ℝ) + 1) ^ 3))
        = Real.log (⌊Real.exp X⌋₊ : ℝ)
          - (Real.log 18 + 3 * Real.log ((m : ℝ) + 1)) := by
      rw [Real.log_div hN0.ne' (by positivity),
        Real.log_mul (by norm_num : (18 : ℝ) ≠ 0) (by positivity),
        Real.log_pow]
      push_cast
      ring
    have h3 : X - 1 ≤ Real.log (⌊Real.exp X⌋₊ : ℝ) := by
      have h4 := log_expFloor_ge hX1
      have h5 : 1 / (⌊Real.exp X⌋₊ : ℝ) ≤ 1 := by
        rw [div_le_one hN0]; exact hN1
      linarith
    have h18 : Real.log 18 ≤ 3 := by
      have he3 : (18 : ℝ) ≤ Real.exp 3 := by
        have h3e : Real.exp (3 : ℝ) = Real.exp 1 ^ (3 : ℕ) := by
          rw [Real.exp_one_pow]; norm_num
        rw [h3e]
        calc (18 : ℝ) ≤ 2.7182818283 ^ (3 : ℕ) := by norm_num
          _ ≤ Real.exp 1 ^ (3 : ℕ) :=
            pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 3
      calc Real.log 18 ≤ Real.log (Real.exp 3) :=
            Real.log_le_log (by norm_num) he3
        _ = 3 := Real.log_exp 3
    linarith
  -- `log t ≤ 4 + 3log(m+1)` for `t = b·e^{a_m}/P`
  have ht0 : (0 : ℝ) < (avgLow_bChoice X m : ℝ) * Real.exp (min (g m) X)
      / ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) := by positivity
  have hlogt : Real.log ((avgLow_bChoice X m : ℝ) * Real.exp (min (g m) X)
        / ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ))
      ≤ 4 + 3 * Real.log ((m : ℝ) + 1) := by
    have heq : (avgLow_bChoice X m : ℝ) * Real.exp (min (g m) X)
          / ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)
        = Real.exp (min (g m) X)
          / (((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) / (avgLow_bChoice X m : ℝ)) := by
      field_simp
    have hPBq : (0 : ℝ) < ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)
        / (avgLow_bChoice X m : ℝ) := by positivity
    have hlog2 : Real.log ((avgLow_bChoice X m : ℝ) * Real.exp (min (g m) X)
          / ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ))
        = min (g m) X - Real.log (((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)
            / (avgLow_bChoice X m : ℝ)) := by
      rw [heq, Real.log_div (Real.exp_pos _).ne' hPBq.ne', Real.log_exp]
    rw [hlog2]
    have hminX : min (g m) X ≤ X := min_le_right _ _
    linarith
  -- assemble
  have hell := avgLow_log_one_add_le ht0
  have hlog2le : Real.log 2 ≤ 1 := log_two_le_one
  have hlogm_nn : (0 : ℝ) ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hmax : max 0 (Real.log ((avgLow_bChoice X m : ℝ)
        * Real.exp (min (g m) X) / ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)))
      ≤ 4 + 3 * Real.log ((m : ℝ) + 1) :=
    max_le (by linarith) hlogt
  unfold avgLow_shellDeficit
  linarith

/-! ## The per-shell master inequality -/

/-- The per-shell loss budget: the exponentially negligible `4e^{X/4}`
(normalized) in the small-`m` regime, the `O(log(m+1))`-per-weight loss in
the large-`m` regime. -/
noncomputable def avgLow_regimeTerm (X : ℝ) (m : ℕ) : ℝ :=
  if (m : ℝ) * Real.log 2 ≤ X / 4 then
    X / (⌊Real.exp X⌋₊ : ℝ) * (4 * Real.exp (X / 4))
  else
    2 * (3 * Real.log ((m : ℝ) + 1) + 5) / ((m : ℝ) * ((m : ℝ) + 1))

/-- **Per-shell master inequality** (the lower-bound half of the paper's
shellwise estimate, combining eq. `prime-shell-sum`, eq. `collision-sum`,
and the two loss regimes): for every shell `1 ≤ m ≤ M`, `X ≥ 10⁷`,

```
min(g(m),X)/(m(m+1)) ≤ (X/N)·Σ_{p ∈ shell m} log σ_p(m)
                       + 2·X·(X/N)·(FKS errors of shell m)
                       + avgLow_regimeTerm X m.
```
-/
theorem avgLow_shell_term_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X) :
    min (g m) X / ((m : ℝ) * ((m : ℝ) + 1))
      ≤ X / (⌊Real.exp X⌋₊ : ℝ)
            * ∑ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, Real.log (sigma p m)
          + 2 * (X * (X / (⌊Real.exp X⌋₊ : ℝ)
            * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
              + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))))
          + avgLow_regimeTerm X m := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hN1 : (1 : ℝ) ≤ (⌊Real.exp X⌋₊ : ℝ) := by
    exact_mod_cast one_le_expFloor hX1
  have hN0 : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) := by linarith
  have hfks0 : 0 ≤ fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
      + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)) :=
    add_nonneg (fksError_nonneg (by positivity)) (fksError_nonneg (by positivity))
  have ham0 : 0 ≤ min (g m) X := le_min (g_nonneg m) hX0.le
  have hamX : min (g m) X ≤ X := min_le_right _ _
  have hPC : (0 : ℝ) < ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (avgLow_shell_nonempty hX hm1 hmM)
  have hXN0 : (0 : ℝ) ≤ X / (⌊Real.exp X⌋₊ : ℝ) := by positivity
  -- positive part: `min(g,X)/(m(m+1)) ≤ (X/N)·(P·min) + X·(X/N)·fks`
  have hpos : min (g m) X / ((m : ℝ) * ((m : ℝ) + 1))
      ≤ X / (⌊Real.exp X⌋₊ : ℝ)
          * (((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * min (g m) X)
        + X * (X / (⌊Real.exp X⌋₊ : ℝ)
          * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))) := by
    have hlow := avgLow_card_lower hX hm1 hmM
    have h1 := mul_le_mul_of_nonneg_right hlow ham0
    have h2 : (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
          + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))) * min (g m) X
        ≤ (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
          + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))) * X :=
      mul_le_mul_of_nonneg_left hamX hfks0
    have h3 : (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / X * min (g m) X
        ≤ ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * min (g m) X
          + (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))) * X := by
      nlinarith [h1, h2]
    have h4 := mul_le_mul_of_nonneg_left h3 hXN0
    have h5 : X / (⌊Real.exp X⌋₊ : ℝ)
        * ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) / X * min (g m) X)
        = min (g m) X / ((m : ℝ) * ((m : ℝ) + 1)) := by
      field_simp
    have h6 : X / (⌊Real.exp X⌋₊ : ℝ)
        * (((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * min (g m) X
          + (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))) * X)
        = X / (⌊Real.exp X⌋₊ : ℝ)
            * (((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * min (g m) X)
          + X * (X / (⌊Real.exp X⌋₊ : ℝ)
            * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
              + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))) := by ring
    rw [h5, h6] at h4
    exact h4
  -- collision: `(X/N)·(P·min) ≤ (X/N)·Σ + (X/N)·(P·ℓ)`
  have hcol := avgLow_shell_collision hX hm1 hmM
  have h7 : ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * min (g m) X
      ≤ (∑ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, Real.log (sigma p m))
        + ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * avgLow_shellDeficit X m := by
    rw [mul_sub] at hcol
    linarith
  have h14 := mul_le_mul_of_nonneg_left h7 hXN0
  rw [mul_add] at h14
  -- the loss, by regime
  have h8 : X / (⌊Real.exp X⌋₊ : ℝ)
      * (((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * avgLow_shellDeficit X m)
      ≤ avgLow_regimeTerm X m
        + X * (X / (⌊Real.exp X⌋₊ : ℝ)
          * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))) := by
    unfold avgLow_regimeTerm
    split_ifs with hreg
    · have hd := avgLow_deficit_small hX hm1 hmM hreg
      have h9 := mul_le_mul_of_nonneg_left hd hXN0
      have hfnn : 0 ≤ X * (X / (⌊Real.exp X⌋₊ : ℝ)
          * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))) :=
        mul_nonneg hX0.le (mul_nonneg hXN0 hfks0)
      linarith
    · push Not at hreg
      have hd := avgLow_deficit_le_large hX hm1 hmM hreg
      have hd0 : 0 ≤ avgLow_shellDeficit X m := by
        unfold avgLow_shellDeficit
        apply Real.log_nonneg
        have : (0 : ℝ) ≤ (avgLow_bChoice X m : ℝ) * Real.exp (min (g m) X)
            / ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) := by positivity
        linarith
      have hup := avgLow_card_le hX hm1 hmM
      have hlogm_nn : (0 : ℝ) ≤ Real.log ((m : ℝ) + 1) :=
        Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 m)
      have hupnn : (0 : ℝ) ≤ 2 * ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1))) / X
          + (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))) := by
        have : (0 : ℝ) ≤ 2 * ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1))) / X := by
          positivity
        linarith
      have h9 : ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * avgLow_shellDeficit X m
          ≤ (2 * ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1))) / X
              + (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
                + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))))
            * (3 * Real.log ((m : ℝ) + 1) + 5) :=
        mul_le_mul hup hd hd0 hupnn
      have h10 := mul_le_mul_of_nonneg_left h9 hXN0
      have h11 : X / (⌊Real.exp X⌋₊ : ℝ)
          * ((2 * ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1))) / X
              + (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
                + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))))
            * (3 * Real.log ((m : ℝ) + 1) + 5))
          = 2 * (3 * Real.log ((m : ℝ) + 1) + 5) / ((m : ℝ) * ((m : ℝ) + 1))
            + X / (⌊Real.exp X⌋₊ : ℝ)
              * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
                + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))
              * (3 * Real.log ((m : ℝ) + 1) + 5) := by
        field_simp
      rw [h11] at h10
      have hdmX := avgLow_deficit_bound_le hX hmM
      have h12 : X / (⌊Real.exp X⌋₊ : ℝ)
          * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))
          * (3 * Real.log ((m : ℝ) + 1) + 5)
          ≤ X / (⌊Real.exp X⌋₊ : ℝ)
            * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
              + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))) * X :=
        mul_le_mul_of_nonneg_left hdmX (mul_nonneg hXN0 hfks0)
      have h13 : X / (⌊Real.exp X⌋₊ : ℝ)
          * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))) * X
          = X * (X / (⌊Real.exp X⌋₊ : ℝ)
            * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
              + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))) := by ring
      rw [h13] at h12
      linarith
  linarith

/-! ## Summing the regimes -/

/-- Absorbing the linear-in-`log X` losses into `3(log X)²`: for `l ≥ 16`,
`36(l+1) + 30 ≤ 3l²`. -/
theorem avgLow_absorb_logsq {l : ℝ} (hl : 16 ≤ l) :
    36 * (l + 1) + 30 ≤ 3 * l ^ 2 := by
  nlinarith [sq_nonneg (l - 16)]

/-- **Total small-`m` loss**: at most `X` shells lie below `X/(4 log 2)`, and
each contributes `(X/N)·4e^{X/4}`, so the total is exponentially negligible,
`≤ 1/X²` (paper: "If `m ≤ X/(4log2)`, the logarithmic loss in
eq. `collision-sum` is `O(e^{−X/2})`"). -/
theorem avgLow_regime_small_sum_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    ∑ m ∈ (Finset.Icc 1 (shellCutoff X)).filter
        (fun m : ℕ => (m : ℝ) * Real.log 2 ≤ X / 4), avgLow_regimeTerm X m
      ≤ 1 / X ^ 2 := by
  have hX' : (10000000 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog2gt := Real.log_two_gt_d9
  have hconst : ∀ m ∈ (Finset.Icc 1 (shellCutoff X)).filter
      (fun m : ℕ => (m : ℝ) * Real.log 2 ≤ X / 4),
      avgLow_regimeTerm X m
        = X / (⌊Real.exp X⌋₊ : ℝ) * (4 * Real.exp (X / 4)) := by
    intro m hm
    unfold avgLow_regimeTerm
    rw [if_pos (Finset.mem_filter.mp hm).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hsub : (Finset.Icc 1 (shellCutoff X)).filter
      (fun m : ℕ => (m : ℝ) * Real.log 2 ≤ X / 4) ⊆ Finset.Icc 1 ⌊X⌋₊ := by
    intro k hk
    obtain ⟨hkIcc, hkp⟩ := Finset.mem_filter.mp hk
    have hk1 := (Finset.mem_Icc.mp hkIcc).1
    have hkX : (k : ℝ) ≤ X := by
      nlinarith [hkp, Nat.cast_nonneg (α := ℝ) k,
        mul_le_mul_of_nonneg_left hlog2gt.le (Nat.cast_nonneg (α := ℝ) k)]
    exact Finset.mem_Icc.mpr ⟨hk1, Nat.le_floor hkX⟩
  have hcard : (((Finset.Icc 1 (shellCutoff X)).filter
      (fun m : ℕ => (m : ℝ) * Real.log 2 ≤ X / 4)).card : ℝ) ≤ X := by
    have h1 := Finset.card_le_card hsub
    have h2 : (Finset.Icc 1 ⌊X⌋₊).card = ⌊X⌋₊ := by
      rw [Nat.card_Icc]; omega
    have h3 : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0.le
    calc (((Finset.Icc 1 (shellCutoff X)).filter
          (fun m : ℕ => (m : ℝ) * Real.log 2 ≤ X / 4)).card : ℝ)
        ≤ ((⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1.trans_eq h2
      _ ≤ X := h3
  have hcnn : (0 : ℝ) ≤ X / (⌊Real.exp X⌋₊ : ℝ) * (4 * Real.exp (X / 4)) := by
    positivity
  have h4 : (((Finset.Icc 1 (shellCutoff X)).filter
        (fun m : ℕ => (m : ℝ) * Real.log 2 ≤ X / 4)).card : ℝ)
        * (X / (⌊Real.exp X⌋₊ : ℝ) * (4 * Real.exp (X / 4)))
      ≤ X * (X / (⌊Real.exp X⌋₊ : ℝ) * (4 * Real.exp (X / 4))) :=
    mul_le_mul_of_nonneg_right hcard hcnn
  have h5 : X * (X / (⌊Real.exp X⌋₊ : ℝ) * (4 * Real.exp (X / 4))) ≤ 1 / X ^ 2 := by
    have hXN : X / (⌊Real.exp X⌋₊ : ℝ) ≤ 2 * X / Real.exp X := div_expFloor_le hX1
    have h6 : X * (X / (⌊Real.exp X⌋₊ : ℝ) * (4 * Real.exp (X / 4)))
        ≤ 8 * X ^ 2 * Real.exp (X / 4) / Real.exp X := by
      have h7 := mul_le_mul_of_nonneg_right hXN
        (by positivity : (0 : ℝ) ≤ 4 * Real.exp (X / 4))
      calc X * (X / (⌊Real.exp X⌋₊ : ℝ) * (4 * Real.exp (X / 4)))
          ≤ X * (2 * X / Real.exp X * (4 * Real.exp (X / 4))) :=
            mul_le_mul_of_nonneg_left h7 hX0.le
        _ = 8 * X ^ 2 * Real.exp (X / 4) / Real.exp X := by ring
    have h8 : 8 * X ^ 2 * Real.exp (X / 4) / Real.exp X ≤ 1 / X ^ 2 := by
      rw [div_le_div_iff₀ (Real.exp_pos X) (by positivity : (0 : ℝ) < X ^ 2)]
      have hsplit : Real.exp X
          = Real.exp (X / 2) * Real.exp (X / 4) * Real.exp (X / 4) := by
        rw [← Real.exp_add, ← Real.exp_add,
          show X / 2 + X / 4 + X / 4 = X by ring]
      have h30 := poly_le_exp_half hX
      have he1 : (1 : ℝ) ≤ Real.exp (X / 4) := by
        rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
        exact Real.exp_le_exp.mpr (by linarith)
      rw [hsplit]
      nlinarith [mul_le_mul_of_nonneg_right h30 (Real.exp_pos (X / 4)).le,
        (Real.exp_pos (X / 4)).le, (Real.exp_pos (X / 2)).le,
        mul_nonneg (pow_nonneg hX0.le 4) (Real.exp_pos (X / 4)).le,
        mul_pos (mul_pos (Real.exp_pos (X / 2)) (Real.exp_pos (X / 4)))
          (Real.exp_pos (X / 4))]
    linarith
  linarith

/-- **Total large-`m` loss**: the `O(log(m+1))`-per-shell losses beyond
`X/(4 log 2)` sum to at most `3(log X)²/X` (paper: "its normalized sum is
bounded by `Σ_{X/(4log2)<m≤X²} log(m+1)/(m(m+1)) = O(log X/X)`"; our shells
run to `M = ⌊X³⌋` instead of `X²`, which only helps since the summand is
positive and the integral-tail bounds of `LogSumBounds` are uniform in the
upper limit). -/
theorem avgLow_regime_large_sum_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    ∑ m ∈ (Finset.Icc 1 (shellCutoff X)).filter
        (fun m : ℕ => ¬ ((m : ℝ) * Real.log 2 ≤ X / 4)), avgLow_regimeTerm X m
      ≤ 3 * Real.log X ^ 2 / X := by
  have hX' : (10000000 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog2gt := Real.log_two_gt_d9
  have hlog2lt := Real.log_two_lt_d9
  have hAd0 : (0 : ℝ) < 4 * Real.log 2 := by linarith
  have hAle : ((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) ≤ X / (4 * Real.log 2) :=
    Nat.floor_le (by positivity)
  have hAgt : X / (4 * Real.log 2) - 1 < ((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) :=
    Nat.sub_one_lt_floor _
  have hd36 : 0.36 * X ≤ X / (4 * Real.log 2) := by
    rw [le_div_iff₀ hAd0]
    nlinarith [mul_nonneg hX0.le (by linarith : (0 : ℝ) ≤ 1 - 1.44 * Real.log 2)]
  have hA35 : 0.35 * X ≤ ((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) := by linarith
  have hA3 : 3 ≤ ⌊X / (4 * Real.log 2)⌋₊ := by
    have h1 : (3 : ℝ) ≤ ((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) := by linarith
    exact_mod_cast h1
  have hA1 : 1 ≤ ⌊X / (4 * Real.log 2)⌋₊ := le_trans (by norm_num) hA3
  have hAX : ((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) + 1 ≤ X := by
    have h1 : X / (4 * Real.log 2) ≤ X / 2 := by
      rw [div_le_div_iff₀ hAd0 (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hX0.le]
    linarith
  -- the regime-b shells sit inside `Ioc A M`
  have hsub : (Finset.Icc 1 (shellCutoff X)).filter
        (fun m : ℕ => ¬ ((m : ℝ) * Real.log 2 ≤ X / 4))
      ⊆ Finset.Ioc ⌊X / (4 * Real.log 2)⌋₊ (shellCutoff X) := by
    intro k hk
    obtain ⟨hkIcc, hkp⟩ := Finset.mem_filter.mp hk
    push Not at hkp
    have hkM := (Finset.mem_Icc.mp hkIcc).2
    have hAk : ((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) < (k : ℝ) := by
      have h2 : X / (4 * Real.log 2) < (k : ℝ) := by
        rw [div_lt_iff₀ hAd0]
        nlinarith [hkp]
      linarith
    have hAk' : ⌊X / (4 * Real.log 2)⌋₊ < k := by exact_mod_cast hAk
    exact Finset.mem_Ioc.mpr ⟨hAk', hkM⟩
  have hterm_eq : ∀ k ∈ (Finset.Icc 1 (shellCutoff X)).filter
      (fun m : ℕ => ¬ ((m : ℝ) * Real.log 2 ≤ X / 4)),
      avgLow_regimeTerm X k
        = 2 * (3 * Real.log ((k : ℝ) + 1) + 5) / ((k : ℝ) * ((k : ℝ) + 1)) := by
    intro k hk
    unfold avgLow_regimeTerm
    rw [if_neg (Finset.mem_filter.mp hk).2]
  have hfnonneg : ∀ k ∈ Finset.Ioc ⌊X / (4 * Real.log 2)⌋₊ (shellCutoff X),
      (0 : ℝ) ≤ 2 * (3 * Real.log ((k : ℝ) + 1) + 5) / ((k : ℝ) * ((k : ℝ) + 1)) := by
    intro k hk
    have hk1 : 1 ≤ k := by
      have := (Finset.mem_Ioc.mp hk).1
      omega
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hlognn : (0 : ℝ) ≤ Real.log ((k : ℝ) + 1) :=
      Real.log_nonneg (by linarith)
    apply div_nonneg (by linarith) (by positivity)
  have hsplit : ∀ k ∈ Finset.Ioc ⌊X / (4 * Real.log 2)⌋₊ (shellCutoff X),
      2 * (3 * Real.log ((k : ℝ) + 1) + 5) / ((k : ℝ) * ((k : ℝ) + 1))
        ≤ 12 * (Real.log ((k : ℝ) + 1) / (((k : ℝ) + 1) * ((k : ℝ) + 1)))
          + 10 * (1 / ((k : ℝ) * (k : ℝ))) := by
    intro k hk
    have hk1 : 1 ≤ k := by
      have := (Finset.mem_Ioc.mp hk).1
      omega
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hL : (0 : ℝ) ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith)
    have heq : 2 * (3 * Real.log ((k : ℝ) + 1) + 5) / ((k : ℝ) * ((k : ℝ) + 1))
        = 6 * Real.log ((k : ℝ) + 1) / ((k : ℝ) * ((k : ℝ) + 1))
          + 10 / ((k : ℝ) * ((k : ℝ) + 1)) := by
      ring
    have h1 : 6 * Real.log ((k : ℝ) + 1) / ((k : ℝ) * ((k : ℝ) + 1))
        ≤ 12 * (Real.log ((k : ℝ) + 1) / (((k : ℝ) + 1) * ((k : ℝ) + 1))) := by
      rw [mul_div_assoc' 12 _ _, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hk1'
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6)
          (mul_nonneg hL (by linarith : (0 : ℝ) ≤ (k : ℝ) + 1)))]
    have h2 : 10 / ((k : ℝ) * ((k : ℝ) + 1)) ≤ 10 * (1 / ((k : ℝ) * (k : ℝ))) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith [heq ▸ le_refl
      (2 * (3 * Real.log ((k : ℝ) + 1) + 5) / ((k : ℝ) * ((k : ℝ) + 1)))]
  have hsum1 := sum_log_div_sq_tail_le ⌊X / (4 * Real.log 2)⌋₊ (shellCutoff X) hA3
  have hsum2 := sum_one_div_Ioc_le ⌊X / (4 * Real.log 2)⌋₊ (shellCutoff X) hA1
  calc ∑ m ∈ (Finset.Icc 1 (shellCutoff X)).filter
        (fun m : ℕ => ¬ ((m : ℝ) * Real.log 2 ≤ X / 4)), avgLow_regimeTerm X m
      = ∑ m ∈ (Finset.Icc 1 (shellCutoff X)).filter
          (fun m : ℕ => ¬ ((m : ℝ) * Real.log 2 ≤ X / 4)),
          2 * (3 * Real.log ((m : ℝ) + 1) + 5) / ((m : ℝ) * ((m : ℝ) + 1)) :=
        Finset.sum_congr rfl hterm_eq
    _ ≤ ∑ m ∈ Finset.Ioc ⌊X / (4 * Real.log 2)⌋₊ (shellCutoff X),
          2 * (3 * Real.log ((m : ℝ) + 1) + 5) / ((m : ℝ) * ((m : ℝ) + 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k hk _ => hfnonneg k hk)
    _ ≤ ∑ m ∈ Finset.Ioc ⌊X / (4 * Real.log 2)⌋₊ (shellCutoff X),
          (12 * (Real.log ((m : ℝ) + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 1)))
            + 10 * (1 / ((m : ℝ) * (m : ℝ)))) := Finset.sum_le_sum hsplit
    _ = 12 * ∑ m ∈ Finset.Ioc ⌊X / (4 * Real.log 2)⌋₊ (shellCutoff X),
          Real.log ((m : ℝ) + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 1))
        + 10 * ∑ m ∈ Finset.Ioc ⌊X / (4 * Real.log 2)⌋₊ (shellCutoff X),
          1 / ((m : ℝ) * (m : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 12 * ((Real.log (((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) + 1) + 1)
          / (((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) + 1))
        + 10 * (1 / ((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ)) := by
        have h12 := mul_le_mul_of_nonneg_left hsum1 (by norm_num : (0 : ℝ) ≤ 12)
        have h10 := mul_le_mul_of_nonneg_left hsum2 (by norm_num : (0 : ℝ) ≤ 10)
        rw [one_div] at h10 ⊢
        linarith
    _ ≤ 3 * Real.log X ^ 2 / X := by
        have hlogA : Real.log (((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) + 1)
            ≤ Real.log X := Real.log_le_log (by positivity) hAX
        have hl16 := avgLow_sixteen_le_log hX
        have hA3X : X / 3 ≤ ((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) := by linarith
        have hA3X1 : X / 3 ≤ ((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) + 1 := by
          linarith
        have hb1 : 12 * ((Real.log (((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) + 1) + 1)
              / (((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) + 1))
            ≤ 12 * ((Real.log X + 1) / (X / 3)) := by
          have h1 : (Real.log (((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) + 1) + 1)
                / (((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) + 1)
              ≤ (Real.log X + 1) / (X / 3) :=
            div_le_div₀ (by linarith) (by linarith)
              (by positivity) hA3X1
          linarith
        have hb2 : 10 * (1 / ((⌊X / (4 * Real.log 2)⌋₊ : ℕ) : ℝ))
            ≤ 10 * (1 / (X / 3)) := by
          have h1 := one_div_le_one_div_of_le
            (by positivity : (0 : ℝ) < X / 3) hA3X
          linarith
        have hfin : 12 * ((Real.log X + 1) / (X / 3)) + 10 * (1 / (X / 3))
            ≤ 3 * Real.log X ^ 2 / X := by
          have heqL : 12 * ((Real.log X + 1) / (X / 3)) + 10 * (1 / (X / 3))
              = (36 * (Real.log X + 1) + 30) * (1 / X) := by
            field_simp
            ring
          have heqR : 3 * Real.log X ^ 2 / X = 3 * Real.log X ^ 2 * (1 / X) := by
            ring
          rw [heqL, heqR]
          exact mul_le_mul_of_nonneg_right (avgLow_absorb_logsq hl16)
            (by positivity : (0 : ℝ) ≤ 1 / X)
        linarith

/-- **Total loss over all shells** — the paper's two loss estimates summed:
`Σ_m avgLow_regimeTerm X m ≤ 1/X² + 3(log X)²/X`. -/
theorem avgLow_regimeTerm_sum_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    ∑ m ∈ Finset.Icc 1 (shellCutoff X), avgLow_regimeTerm X m
      ≤ 1 / X ^ 2 + 3 * Real.log X ^ 2 / X := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (shellCutoff X))
    (fun m : ℕ => (m : ℝ) * Real.log 2 ≤ X / 4)]
  exact add_le_add (avgLow_regime_small_sum_le hX) (avgLow_regime_large_sum_le hX)

/-! ## Cutting `𝓑` at the shell cutoff -/

/-- `𝓑(X)` is its partial sum over the shells `1 ≤ m ≤ M` up to the
telescoping tail: `𝓑(X) ≤ Σ_{m≤M} min(g(m),X)/(m(m+1)) + 1/X²` (paper:
"`Σ_{m>M} min(g(m),X)/(m(m+1)) ≤ X/(M+1)`, which is `O(X⁻²)`"). -/
theorem avgLow_B_le_capped_sum {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    B X ≤ (∑ m ∈ Finset.Icc 1 (shellCutoff X),
        min (g m) X / ((m : ℝ) * ((m : ℝ) + 1))) + 1 / X ^ 2 := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hf1 : Summable (fun k =>
      if k ∈ Finset.range (shellCutoff X) then BTerm X k else 0) :=
    summable_of_ne_finset_zero (s := Finset.range (shellCutoff X))
      (fun _k hk => if_neg hk)
  have hf2 : Summable (fun k => X * weightTail (shellCutoff X + 1) k) :=
    (summable_weightTail _).mul_left X
  have hle : ∀ k, BTerm X k
      ≤ (if k ∈ Finset.range (shellCutoff X) then BTerm X k else 0)
        + X * weightTail (shellCutoff X + 1) k := by
    intro k
    by_cases hk : k ∈ Finset.range (shellCutoff X)
    · rw [if_pos hk]
      have h0 : 0 ≤ X * weightTail (shellCutoff X + 1) k :=
        mul_nonneg hX0.le (weightTail_nonneg _ _)
      linarith
    · rw [if_neg hk]
      have hkM : shellCutoff X ≤ k := by
        simp only [Finset.mem_range, not_lt] at hk
        exact hk
      have hwt : weightTail (shellCutoff X + 1) k
          = 1 / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
        rw [weightTail, if_pos (by omega : shellCutoff X + 1 ≤ k + 1)]
      rw [hwt, BTerm, zero_add, mul_one_div]
      exact div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
  have htsum : B X ≤ (∑ k ∈ Finset.range (shellCutoff X), BTerm X k)
      + X * (1 / ((shellCutoff X + 1 : ℕ) : ℝ)) := by
    have h1 : B X ≤ ∑' k,
        ((if k ∈ Finset.range (shellCutoff X) then BTerm X k else 0)
          + X * weightTail (shellCutoff X + 1) k) :=
      Summable.tsum_le_tsum hle (summable_BTerm X) (hf1.add hf2)
    rw [hf1.tsum_add hf2,
      tsum_eq_sum (s := Finset.range (shellCutoff X)) (fun _k hk => if_neg hk),
      Finset.sum_congr rfl (fun k hk => if_pos hk), tsum_mul_left,
      tsum_weightTail (Nat.le_add_left 1 _)] at h1
    exact h1
  have hreindex : ∑ k ∈ Finset.range (shellCutoff X), BTerm X k
      = ∑ m ∈ Finset.Icc 1 (shellCutoff X),
          min (g m) X / ((m : ℝ) * ((m : ℝ) + 1)) := by
    rw [show Finset.Icc 1 (shellCutoff X) = Finset.Ico 1 (shellCutoff X + 1) by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i _
    rw [BTerm, Nat.add_comm 1 i]
    push_cast
    ring_nf
  have htail : X * (1 / ((shellCutoff X + 1 : ℕ) : ℝ)) ≤ 1 / X ^ 2 := by
    have hM3 : X ^ 3 < ((shellCutoff X : ℕ) : ℝ) + 1 := cube_lt_shellCutoff_add_one X
    have hcast : ((shellCutoff X + 1 : ℕ) : ℝ) = ((shellCutoff X : ℕ) : ℝ) + 1 := by
      push_cast; ring
    rw [hcast]
    have hX3 : (0 : ℝ) < X ^ 3 := by positivity
    have h1 : 1 / (((shellCutoff X : ℕ) : ℝ) + 1) ≤ 1 / X ^ 3 :=
      one_div_le_one_div_of_le hX3 hM3.le
    calc X * (1 / (((shellCutoff X : ℕ) : ℝ) + 1)) ≤ X * (1 / X ^ 3) :=
          mul_le_mul_of_nonneg_left h1 hX0.le
      _ = 1 / X ^ 2 := by
          field_simp
  rw [hreindex] at htsum
  linarith

/-! ## Summing the shells against the shell decomposition -/

/-- The capped shell sum is dominated by the normalized `g(N)` plus the three
explicit error budgets — the reverse of eq. `shell-upper` before the
`𝓑`-tail and the normalization bridge are added. -/
theorem avgLow_capped_sum_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    ∑ m ∈ Finset.Icc 1 (shellCutoff X),
        min (g m) X / ((m : ℝ) * ((m : ℝ) + 1))
      ≤ X / (⌊Real.exp X⌋₊ : ℝ) * g ⌊Real.exp X⌋₊
        + (2 / X + (1 / X ^ 2 + 3 * Real.log X ^ 2 / X)) := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hN1 : (1 : ℝ) ≤ (⌊Real.exp X⌋₊ : ℝ) := by
    exact_mod_cast one_le_expFloor hX1
  have hXN0 : (0 : ℝ) ≤ X / (⌊Real.exp X⌋₊ : ℝ) := by positivity
  have hterm : ∀ m ∈ Finset.Icc 1 (shellCutoff X),
      min (g m) X / ((m : ℝ) * ((m : ℝ) + 1))
        ≤ X / (⌊Real.exp X⌋₊ : ℝ)
              * ∑ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, Real.log (sigma p m)
            + 2 * (X * (X / (⌊Real.exp X⌋₊ : ℝ)
              * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
                + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))))
            + avgLow_regimeTerm X m := by
    intro m hm
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    exact avgLow_shell_term_le hX hm1 hmM
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  -- the shell decomposition bounds the main term
  have hdecomp := (g_shell_decomposition (averaging_hQN hX) (averaging_hQ2 hX)).1
  have h2 : X / (⌊Real.exp X⌋₊ : ℝ)
      * ∑ m ∈ Finset.Icc 1 (shellCutoff X),
          ∑ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, Real.log (sigma p m)
      ≤ X / (⌊Real.exp X⌋₊ : ℝ) * g ⌊Real.exp X⌋₊ :=
    mul_le_mul_of_nonneg_left hdecomp hXN0
  -- the FKS budget
  have h3 : ∑ m ∈ Finset.Icc 1 (shellCutoff X),
        2 * (X * (X / (⌊Real.exp X⌋₊ : ℝ)
          * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))))
      = 2 * X * (X / (⌊Real.exp X⌋₊ : ℝ)
          * ∑ m ∈ Finset.Icc 1 (shellCutoff X),
            (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
              + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have h4 := fks_shell_total_le hX
  have h5 : 2 * X * (X / (⌊Real.exp X⌋₊ : ℝ)
        * ∑ m ∈ Finset.Icc 1 (shellCutoff X),
          (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))))
      ≤ 2 * X * (1 / X ^ 2) :=
    mul_le_mul_of_nonneg_left h4 (by linarith)
  have h6 : 2 * X * (1 / X ^ 2) = 2 / X := by
    field_simp
  have h7 := avgLow_regimeTerm_sum_le hX
  rw [h3] at hsum
  linarith

/-! ## The main theorems -/

/-- **Lower half of the averaging relation** (`prop:averaging-relation`,
reverse of eq. `shell-upper`), in explicit-constant form: for `X ≥ 10⁷`,

```
𝓑(X) − F(e^X) ≤ 4·(log X)²/X.
```

Budget: `1/X²` (𝓑-tail beyond `M = ⌊X³⌋`) + `2/X` (FKS shell-count errors,
`fks_shell_total_le`, applied once to the positive term and once to the loss)
+ `1/X²` (small-`m` collision losses) + `3(log X)²/X` (large-`m` collision
losses) + `1/X²` (bridge `F(e^X) ↔ (X/N)g(N)`), absorbed into `4(log X)²/X`
using `log X ≥ 16`. -/
theorem averaging_lower {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    B X - FReal (Real.exp X) ≤ 4 * Real.log X ^ 2 / X := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hA := avgLow_B_le_capped_sum hX
  have hB := avgLow_capped_sum_le hX
  have hbridge := abs_FReal_exp_sub_div_floor hX1
  have hbridge' : X / (⌊Real.exp X⌋₊ : ℝ) * g ⌊Real.exp X⌋₊
      ≤ FReal (Real.exp X) + X * Real.log 2 / Real.exp X := by
    have h := (abs_le.mp hbridge).1
    linarith
  have hsmall : X * Real.log 2 / Real.exp X ≤ 1 / X ^ 2 := by
    have hpoly := exp_gt_poly hX
    have hlog2 : Real.log 2 ≤ 1 := log_two_le_one
    rw [div_le_div_iff₀ (Real.exp_pos X) (by positivity : (0 : ℝ) < X ^ 2)]
    have hX36 : X ^ 3 ≤ X ^ 6 := pow_le_pow_right₀ hX1 (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hlog2
      (by positivity : (0 : ℝ) ≤ X ^ 3), pow_nonneg hX0.le 6]
  have hl16 := avgLow_sixteen_le_log hX
  have hfinal : 3 * Real.log X ^ 2 / X + (2 / X + 3 * (1 / X ^ 2))
      ≤ 4 * Real.log X ^ 2 / X := by
    have h1 : 1 / X ^ 2 ≤ 1 / X := by
      apply one_div_le_one_div_of_le hX0
      nlinarith
    have h3 : 5 * (1 / X) ≤ Real.log X ^ 2 * (1 / X) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    have h4 : Real.log X ^ 2 * (1 / X) + 3 * Real.log X ^ 2 / X
        = 4 * Real.log X ^ 2 / X := by ring
    have h5 : 2 / X = 2 * (1 / X) := by ring
    linarith
  linarith

/-- The lower half of eq. `averaging-relation` in terms of the error
`𝓡(X) = F(e^X) − 𝓑(X)`: `−4·(log X)²/X ≤ 𝓡(X)` for `X ≥ 10⁷`. -/
theorem neg_le_averagingError {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    -(4 * Real.log X ^ 2 / X) ≤ averagingError X := by
  have h := averaging_lower hX
  unfold averagingError
  linarith

end Erdos320
