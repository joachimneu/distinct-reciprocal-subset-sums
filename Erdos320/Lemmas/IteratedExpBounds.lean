import Erdos320.Defs.IteratedExp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Quantitative bounds for the iterated exponentials `E`, `D`, `J`, `q`

A toolkit of explicit numeric and structural estimates on the iterated
exponentials `E j u` and the §5 normalizations `D`, `J`, `q` of the
manuscript, needed by the §4–5 analytic development
(`prop:averaging-relation`, `lem:iteration-endpoint-matching`) and the §8
certificates.

Contents:

* **Elementary exponential estimates** usable at rational points:
  `pow_div_factorial_le_exp` (a single Taylor term is below `exp`),
  `two_mul_le_exp`, `sq_le_exp_half`.
* **Certified tower values**:
  `E_two_one_bounds` (`15.154 < E₂(1) < 15.155`, Lean-internal),
  `E_three_one_gt`/`E_three_one_lt` (`3.8·10⁶ < E₃(1) < 3.9·10⁶`;
  `sec:backward-reference` / `prop:constant-phase-backward`),
  and `E_three_two_gt` (`E₃(2) > 1.3·10²⁸`; `prop:constant-phase-backward`).
* **Structural comparisons on `u ≥ 1`**: growth of consecutive iterates
  (`E_add_one_le_E_succ`, `two_mul_E_le_E_add_two`), monotonicity and size of
  the gap `q` (`q_pos`, `q_le_one`, `q_antitoneOn`, `q_exp_one`,
  `q_succ_le_half`, `q_add_le_geometric`, `tsum_q_le`), the normalizations
  `D` and `J` (`one_le_D`, `D_le_D_succ`, `D_eq_D_pred_mul`, `D_ratio`,
  `J_eq`, `D_le_J`, `J_le_two_D`), and the super-exponentially small error
  factor `E_sq_div_le` behind the §5 remainder terms.

All numeric bounds are proved from `Real.exp_one_gt_d9`/`Real.exp_one_lt_d9`
together with exact-rational Taylor estimates (`Real.sum_le_exp_of_nonneg`
below, `Real.exp_bound'` above), so they are kernel-checked with no axioms
beyond Mathlib's.
-/

namespace Erdos320

/-! ## Elementary exponential estimates -/

/-- A single Taylor term is below the exponential: for `x ≥ 0` and any `n`,
`xⁿ/n! ≤ exp x`.  The workhorse for turning `exp` lower bounds into
polynomial inequalities. -/
theorem pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n / (n.factorial : ℝ) ≤ Real.exp x := by
  have hterm : x ^ n / (n.factorial : ℝ)
      ≤ ∑ i ∈ Finset.range (n + 1), x ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (f := fun i => x ^ i / (i.factorial : ℝ))
      (fun i _ => div_nonneg (pow_nonneg hx i) (Nat.cast_nonneg _))
      (Finset.self_mem_range_succ n)
  exact hterm.trans (Real.sum_le_exp_of_nonneg hx (n + 1))

/-- `2x ≤ exp x` for `x ≥ 0` (from the degree-2 Taylor polynomial):
the doubling estimate behind `two_mul_E_le_E_add_two`. -/
theorem two_mul_le_exp {x : ℝ} (hx : 0 ≤ x) : 2 * x ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  norm_num at h
  nlinarith [h, sq_nonneg (x - 1)]

/-- `x² ≤ exp (x/2)` once `x ≥ 20` (from the degree-4 Taylor term
`(x/2)⁴/24 = x⁴/384 ≥ x²`, valid as soon as `x² ≥ 384`).  The hypothesis
`20 ≤ x` is far weaker than needed at every use site: there `x = E j u`
exceeds `E₃(1) > 3.8·10⁶`. -/
theorem sq_le_exp_half {x : ℝ} (hx : 20 ≤ x) : x ^ 2 ≤ Real.exp (x / 2) := by
  have hx0 : (0 : ℝ) ≤ x / 2 := by linarith
  have h := pow_div_factorial_le_exp hx0 4
  have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num
  rw [hfac] at h
  have hx2 : (400 : ℝ) ≤ x ^ 2 := by nlinarith
  have hkey : x ^ 2 ≤ (x / 2) ^ 4 / 24 := by nlinarith [hx2, sq_nonneg x]
  linarith

/-! ## Certified tower values

The manuscript cites `E₃(1) > 3.8·10⁶` (§6, at eq. `Q47-tail-majorant`),
and `E₃(1) < 3.9·10⁶`, `E₃(2) > 1.3·10²⁸` (in `prop:constant-phase-backward`).
We derive all three from digit bounds on `e` via `E₂(1) = eᵉ ∈ (15.154, 15.155)`. -/

/-- `15.154 < E₂(1) < 15.155`, i.e. two-sided bounds on `eᵉ = 15.15426…`.
Lower bound: 18 Taylor terms of `exp` at `2.7182818283 < e`.  Upper bound:
`exp e < exp 2.7182818286 = (exp 1)² · exp 0.7182818286` with
`Real.exp_bound'` at the fractional part. -/
theorem E_two_one_bounds : (15.154 : ℝ) < E 2 1 ∧ E 2 1 < 15.155 := by
  have h21 : E 2 1 = Real.exp (Real.exp 1) := by
    have h : E 2 1 = Real.exp (E 1 1) := E_succ 1 1
    rw [h, show E 1 1 = Real.exp (E 0 1) from E_succ 0 1, E_zero]
  constructor
  · rw [h21]
    have hlow : ∑ i ∈ Finset.range 18, (2.7182818283 : ℝ) ^ i / (i.factorial : ℝ)
        ≤ Real.exp 2.7182818283 := Real.sum_le_exp_of_nonneg (by norm_num) 18
    have hnum : (15.154 : ℝ)
        < ∑ i ∈ Finset.range 18, (2.7182818283 : ℝ) ^ i / (i.factorial : ℝ) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    have hmono : Real.exp 2.7182818283 ≤ Real.exp (Real.exp 1) :=
      Real.exp_le_exp.mpr Real.exp_one_gt_d9.le
    linarith
  · rw [h21]
    have hmono : Real.exp (Real.exp 1) < Real.exp 2.7182818286 :=
      Real.exp_lt_exp.mpr Real.exp_one_lt_d9
    have hsplit : Real.exp (2.7182818286 : ℝ)
        = Real.exp 1 ^ 2 * Real.exp 0.7182818286 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have hfrac : Real.exp (0.7182818286 : ℝ) ≤ 2.050907 := by
      have hb := Real.exp_bound' (x := (0.7182818286 : ℝ)) (by norm_num)
        (by norm_num) (n := 12) (by norm_num)
      refine hb.trans ?_
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    have hsq : Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
    have hprod : Real.exp 1 ^ 2 * Real.exp 0.7182818286
        ≤ (2.7182818286 : ℝ) ^ 2 * 2.050907 :=
      mul_le_mul hsq hfrac (Real.exp_pos _).le (by positivity)
    have hnum : (2.7182818286 : ℝ) ^ 2 * 2.050907 < 15.155 := by norm_num
    linarith

/-- `E₃(1) > 3.8·10⁶`: the manuscript's lower bound on `E₃(1) = e^{eᵉ}`
(used around eq. `Q47-tail-majorant` in `sec:backward-reference`).
Proof: `E₃(1) > exp 15.154 = (exp 1)¹⁵ · exp 0.154
≥ 2.7182818283¹⁵ · 1.16646 > 3.8·10⁶`. -/
theorem E_three_one_gt : (3.8e6 : ℝ) < E 3 1 := by
  have h31 : E 3 1 = Real.exp (E 2 1) := E_succ 2 1
  have h1 : Real.exp (15.154 : ℝ) < Real.exp (E 2 1) :=
    Real.exp_lt_exp.mpr E_two_one_bounds.1
  have hsplit : Real.exp (15.154 : ℝ) = Real.exp 1 ^ 15 * Real.exp 0.154 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have hpow : (2.7182818283 : ℝ) ^ 15 ≤ Real.exp 1 ^ 15 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 15
  have hfrac : (1.16646 : ℝ) ≤ Real.exp 0.154 := by
    have hb : ∑ i ∈ Finset.range 4, (0.154 : ℝ) ^ i / (i.factorial : ℝ)
        ≤ Real.exp 0.154 := Real.sum_le_exp_of_nonneg (by norm_num) 4
    refine le_trans ?_ hb
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hprod : (2.7182818283 : ℝ) ^ 15 * 1.16646
      ≤ Real.exp 1 ^ 15 * Real.exp 0.154 :=
    mul_le_mul hpow hfrac (by norm_num) (by positivity)
  have hnum : (3.8e6 : ℝ) < (2.7182818283 : ℝ) ^ 15 * 1.16646 := by norm_num
  rw [h31]
  linarith

/-- `E₃(1) < 3.9·10⁶`: the manuscript's upper bound on `E₃(1)`
(used in the proof of `prop:constant-phase-backward`).  Proof:
`E₃(1) < exp 15.155 = (exp 1)¹⁵ · exp 0.155
≤ 2.7182818286¹⁵ · 1.1677 < 3.9·10⁶`. -/
theorem E_three_one_lt : E 3 1 < (3.9e6 : ℝ) := by
  have h31 : E 3 1 = Real.exp (E 2 1) := E_succ 2 1
  have h1 : Real.exp (E 2 1) < Real.exp (15.155 : ℝ) :=
    Real.exp_lt_exp.mpr E_two_one_bounds.2
  have hsplit : Real.exp (15.155 : ℝ) = Real.exp 1 ^ 15 * Real.exp 0.155 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have hpow : Real.exp 1 ^ 15 ≤ (2.7182818286 : ℝ) ^ 15 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 15
  have hfrac : Real.exp (0.155 : ℝ) ≤ 1.1677 := by
    have hb := Real.exp_bound' (x := (0.155 : ℝ)) (by norm_num) (by norm_num)
      (n := 5) (by norm_num)
    refine hb.trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hprod : Real.exp 1 ^ 15 * Real.exp 0.155
      ≤ (2.7182818286 : ℝ) ^ 15 * 1.1677 :=
    mul_le_mul hpow hfrac (Real.exp_pos _).le (by positivity)
  have hnum : (2.7182818286 : ℝ) ^ 15 * 1.1677 < 3.9e6 := by norm_num
  rw [h31]
  linarith

/-- `E₃(2) > 1.3·10²⁸`: the manuscript's lower bound on
`E₃(2) = exp (exp (exp 2))` (used in the proof of
`prop:constant-phase-backward`).  Proof:
`exp 2 > 5`, hence `exp (exp 2) > exp 5 > 65`, hence
`E₃(2) > exp 65 = (exp 1)⁶⁵ ≥ 2.7182818283⁶⁵ > 1.3·10²⁸`. -/
theorem E_three_two_gt : (1.3e28 : ℝ) < E 3 2 := by
  have h32 : E 3 2 = Real.exp (Real.exp (Real.exp 2)) := by
    have h3 : E 3 2 = Real.exp (E 2 2) := E_succ 2 2
    have h2 : E 2 2 = Real.exp (E 1 2) := E_succ 1 2
    have h1 : E 1 2 = Real.exp (E 0 2) := E_succ 0 2
    rw [h3, h2, h1, E_zero]
  have hexp2 : (5 : ℝ) < Real.exp 2 := by
    have hb : ∑ i ∈ Finset.range 6, (2 : ℝ) ^ i / (i.factorial : ℝ)
        ≤ Real.exp 2 := Real.sum_le_exp_of_nonneg (by norm_num) 6
    have hnum : (5 : ℝ) < ∑ i ∈ Finset.range 6, (2 : ℝ) ^ i / (i.factorial : ℝ) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    linarith
  have hexpexp2 : (65 : ℝ) < Real.exp (Real.exp 2) := by
    have hb : ∑ i ∈ Finset.range 8, (5 : ℝ) ^ i / (i.factorial : ℝ)
        ≤ Real.exp 5 := Real.sum_le_exp_of_nonneg (by norm_num) 8
    have hnum : (65 : ℝ) < ∑ i ∈ Finset.range 8, (5 : ℝ) ^ i / (i.factorial : ℝ) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    have hmono : Real.exp 5 ≤ Real.exp (Real.exp 2) := Real.exp_le_exp.mpr hexp2.le
    linarith
  have hpow : Real.exp (65 : ℝ) = Real.exp 1 ^ 65 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hc : (2.7182818283 : ℝ) ^ 65 ≤ Real.exp 1 ^ 65 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 65
  have hnum : (1.3e28 : ℝ) < (2.7182818283 : ℝ) ^ 65 := by norm_num
  have hchain : Real.exp (65 : ℝ) < Real.exp (Real.exp (Real.exp 2)) :=
    Real.exp_lt_exp.mpr hexpexp2
  rw [h32]
  linarith

/-! ## Growth of consecutive iterates -/

/-- Each exponential iterate exceeds the previous one by at least `1`:
`E j u + 1 ≤ E (j+1) u` (from `x + 1 ≤ exp x`; no hypothesis on `u`). -/
theorem E_add_one_le_E_succ (j : ℕ) (u : ℝ) : E j u + 1 ≤ E (j + 1) u := by
  rw [E_succ]
  exact Real.add_one_le_exp (E j u)

/-- Two exponentiation steps at least double the iterate when `u ≥ 1`:
`2·E j u ≤ E (j+2) u`.  This is the geometric-decay engine behind
`q_succ_le_half`. -/
theorem two_mul_E_le_E_add_two {u : ℝ} (hu : 1 ≤ u) (j : ℕ) :
    2 * E j u ≤ E (j + 2) u := by
  have h1 : 1 ≤ E j u := one_le_E_of_one_le hu j
  have h2 : E j u ≤ E (j + 1) u := (E_lt_E_succ j u).le
  have h3 : 2 * E (j + 1) u ≤ Real.exp (E (j + 1) u) :=
    two_mul_le_exp (by linarith)
  have h4 : E (j + 2) u = Real.exp (E (j + 1) u) := E_succ (j + 1) u
  linarith

/-! ## The gap `q_r = D_{r-2}/D_r` -/

/-- The gap `q r u` is positive for `u > 0`. -/
theorem q_pos {u : ℝ} (hu : 0 < u) (r : ℕ) : 0 < q r u := by
  unfold q
  exact one_div_pos.mpr (mul_pos (E_pos_of_pos hu _) (E_pos_of_pos hu _))

/-- The gap is at most `1` when `u ≥ 1` (each `E j u ≥ 1`). -/
theorem q_le_one {u : ℝ} (hu : 1 ≤ u) (r : ℕ) : q r u ≤ 1 := by
  have h3 := one_le_E_of_one_le hu (r - 3)
  have h4 := one_le_E_of_one_le hu (r - 4)
  have hprod : (1 : ℝ) ≤ E (r - 3) u * E (r - 4) u := by nlinarith
  unfold q
  rw [div_le_one (by linarith)]
  exact hprod

/-- For each fixed `r`, the gap `q r` is antitone in the phase `u` on
`[1, ∞)` (both `E`-factors in its denominator are increasing). -/
theorem q_antitoneOn (r : ℕ) : AntitoneOn (q r) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  have hpos : 0 < E (r - 3) x * E (r - 4) x :=
    mul_pos (E_pos_of_pos hx0 _) (E_pos_of_pos hx0 _)
  have hle : E (r - 3) x * E (r - 4) x ≤ E (r - 3) y * E (r - 4) y :=
    mul_le_mul (E_mono _ hxy) (E_mono _ hxy) (E_pos_of_pos hx0 _).le
      (E_pos_of_pos hy0 _).le
  unfold q
  exact one_div_le_one_div_of_le hpos hle

/-- Endpoint matching for the gap: `q r e = q (r+1) 1` for `r ≥ 4`
(the `q`-analogue of eq. `endpoint-matching`, from `E_exp_one`). -/
theorem q_exp_one {r : ℕ} (hr : 4 ≤ r) : q r (Real.exp 1) = q (r + 1) 1 := by
  unfold q
  rw [E_exp_one, E_exp_one, show r - 3 + 1 = r + 1 - 3 by omega,
    show r - 4 + 1 = r + 1 - 4 by omega]

/-- Consecutive gaps decay at least geometrically: `q (r+1) u ≤ q r u / 2`
for `u ≥ 1` and `r ≥ 4`.  (The manuscript uses this only for `r ≥ 7`,
where it holds a fortiori.)  The ratio is `E (r-4) u / E (r-2) u ≤ 1/2` by
`two_mul_E_le_E_add_two`. -/
theorem q_succ_le_half {u : ℝ} (hu : 1 ≤ u) {r : ℕ} (hr : 4 ≤ r) :
    q (r + 1) u ≤ q r u / 2 := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have h2 : 2 * E (r - 4) u ≤ E (r - 2) u := by
    have h := two_mul_E_le_E_add_two hu (r - 4)
    rwa [show r - 4 + 2 = r - 2 by omega] at h
  have e3 : 0 < E (r - 3) u := E_pos_of_pos hu0 _
  have e4 : 0 < E (r - 4) u := E_pos_of_pos hu0 _
  have key : E (r - 3) u * E (r - 4) u * 2 ≤ E (r - 2) u * E (r - 3) u := by
    nlinarith
  unfold q
  rw [show r + 1 - 3 = r - 2 by omega, show r + 1 - 4 = r - 3 by omega, div_div]
  exact one_div_le_one_div_of_le
    (mul_pos (mul_pos e3 e4) (by norm_num : (0 : ℝ) < 2)) key

/-- Iterated form of `q_succ_le_half`: `q (r+k) u ≤ (1/2)ᵏ · q r u` for
`u ≥ 1`, `r ≥ 4`. -/
theorem q_add_le_geometric {u : ℝ} (hu : 1 ≤ u) {r : ℕ} (hr : 4 ≤ r) (k : ℕ) :
    q (r + k) u ≤ (1 / 2) ^ k * q r u := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h := q_succ_le_half hu (show 4 ≤ r + k by omega) (u := u)
      calc q (r + (k + 1)) u = q (r + k + 1) u := by rw [← Nat.add_assoc]
        _ ≤ q (r + k) u / 2 := h
        _ ≤ ((1 / 2) ^ k * q r u) / 2 := by linarith
        _ = (1 / 2) ^ (k + 1) * q r u := by ring

/-- Geometric summation of the gaps: `∑_{k≥0} q (r+k) u ≤ 2 · q r u` for
`u ≥ 1`, `r ≥ 4`.  This is what makes the §5 iteration errors telescope
into a single `O(q_r)` term. -/
theorem tsum_q_le {u : ℝ} (hu : 1 ≤ u) {r : ℕ} (hr : 4 ≤ r) :
    ∑' k : ℕ, q (r + k) u ≤ 2 * q r u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hg : Summable fun k : ℕ => ((1 : ℝ) / 2) ^ k * q r u :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hle : ∀ k, q (r + k) u ≤ (1 / 2) ^ k * q r u := q_add_le_geometric hu hr
  have hq : Summable fun k : ℕ => q (r + k) u :=
    Summable.of_nonneg_of_le (fun k => (q_pos hu0 _).le) hle hg
  calc ∑' k : ℕ, q (r + k) u
      ≤ ∑' k : ℕ, ((1 : ℝ) / 2) ^ k * q r u := hq.tsum_le_tsum hle hg
    _ = (∑' k : ℕ, ((1 : ℝ) / 2) ^ k) * q r u := tsum_mul_right
    _ = 2 * q r u := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num

/-! ## The normalizations `D` and `J` -/

/-- `1 ≤ D r u` when `u ≥ 1` (each factor `E j u ≥ 1`). -/
theorem one_le_D {u : ℝ} (hu : 1 ≤ u) (r : ℕ) : 1 ≤ D r u :=
  Finset.one_le_prod fun j _ => one_le_E_of_one_le hu j

/-- `D` is monotone in the scale index when `u ≥ 1`:
`D r u ≤ D (r+1) u`. -/
theorem D_le_D_succ {u : ℝ} (hu : 1 ≤ u) (r : ℕ) : D r u ≤ D (r + 1) u := by
  rcases Nat.lt_or_ge r 2 with h | h
  · rw [D_of_le_two (by omega) u, D_of_le_two (by omega) u]
  · rw [D_succ h u]
    have h1 := one_le_D hu r
    have h2 := one_le_E_of_one_le hu (r - 2)
    nlinarith

/-- The one-step recursion read at the top factor: for `r ≥ 3`,
`D r u = D (r-1) u · E (r-3) u` (a reindexed `D_succ`). -/
theorem D_eq_D_pred_mul {r : ℕ} (hr : 3 ≤ r) (u : ℝ) :
    D r u = D (r - 1) u * E (r - 3) u := by
  have h := D_succ (r := r - 1) (by omega) u
  rwa [show r - 1 + 1 = r by omega, show r - 1 - 2 = r - 3 by omega] at h

/-- The ratio of consecutive normalizations: for `r ≥ 3` and `u > 0`,
`D (r-1) u / D r u = 1 / E (r-3) u`. -/
theorem D_ratio {u : ℝ} (hu : 0 < u) {r : ℕ} (hr : 3 ≤ r) :
    D (r - 1) u / D r u = 1 / E (r - 3) u := by
  have hD : D (r - 1) u ≠ 0 := (D_pos hu _).ne'
  rw [D_eq_D_pred_mul hr u, ← div_div, div_self hD]

/-- `J` as a multiplicative correction of `D`: for `r ≥ 3` and `u > 0`,
`J r u = D r u · (1 + 1/E (r-3) u)` (eq. `D-J`). -/
theorem J_eq {u : ℝ} (hu : 0 < u) {r : ℕ} (hr : 3 ≤ r) :
    J r u = D r u * (1 + 1 / E (r - 3) u) := by
  have hE : E (r - 3) u ≠ 0 := (E_pos_of_pos hu _).ne'
  unfold J
  rw [mul_add, mul_one, mul_one_div]
  congr 1
  rw [D_eq_D_pred_mul hr u, mul_div_assoc, div_self hE, mul_one]

/-- `D r u ≤ J r u` for `u > 0` (the endpoint-matching summand
`D (r-1) u` is positive). -/
theorem D_le_J {u : ℝ} (hu : 0 < u) (r : ℕ) : D r u ≤ J r u := by
  have h := D_pos hu (r - 1)
  unfold J
  linarith

/-- `J r u ≤ 2 · D r u` when `u ≥ 1` (since `D (r-1) u ≤ D r u`):
`J` and `D` agree up to a factor of `2`, uniformly. -/
theorem J_le_two_D {u : ℝ} (hu : 1 ≤ u) (r : ℕ) : J r u ≤ 2 * D r u := by
  have h : D (r - 1) u ≤ D r u := by
    cases r with
    | zero => exact le_rfl
    | succ n => exact D_le_D_succ hu n
  unfold J
  linarith

/-! ## Super-exponentially small error factors -/

/-- `E j u ² / E (j+1) u ≤ exp (−E j u / 2)` once `E j u ≥ 20`: the ratio
controlling the §5 remainder terms is super-exponentially small in the
iterate.  (At every use site `E j u > 3.8·10⁶`, so the hypothesis is
harmless.) -/
theorem E_sq_div_le {u : ℝ} {j : ℕ} (h : 20 ≤ E j u) :
    E j u ^ 2 / E (j + 1) u ≤ Real.exp (-(E j u) / 2) := by
  have h1 : E j u ^ 2 ≤ Real.exp (E j u / 2) := sq_le_exp_half h
  have h2 : Real.exp (-(E j u) / 2)
      = Real.exp (E j u / 2) / Real.exp (E j u) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [E_succ, h2]
  gcongr

end Erdos320
