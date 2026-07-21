/-
# Backward propagation for a constant phase function (`prop:constant-phase-backward`)

Formalizes the paper's Proposition "Backward propagation for a constant
phase function" (`\label{prop:constant-phase-backward}`, displayed equation
`eq:H4-Q4`): if the phase `Φ` were identically a
constant `C` on `[1, e]`, then on the window `U = E₃⁻¹([w₋, w₊])` (with
buffer `U⁺ = E₃⁻¹([0.999 w₋, 1.001 w₊]) ⊂ (1,2)`, `0.999 w₋ ≥ 9.7·10⁶`,
`1.001 w₊ ≤ 1.3·10²⁸`) the depth-4 averages satisfy

  `‖H̄₄ − C·Q₄*‖_U ≤ ‖ρ₄‖_{U⁺} + (1 + C)·exp(−w₋ / 110)`.

The proof follows the paper: the terminal input is the iteration tail
`|H̄_R/J_R − Φ| ≤ C₀ q_R` of `prop:phase` (`abs_Hbar_div_J_sub_phasePhi_le`),
which under `Φ ≡ C` bounds `H̄_R − C·Q_R*` at an arbitrarily high depth `R`;
the backward stability estimate (`lem:backward-stability`,
`backward_stability`) then transports this bound down one exponential depth
at a time, on intervals enlarged by the paper's radii
`h_s = E_{s-2}(a)^{-1/2} = exp(−E_{s-3}(a)/2)` (`s ≥ 6`),
`h₅ = exp(−w/20)`, `h₄ = exp(−w/100)`, whose total is dwarfed by the
`u`-distance from `U` to `∂U⁺`.  The three per-step losses are controlled by
the explicit `ρ`-bound `cor:explicit-high-rho` (`rhoDepth_lt_of_big`), the
reference-derivative bounds of eq. `reference-derivative-bound`
(`abs_deriv_Qref_sub_A_le`, and for depth 4 the `Q̃₄`-core comparison of
eq. `R7-tail`), and the growth of `h_s·inf a_s`.  Finally `R → ∞` removes
the terminal remainder (`abs_QrefLimit_sub_Qref`).

**Formalization notes.**
* The backward recursion is run directly with the *limit* reference
  functions `Q_s* = QrefLimit s` (using `(Q_{s+1}*)' = a_s Q_s*`,
  `hasDerivAt_QrefLimit_succ`), rather than with `Q_s^{[R]}` followed by a
  limit interchange as in the paper; this is equivalent (the paper's
  `lem:backward-reference-convergence` provides exactly this `C¹` limit)
  and shortens the ledger.  The depth `R` then enters only through the
  terminal comparison `|Q_R* − J_R| ≤ Rdefect + tail`.
* The paper's interval endpoints are spelled via `iteratedLog 3`; on the
  window `[9.7·10⁶, 1.3·10²⁸]` this is a two-sided inverse of `E 3`
  (`cpb_E3_iteratedLog3`).
* The terminal remainder is `δ_R = 4·(2C₀+10C)·exp(−3·E_{R−4}(a)/10) → 0`;
  the conclusion follows by letting `R → ∞` through
  `le_of_forall_gt_imp_ge_of_dense`.

All helpers are prefixed `cpb_`/`cpb` (constant-phase-backward).
-/
import Erdos320.Lemmas.Phase
import Erdos320.Lemmas.BackwardStability
import Erdos320.Lemmas.BackwardReferenceLimit
import Erdos320.Lemmas.ExplicitHighAveraging
import Erdos320.Defs.StoppingDepth

namespace Erdos320

/-! ## Elementary numeric exponential bounds -/

/-- `exp 16 ≤ 9.7·10⁶` (in fact `e¹⁶ ≈ 8.89·10⁶`). -/
theorem cpb_exp_sixteen_le : Real.exp 16 ≤ 9.7e6 := by
  have h : Real.exp (16 : ℝ) = Real.exp 1 ^ 16 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 16 ≤ (2.7182818286 : ℝ) ^ 16 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 16
    _ ≤ 9.7e6 := by norm_num

/-- `1.3·10²⁸ ≤ exp 65` (in fact `e⁶⁵ ≈ 1.69·10²⁸`). -/
theorem cpb_le_exp_sixtyfive : (1.3e28 : ℝ) ≤ Real.exp 65 := by
  have h : Real.exp (65 : ℝ) = Real.exp 1 ^ 65 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc (1.3e28 : ℝ) ≤ (2.7182818283 : ℝ) ^ 65 := by norm_num
    _ ≤ Real.exp 1 ^ 65 :=
        pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 65

/-- `65 ≤ exp 4.2` (in fact `e^{4.2} ≈ 66.7`). -/
theorem cpb_sixtyfive_le_exp : (65 : ℝ) ≤ Real.exp 4.2 := by
  have h4 : (54.5 : ℝ) ≤ Real.exp 4 := by
    have h : Real.exp (4 : ℝ) = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc (54.5 : ℝ) ≤ (2.7182818283 : ℝ) ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 :=
          pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 4
  have h02 : (1.2 : ℝ) ≤ Real.exp 0.2 := by
    have := Real.add_one_le_exp (0.2 : ℝ)
    linarith
  have hsplit : Real.exp (4.2 : ℝ) = Real.exp 4 * Real.exp 0.2 := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  calc (65 : ℝ) ≤ 54.5 * 1.2 := by norm_num
    _ ≤ Real.exp 4 * Real.exp 0.2 :=
        mul_le_mul h4 h02 (by norm_num) (Real.exp_pos _).le

/-- `666667 ≤ exp 14` (in fact `e¹⁴ ≈ 1.2·10⁶`). -/
theorem cpb_le_exp_fourteen : (666667 : ℝ) ≤ Real.exp 14 := by
  have h : Real.exp (14 : ℝ) = Real.exp 1 ^ 14 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc (666667 : ℝ) ≤ (2.7182818283 : ℝ) ^ 14 := by norm_num
    _ ≤ Real.exp 1 ^ 14 :=
        pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 14

/-- `288 ≤ exp 6` (in fact `e⁶ ≈ 403`). -/
theorem cpb_le_exp_six : (288 : ℝ) ≤ Real.exp 6 := by
  have h : Real.exp (6 : ℝ) = Real.exp 1 ^ 6 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc (288 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
    _ ≤ Real.exp 1 ^ 6 :=
        pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 6

/-- `8·10²⁶ ≤ exp 62` (in fact `e⁶² ≈ 8.4·10²⁶`). -/
theorem cpb_le_exp_sixtytwo : (8e26 : ℝ) ≤ Real.exp 62 := by
  have h : Real.exp (62 : ℝ) = Real.exp 1 ^ 62 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc (8e26 : ℝ) ≤ (2.7182818283 : ℝ) ^ 62 := by norm_num
    _ ≤ Real.exp 1 ^ 62 :=
        pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 62

/-- `10 ≤ exp 3` (in fact `e³ ≈ 20.1`). -/
theorem cpb_ten_le_exp_three : (10 : ℝ) ≤ Real.exp 3 := by
  have h : Real.exp (3 : ℝ) = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc (10 : ℝ) ≤ (2.7182818283 : ℝ) ^ 3 := by norm_num
    _ ≤ Real.exp 1 ^ 3 :=
        pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 3

/-- `2 ≤ exp 1`. -/
theorem cpb_two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  linarith [Real.exp_one_gt_d9]

/-- Combining exponentials with a prescribed exponent sum. -/
theorem cpb_exp_mul_exp {x y z : ℝ} (h : x + y = z) :
    Real.exp x * Real.exp y = Real.exp z := by
  rw [← Real.exp_add, h]

/-- `exp (−1) ≤ 1/2`. -/
theorem cpb_exp_neg_one_le : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := cpb_two_le_exp_one
  have hprod : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
    rw [cpb_exp_mul_exp (show (-1 : ℝ) + 1 = 0 by norm_num), Real.exp_zero]
  nlinarith [Real.exp_pos (-1 : ℝ)]

/-- `exp 2 ≤ 7.3890561`. -/
theorem cpb_exp_two_le : Real.exp 2 ≤ 7.3890561 := by
  have h : Real.exp (2 : ℝ) = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
    _ ≤ 7.3890561 := by norm_num

/-- `exp (exp 2) ≤ 1650` (in fact `e^{e²} ≈ 1618.2`). -/
theorem cpb_exp_exp_two_le : Real.exp (Real.exp 2) ≤ 1650 := by
  have h1 : Real.exp (Real.exp 2) ≤ Real.exp 7.389057 :=
    Real.exp_le_exp.mpr (cpb_exp_two_le.trans (by norm_num))
  have hsplit : Real.exp (7.389057 : ℝ) = Real.exp 1 ^ 7 * Real.exp 0.389057 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have hpow : Real.exp 1 ^ 7 ≤ (2.7182818286 : ℝ) ^ 7 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
  have hfrac : Real.exp (0.389057 : ℝ) ≤ 1.4767 := by
    have hb := Real.exp_bound' (x := (0.389057 : ℝ)) (by norm_num) (by norm_num)
      (n := 6) (by norm_num)
    refine hb.trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hprod : Real.exp 1 ^ 7 * Real.exp 0.389057
      ≤ (2.7182818286 : ℝ) ^ 7 * 1.4767 :=
    mul_le_mul hpow hfrac (Real.exp_pos _).le (by positivity)
  have hnum : (2.7182818286 : ℝ) ^ 7 * 1.4767 ≤ 1650 := by norm_num
  rw [hsplit] at h1
  linarith

/-! ## Iterated-logarithm window geometry -/

/-- `iteratedLog 3` in closed form. -/
theorem cpb_iteratedLog3_eq (x : ℝ) :
    iteratedLog 3 x = Real.log (Real.log (Real.log x)) := by
  have h3 : iteratedLog 3 x = Real.log (iteratedLog 2 x) := iteratedLog_succ 2 x
  have h2 : iteratedLog 2 x = Real.log (iteratedLog 1 x) := iteratedLog_succ 1 x
  have h1 : iteratedLog 1 x = Real.log (iteratedLog 0 x) := iteratedLog_succ 0 x
  rw [h3, h2, h1, iteratedLog_zero]

/-- `E 3` in closed form. -/
theorem cpb_E3_eq (t : ℝ) : E 3 t = Real.exp (Real.exp (Real.exp t)) := by
  have h3 : E 3 t = Real.exp (E 2 t) := E_succ 2 t
  have h2 : E 2 t = Real.exp (E 1 t) := E_succ 1 t
  have h1 : E 1 t = Real.exp (E 0 t) := E_succ 0 t
  rw [h3, h2, h1, E_zero]

/-- On the paper's window, `log x ≥ 16`. -/
theorem cpb_sixteen_le_log {x : ℝ} (hx : 9.7e6 ≤ x) : (16 : ℝ) ≤ Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [Real.le_log_iff_exp_le hx0]
  exact cpb_exp_sixteen_le.trans hx

/-- On the paper's window, `log x ≤ 65`. -/
theorem cpb_log_le_sixtyfive {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1.3e28) :
    Real.log x ≤ 65 := by
  rw [Real.log_le_iff_le_exp hx0]
  exact hx.trans cpb_le_exp_sixtyfive

/-- On the paper's window, `log₂ x ≤ 4.2`. -/
theorem cpb_loglog_le {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 65) : Real.log x ≤ 4.2 := by
  rw [Real.log_le_iff_le_exp hx0]
  exact hx.trans cpb_sixtyfive_le_exp

/-- `E 3 ∘ iteratedLog 3 = id` on `[9.7·10⁶, ∞)` (the tower of logs stays
positive there, so Mathlib's junk conventions never fire). -/
theorem cpb_E3_iteratedLog3 {x : ℝ} (hx : 9.7e6 ≤ x) :
    E 3 (iteratedLog 3 x) = x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hl1 : (16 : ℝ) ≤ Real.log x := cpb_sixteen_le_log hx
  have hl1p : (0 : ℝ) < Real.log x := by linarith
  have hl2 : (0 : ℝ) < Real.log (Real.log x) := Real.log_pos (by linarith)
  rw [cpb_iteratedLog3_eq, cpb_E3_eq, Real.exp_log hl2, Real.exp_log hl1p,
    Real.exp_log hx0]

/-- `iteratedLog 3` is monotone on the paper's window. -/
theorem cpb_iteratedLog3_mono {x y : ℝ} (hx : 9.7e6 ≤ x) (hxy : x ≤ y) :
    iteratedLog 3 x ≤ iteratedLog 3 y := by
  by_contra h
  push Not at h
  have := E_strictMono 3 h
  rw [cpb_E3_iteratedLog3 hx, cpb_E3_iteratedLog3 (hx.trans hxy)] at this
  linarith

/-- `1 < iteratedLog 3 x` on the paper's window (`E₃(1) < 3.9·10⁶`). -/
theorem cpb_one_lt_iteratedLog3 {x : ℝ} (hx : 9.7e6 ≤ x) :
    1 < iteratedLog 3 x := by
  have h1 : E 3 1 < E 3 (iteratedLog 3 x) := by
    rw [cpb_E3_iteratedLog3 hx]
    linarith [E_three_one_lt]
  exact (E_strictMono 3).lt_iff_lt.mp h1

/-- `iteratedLog 3 x ≤ 2` on the paper's window (`E₃(2) > 1.3·10²⁸`). -/
theorem cpb_iteratedLog3_le_two {x : ℝ} (hx : 9.7e6 ≤ x) (hx' : x ≤ 1.3e28) :
    iteratedLog 3 x ≤ 2 := by
  have h1 : E 3 (iteratedLog 3 x) < E 3 2 := by
    rw [cpb_E3_iteratedLog3 hx]
    linarith [E_three_two_gt]
  exact ((E_strictMono 3).lt_iff_lt.mp h1).le

/-- **Buffer geometry** (paper: `(E₃⁻¹)'(t) > 1/(24000 t)` on the window):
the `u`-distance between the `iteratedLog 3`-images is at least `1/273` of
the distance between the logarithms. -/
theorem cpb_iteratedLog3_sub_ge {x y : ℝ} (hx : 9.7e6 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 1.3e28) :
    (Real.log y - Real.log x) / 273 ≤ iteratedLog 3 y - iteratedLog 3 x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hl1 : (16 : ℝ) ≤ Real.log x := cpb_sixteen_le_log hx
  have hm1 : (16 : ℝ) ≤ Real.log y := cpb_sixteen_le_log (hx.trans hxy)
  have hm1' : Real.log y ≤ 65 := cpb_log_le_sixtyfive (by linarith) hy
  have h12 : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hl2 : (0 : ℝ) < Real.log (Real.log x) := Real.log_pos (by linarith)
  have hm2' : Real.log (Real.log y) ≤ 4.2 := cpb_loglog_le (by linarith) hm1'
  have h23 : Real.log (Real.log x) ≤ Real.log (Real.log y) :=
    Real.log_le_log (by linarith) h12
  -- level 2: `m1 − l1 ≤ 65·(m2 − l2)`
  have hstep1 : Real.log y - Real.log x
      ≤ 65 * (Real.log (Real.log y) - Real.log (Real.log x)) := by
    have hm1pos : (0 : ℝ) < Real.log y := by linarith
    have hkey : Real.log (Real.log x / Real.log y)
        ≤ Real.log x / Real.log y - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (by linarith) hm1pos)
    rw [Real.log_div (by linarith) (by linarith)] at hkey
    have hp1 := mul_le_mul_of_nonneg_right hkey hm1pos.le
    rw [sub_mul, sub_mul, div_mul_cancel₀ _ hm1pos.ne', one_mul] at hp1
    have hp2 : (0 : ℝ) ≤ (65 - Real.log y)
        * (Real.log (Real.log y) - Real.log (Real.log x)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hp1, hp2]
  -- level 3: `m2 − l2 ≤ 4.2·(m3 − l3)`
  have hstep2 : Real.log (Real.log y) - Real.log (Real.log x)
      ≤ 4.2 * (Real.log (Real.log (Real.log y))
        - Real.log (Real.log (Real.log x))) := by
    have hm2pos : (0 : ℝ) < Real.log (Real.log y) := lt_of_lt_of_le hl2 h23
    have hkey : Real.log (Real.log (Real.log x) / Real.log (Real.log y))
        ≤ Real.log (Real.log x) / Real.log (Real.log y) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hl2 hm2pos)
    rw [Real.log_div (by linarith) (by linarith)] at hkey
    have hp1 := mul_le_mul_of_nonneg_right hkey hm2pos.le
    rw [sub_mul, sub_mul, div_mul_cancel₀ _ hm2pos.ne', one_mul] at hp1
    have hp2 : (0 : ℝ) ≤ (4.2 - Real.log (Real.log y))
        * (Real.log (Real.log (Real.log y))
          - Real.log (Real.log (Real.log x))) := by
      have hmono : Real.log (Real.log (Real.log x))
          ≤ Real.log (Real.log (Real.log y)) := Real.log_le_log hl2 h23
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith [hp1, hp2]
  rw [cpb_iteratedLog3_eq, cpb_iteratedLog3_eq]
  linarith

/-! ## Monotonicity of the tower quantities in the phase -/

/-- `E j x ≥ 0` for `x ≥ 0`. -/
theorem cpb_E_nonneg {j : ℕ} {x : ℝ} (hx : 0 ≤ x) : 0 ≤ E j x := by
  cases j with
  | zero => simpa using hx
  | succ j => exact (Real.exp_pos _).le

/-- `a r` is monotone in the phase. -/
theorem cpb_a_mono (r : ℕ) {x y : ℝ} (hxy : x ≤ y) : a r x ≤ a r y :=
  Finset.prod_le_prod
    (fun _ hj => (E_pos_of_one_le (Finset.mem_Icc.mp hj).1 x).le)
    (fun j _ => E_mono j hxy)

/-- `D r` is monotone in the phase (on nonnegative phases). -/
theorem cpb_D_mono (r : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    D r x ≤ D r y :=
  Finset.prod_le_prod (fun _ _ => cpb_E_nonneg hx) (fun j _ => E_mono j hxy)

/-- `A s` is monotone in the phase (on nonnegative phases). -/
theorem cpb_A_mono (s : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    A s x ≤ A s y := by
  unfold A
  exact add_le_add le_rfl (Finset.sum_le_sum fun j _ => cpb_D_mono j hx hxy)

/-- Cross-phase index shift (`eq:compact-interval-comparison`,
via `E_j(y) ≤ E_j(e) = E_{j+1}(1) ≤ E_{j+1}(x)` for `y ≤ 2 < e ≤ e^x`):
`D r y ≤ D (r+1) x` for `1 ≤ x`, `0 ≤ y ≤ 2`. -/
theorem cpb_D_le_D_succ_shift {r : ℕ} (hr : 2 ≤ r) {x y : ℝ} (hx : 1 ≤ x)
    (hy0 : 0 ≤ y) (hy : y ≤ 2) : D r y ≤ D (r + 1) x := by
  have hprod : ∀ j, E j y ≤ E (j + 1) x := fun j => by
    calc E j y ≤ E j (Real.exp 1) := E_mono j (by linarith [cpb_two_le_exp_one])
      _ = E (j + 1) 1 := E_exp_one j
      _ ≤ E (j + 1) x := E_mono (j + 1) hx
  unfold D
  rw [show r + 1 - 2 = (r - 2) + 1 by omega, Finset.prod_range_succ']
  have h1 : ∏ j ∈ Finset.range (r - 2), E j y
      ≤ ∏ j ∈ Finset.range (r - 2), E (j + 1) x :=
    Finset.prod_le_prod (fun j _ => cpb_E_nonneg hy0) (fun j _ => hprod j)
  have h2 : (1 : ℝ) ≤ E 0 x := by simpa using hx
  have h3 : (0 : ℝ) ≤ ∏ j ∈ Finset.range (r - 2), E (j + 1) x :=
    Finset.prod_nonneg fun j _ => (E_pos_of_one_le (by omega) x).le
  nlinarith

/-! ## Growth helpers -/

/-- `E j 1 ≥ j + 1`. -/
theorem cpb_nat_add_one_le_E (j : ℕ) : (j : ℝ) + 1 ≤ E j 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h := E_add_one_le_E_succ j 1
      push_cast
      linarith

/-- Geometric domination of the tower partial sums:
`∑_{j ≤ m} E_j(u) ≤ 2 E_m(u)` for `u ≥ 1`. -/
theorem cpb_sum_E_le {u : ℝ} (hu : 1 ≤ u) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), E j u ≤ 2 * E m u := by
  induction m with
  | zero => simpa using by linarith
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have h2 : 2 * E m u ≤ E (m + 1) u := by
        rw [E_succ]
        exact two_mul_le_exp (cpb_E_nonneg (by linarith))
      linarith

/-- Explicit majorant of the normalization: `D s u ≤ 2 exp(2 E_{s-4}(u))`
for `1 ≤ u ≤ 2`, `s ≥ 4`. -/
theorem cpb_D_le_two_exp {s : ℕ} (hs : 4 ≤ s) {u : ℝ} (hu : 1 ≤ u)
    (hu2 : u ≤ 2) : D s u ≤ 2 * Real.exp (2 * E (s - 4) u) := by
  have hEsum : ∑ j ∈ Finset.range (s - 3), E j u ≤ 2 * E (s - 4) u := by
    have h := cpb_sum_E_le hu (s - 4)
    rwa [show s - 4 + 1 = s - 3 by omega] at h
  have hexp : Real.exp (∑ j ∈ Finset.range (s - 3), E j u)
      ≤ Real.exp (2 * E (s - 4) u) := Real.exp_le_exp.mpr hEsum
  have hDeq : D s u = (∏ j ∈ Finset.range (s - 3), E (j + 1) u) * E 0 u := by
    unfold D
    rw [show s - 2 = (s - 3) + 1 by omega, Finset.prod_range_succ']
  have hprod : ∏ j ∈ Finset.range (s - 3), E (j + 1) u
      = Real.exp (∑ j ∈ Finset.range (s - 3), E j u) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => E_succ j u
  rw [hDeq, hprod]
  have h0 : E 0 u = u := E_zero u
  have hpos : (0 : ℝ) < Real.exp (∑ j ∈ Finset.range (s - 3), E j u) :=
    Real.exp_pos _
  rw [h0]
  nlinarith [Real.exp_pos (2 * E (s - 4) u)]

/-- **The growth ledger of the Lipschitz step**: `24 E_k(2) + 36 ≤ E_{k+1}(1)`
for `k ≥ 2` (base: `E₂(2) < 1650` versus `E₃(1) > 3.8·10⁶`). -/
theorem cpb_growth {k : ℕ} (hk : 2 ≤ k) : 24 * E k 2 + 36 ≤ E (k + 1) 1 := by
  induction k, hk using Nat.le_induction with
  | base =>
      have hE22 : E 2 2 ≤ 1650 := by
        have h2 : E 2 2 = Real.exp (E 1 2) := E_succ 1 2
        have h1 : E 1 2 = Real.exp (E 0 2) := E_succ 0 2
        rw [h2, h1, E_zero]
        exact cpb_exp_exp_two_le
      have := E_three_one_gt
      linarith
  | succ k hk ih =>
      have hEsucc1 : E (k + 1 + 1) 1 = Real.exp (E (k + 1) 1) := E_succ (k + 1) 1
      have hEsucc2 : E (k + 1) 2 = Real.exp (E k 2) := E_succ k 2
      have hmono : Real.exp (24 * E k 2 + 36) ≤ Real.exp (E (k + 1) 1) :=
        Real.exp_le_exp.mpr ih
      have h24 : Real.exp (24 * E k 2) = Real.exp (E k 2) ^ 24 := by
        have h := Real.exp_nat_mul (E k 2) 24
        norm_num at h
        exact h
      have hsplit : Real.exp (24 * E k 2 + 36)
          = Real.exp (E k 2) ^ 24 * Real.exp 36 := by
        rw [Real.exp_add, h24]
      have hX1 : (1 : ℝ) ≤ E (k + 1) 2 := one_le_E_of_one_le (by norm_num) _
      have hXpow : E (k + 1) 2 ≤ E (k + 1) 2 ^ 24 := by
        calc E (k + 1) 2 = E (k + 1) 2 ^ 1 := (pow_one _).symm
          _ ≤ E (k + 1) 2 ^ 24 := pow_le_pow_right₀ hX1 (by norm_num)
      have h288 : (288 : ℝ) ≤ Real.exp 36 :=
        cpb_le_exp_six.trans (Real.exp_le_exp.mpr (by norm_num))
      have hpow_nonneg : (0 : ℝ) ≤ E (k + 1) 2 ^ 24 := by positivity
      have hkey : 24 * E (k + 1) 2 + 36 ≤ E (k + 1) 2 ^ 24 * Real.exp 36 := by
        nlinarith
      rw [hEsucc1]
      calc 24 * E (k + 1) 2 + 36 ≤ E (k + 1) 2 ^ 24 * Real.exp 36 := hkey
        _ = Real.exp (E k 2) ^ 24 * Real.exp 36 := by rw [hEsucc2]
        _ = Real.exp (24 * E k 2 + 36) := hsplit.symm
        _ ≤ Real.exp (E (k + 1) 1) := hmono

/-- Geometric domination of the derivative sum of `A_s`:
`∑_{j=3}^s a_{j-1} A_{j-1} ≤ 2 a_{s-1} A_{s-1}` for `u ≥ 1` (consecutive
terms grow by the factor `E_{j-2} ≥ 2`). -/
theorem cpb_sum_aA_le {s : ℕ} (hs : 3 ≤ s) {v : ℝ} (hv : 1 ≤ v) :
    ∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v
      ≤ 2 * (a (s - 1) v * A (s - 1) v) := by
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le one_pos hv
  induction s, hs using Nat.le_induction with
  | base =>
      rw [Finset.Icc_self, Finset.sum_singleton,
        show (3 : ℕ) - 1 = 2 from rfl, a_two, A_two]
      norm_num
  | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ n + 1)]
      have hidx : n + 1 - 1 = n := by omega
      rw [hidx]
      have hkey : 2 * (a (n - 1) v * A (n - 1) v) ≤ a n v * A n v := by
        have han : a n v = a (n - 1) v * E (n - 2) v := by
          have h := a_succ (r := n - 1) (by omega) v
          rwa [show n - 1 + 1 = n by omega, show n - 1 - 1 = n - 2 by omega] at h
        have hE2 : (2 : ℝ) ≤ E (n - 2) v := two_le_E (by omega) hv
        have hAm : A (n - 1) v ≤ A n v := A_mono_index hv0 (by omega)
        have hap : (0 : ℝ) < a (n - 1) v := a_pos _ v
        have hAp : (0 : ℝ) < A (n - 1) v := A_pos hv0 _
        rw [han]
        have h1 : a (n - 1) v * 2 ≤ a (n - 1) v * E (n - 2) v :=
          mul_le_mul_of_nonneg_left hE2 hap.le
        have h2 : a (n - 1) v * 2 * A (n - 1) v ≤ a (n - 1) v * 2 * A n v :=
          mul_le_mul_of_nonneg_left hAm (by nlinarith)
        have h3 : a (n - 1) v * 2 * A n v
            ≤ a (n - 1) v * E (n - 2) v * A n v :=
          mul_le_mul_of_nonneg_right h1 (A_pos hv0 n).le
        nlinarith [h2, h3]
      linarith [ih]

/-! ## The pointwise `ρ` bound (from `cor:explicit-high-rho`) -/

/-- Explicit recurrence-error bound: `|ρ_s(v)| ≤ exp(−E_{s-2}(v)/2)` for
`s ≥ 5`, `v ≥ 1` (`rhoDepth_lt_of_big` plus `10 x² ≤ e^{x/2}`). -/
theorem cpb_rho_le {s : ℕ} (hs : 5 ≤ s) {v : ℝ} (hv : 1 ≤ v) :
    |rhoDepth s v| ≤ Real.exp (-(E (s - 2) v) / 2) := by
  have hE4 : (8e26 : ℝ) ≤ E 4 1 := by
    have h41 : E 4 1 = Real.exp (E 3 1) := E_succ 3 1
    have h62 : Real.exp 62 ≤ Real.exp (E 3 1) :=
      Real.exp_le_exp.mpr (by linarith [E_three_one_gt])
    rw [h41]
    linarith [cpb_le_exp_sixtytwo]
  have hbig : (8e26 : ℝ) ≤ E (s - 1) v := by
    calc (8e26 : ℝ) ≤ E 4 1 := hE4
      _ ≤ E (s - 1) 1 := E_mono_depth le_rfl (by omega)
      _ ≤ E (s - 1) v := E_mono _ hv
  have hlt := rhoDepth_lt_of_big (by omega : 2 ≤ s) hbig
  have hxge : (62 : ℝ) ≤ E (s - 2) v := by
    calc (62 : ℝ) ≤ E 3 1 := by linarith [E_three_one_gt]
      _ ≤ E (s - 2) 1 := E_mono_depth le_rfl (by omega)
      _ ≤ E (s - 2) v := E_mono _ hv
  have hEs1 : E (s - 1) v = Real.exp (E (s - 2) v) := by
    have h := E_succ (s - 2) v
    rwa [show s - 2 + 1 = s - 1 by omega] at h
  set x := E (s - 2) v with hxdef
  have h10 : 10 * x ^ 2 ≤ Real.exp (x / 2) := by
    have hp := pow_div_factorial_le_exp (show (0 : ℝ) ≤ x / 2 by linarith) 4
    have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hfac] at hp
    have hx2 : (3844 : ℝ) ≤ x ^ 2 := by nlinarith
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2 - 3844)]
  have hbound : 10 * (E (s - 2) v ^ 2 / E (s - 1) v) ≤ Real.exp (-(x) / 2) := by
    rw [hEs1, ← hxdef]
    have hexp_pos : (0 : ℝ) < Real.exp x := Real.exp_pos x
    rw [show 10 * (x ^ 2 / Real.exp x) = 10 * x ^ 2 / Real.exp x by ring,
      div_le_iff₀ hexp_pos]
    calc 10 * x ^ 2 ≤ Real.exp (x / 2) := h10
      _ = Real.exp (-(x) / 2) * Real.exp x := by
          rw [← Real.exp_add]
          congr 1
          ring
  exact le_trans hlt.le hbound

/-! ## Lipschitz bounds for the limit reference functions -/

/-- Derivative bound for `Q_s*` at depths `s ≥ 5`:
`|(Q_s*)'(v)| ≤ 34 A_{s-1}(v) a_{s-1}(v) + 4` (via the finite-depth
comparison `abs_deriv_Qref_sub_A_le` at `R = s + 4` and the `C¹` tail). -/
theorem cpb_abs_QrefLimitIterDeriv_le {s : ℕ} (hs : 5 ≤ s) {v : ℝ}
    (hv : 1 ≤ v) :
    |QrefLimitIterDeriv 1 s v| ≤ 34 * (A (s - 1) v * a (s - 1) v) + 4 := by
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le one_pos hv
  have htail := abs_QrefLimitIterDeriv_sub_evalComb_le (s := s) (R := s + 4)
    (by omega) (by omega) (by omega) (m := 1) (by omega) hv
  rw [Function.iterate_one] at htail
  have htail4 : |QrefLimitIterDeriv 1 s v
      - evalComb (derivComb (QrefComb s (s + 4))) v| ≤ 4 := by
    refine htail.trans ?_
    have hE0 : (0 : ℝ) ≤ E (s + 4 - 4) v := cpb_E_nonneg (by linarith)
    calc 4 * Real.exp (-(E (s + 4 - 4) v) / 2) ≤ 4 * Real.exp 0 := by
          have := Real.exp_le_exp.mpr
            (show -(E (s + 4 - 4) v) / 2 ≤ 0 by linarith)
          linarith
      _ = 4 := by rw [Real.exp_zero]; norm_num
  have hQd : HasDerivAt (Qref s (s + 4))
      (evalComb (derivComb (QrefComb s (s + 4))) v) v := hasDerivAt_Qref hv0
  have hAd := hasDerivAt_A s v
  have hsub : HasDerivAt (fun x => Qref s (s + 4) x - A s x)
      (evalComb (derivComb (QrefComb s (s + 4))) v
        - ∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v) v := hQd.sub hAd
  have hd1 : |evalComb (derivComb (QrefComb s (s + 4))) v
      - ∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v|
      ≤ 32 * A (s - 1) v * a (s - 1) v / E (s - 2) v := by
    rw [← hsub.deriv]
    exact abs_deriv_Qref_sub_A_le hs (by omega) hv
  have hd1' : 32 * A (s - 1) v * a (s - 1) v / E (s - 2) v
      ≤ 32 * A (s - 1) v * a (s - 1) v :=
    div_le_self
      (mul_nonneg (mul_nonneg (by norm_num) (A_pos hv0 _).le) (a_pos _ v).le)
      (one_le_E_of_one_le hv _)
  have hsum_le := cpb_sum_aA_le (by omega : 3 ≤ s) hv
  have hsum_abs : |∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v|
      ≤ 2 * (a (s - 1) v * A (s - 1) v) := by
    rw [abs_of_nonneg (Finset.sum_nonneg fun j _ =>
      mul_nonneg (a_pos _ v).le (A_pos hv0 _).le)]
    exact hsum_le
  have h1 : |QrefLimitIterDeriv 1 s v|
      ≤ |QrefLimitIterDeriv 1 s v
          - evalComb (derivComb (QrefComb s (s + 4))) v|
        + |evalComb (derivComb (QrefComb s (s + 4))) v
            - ∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v|
        + |∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v| := by
    have heq : QrefLimitIterDeriv 1 s v
        = (QrefLimitIterDeriv 1 s v
            - evalComb (derivComb (QrefComb s (s + 4))) v)
          + ((evalComb (derivComb (QrefComb s (s + 4))) v
              - ∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v)
            + ∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v) := by ring
    calc |QrefLimitIterDeriv 1 s v|
        = |(QrefLimitIterDeriv 1 s v
              - evalComb (derivComb (QrefComb s (s + 4))) v)
            + ((evalComb (derivComb (QrefComb s (s + 4))) v
                - ∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v)
              + ∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v)| := by
          rw [← heq]
      _ ≤ |QrefLimitIterDeriv 1 s v
            - evalComb (derivComb (QrefComb s (s + 4))) v|
          + |(evalComb (derivComb (QrefComb s (s + 4))) v
              - ∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v)
            + ∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v| :=
          abs_add_le _ _
      _ ≤ _ := by
          have := abs_add_le
            (evalComb (derivComb (QrefComb s (s + 4))) v
              - ∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v)
            (∑ j ∈ Finset.Icc 3 s, a (j - 1) v * A (j - 1) v)
          linarith
  calc |QrefLimitIterDeriv 1 s v|
      ≤ 4 + 32 * A (s - 1) v * a (s - 1) v
          + 2 * (a (s - 1) v * A (s - 1) v) := by
        linarith [h1, htail4, hd1.trans hd1', hsum_abs]
    _ = 34 * (A (s - 1) v * a (s - 1) v) + 4 := by ring

/-- The depth `s ≥ 6` Lipschitz constant fits the radius:
`34 A_{s-1}(b) a_{s-1}(b) + 4 ≤ exp(E_{s-3}(a)/6)` for `1 ≤ a`,
`1 ≤ b ≤ 2` (paper: `log(1 + Lip(Q_s^{[R]})) ≤ 4E_{s-4}(b) ≤ E_{s-3}(a)/6`). -/
theorem cpb_Lip_le_exp {s : ℕ} (hs : 6 ≤ s) {aa bb : ℝ} (haa : 1 ≤ aa)
    (hbb1 : 1 ≤ bb) (hbb2 : bb ≤ 2) :
    34 * (A (s - 1) bb * a (s - 1) bb) + 4 ≤ Real.exp (E (s - 3) aa / 6) := by
  have hbb0 : (0 : ℝ) < bb := by linarith
  -- reduce to `72 D_s(b)²`
  have hA : A (s - 1) bb ≤ 2 * D (s - 1) bb := A_le_two_D (by omega) hbb1
  have ha : a (s - 1) bb ≤ D s bb := by
    have h := a_eq_D_succ_div (u := bb) (by positivity) (r := s - 1) (by omega)
    rw [show s - 1 + 1 = s by omega] at h
    rw [h]
    exact div_le_self (D_pos hbb0 s).le hbb1
  have hDD : D (s - 1) bb ≤ D s bb := by
    have h := D_le_D_succ hbb1 (s - 1)
    rwa [show s - 1 + 1 = s by omega] at h
  have hDpos : (0 : ℝ) < D s bb := D_pos hbb0 s
  have hD1 : (1 : ℝ) ≤ D s bb := one_le_D hbb1 s
  have hApos : (0 : ℝ) < A (s - 1) bb := A_pos hbb0 _
  have hapos : (0 : ℝ) < a (s - 1) bb := a_pos _ bb
  have hstep1 : 34 * (A (s - 1) bb * a (s - 1) bb) + 4 ≤ 72 * D s bb ^ 2 := by
    have hDD' : (0 : ℝ) < D (s - 1) bb := D_pos hbb0 _
    nlinarith
  -- `D_s(b)² ≤ 4 exp(4 E_{s-4}(b))`
  have hDexp : D s bb ≤ 2 * Real.exp (2 * E (s - 4) bb) :=
    cpb_D_le_two_exp (by omega) hbb1 hbb2
  have hsq : D s bb ^ 2 ≤ 4 * Real.exp (4 * E (s - 4) bb) := by
    have hsplit : Real.exp (2 * E (s - 4) bb) * Real.exp (2 * E (s - 4) bb)
        = Real.exp (4 * E (s - 4) bb) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith [Real.exp_pos (2 * E (s - 4) bb)]
  -- the growth ledger
  have hgrow : 24 * E (s - 4) bb + 36 ≤ E (s - 3) aa := by
    have h1 : E (s - 4) bb ≤ E (s - 4) 2 := E_mono _ hbb2
    have h2 : 24 * E (s - 4) 2 + 36 ≤ E (s - 4 + 1) 1 := cpb_growth (by omega)
    have h3 : E (s - 4 + 1) 1 ≤ E (s - 3) 1 := by
      rw [show s - 4 + 1 = s - 3 by omega]
    have h4 : E (s - 3) 1 ≤ E (s - 3) aa := E_mono _ haa
    linarith
  have hfinal : 288 * Real.exp (4 * E (s - 4) bb)
      ≤ Real.exp (E (s - 3) aa / 6) := by
    have h6 : 4 * E (s - 4) bb + 6 ≤ E (s - 3) aa / 6 := by linarith
    calc 288 * Real.exp (4 * E (s - 4) bb)
        ≤ Real.exp 6 * Real.exp (4 * E (s - 4) bb) :=
          mul_le_mul_of_nonneg_right cpb_le_exp_six (Real.exp_pos _).le
      _ = Real.exp (4 * E (s - 4) bb + 6) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (E (s - 3) aa / 6) := Real.exp_le_exp.mpr h6
  nlinarith [Real.exp_pos (4 * E (s - 4) bb)]

/-! ## Depth-4 Lipschitz bound via the `Q̃₄` comb -/

/-- Size invariant for `BrefComb 5` (re-derivation of the library's private
`BrefComb_five_sizeBound`). -/
theorem cpb_BrefComb_five_sizeBound : CombSizeBound 4 12 12 (BrefComb 5) :=
  ((AComb_sizeBound (by norm_num : 2 ≤ 5)).mono_t
    (by norm_num)).backward_step (by norm_num)

/-- Size invariant for the reference core `Q̃₄`. -/
theorem cpb_QrefCore4Comb_sizeBound : CombSizeBound 4 21 192 QrefCore4Comb := by
  have hadd : CombSizeBound 4 12 16 (AComb 5 + BrefComb 5) :=
    (((AComb_sizeBound (by norm_num : 2 ≤ 5)).mono_t (by norm_num)).add
      cpb_BrefComb_five_sizeBound).mono (by norm_num) (by norm_num)
  exact (hadd.derivComb_step.shiftComb_step (by norm_num)).mono
    (by norm_num) (by norm_num)

/-- Size invariant for `Q̃₄'`. -/
theorem cpb_derivCore_sizeBound :
    CombSizeBound 4 26 4032 (derivComb QrefCore4Comb) :=
  cpb_QrefCore4Comb_sizeBound.derivComb_step

/-- Evaluation bound for `Q̃₄'`: `|Q̃₄'(u)| ≤ 4032 E₃(u)²⁶` for `u ≥ 1`. -/
theorem cpb_abs_eval_derivCore_le {u : ℝ} (hu : 1 ≤ u) :
    |evalComb (derivComb QrefCore4Comb) u| ≤ 4032 * E 3 u ^ 26 := by
  have hE1 : (1 : ℝ) ≤ E 3 u := one_le_E_of_one_le hu 3
  have hb := abs_evalComb_le hu hE1 (P := derivComb QrefCore4Comb)
    (fun ν hν j _ hpos => by
      have h := cpb_derivCore_sizeBound.pos_index_le ν hν j hpos
      exact E_mono_depth hu (by omega))
  refine hb.trans ?_
  have hl : ((l1Norm (derivComb QrefCore4Comb) : ℕ) : ℝ) ≤ 4032 := by
    exact_mod_cast cpb_derivCore_sizeBound.l1Norm_le
  have hd : E 3 u ^ combPosDeg (derivComb QrefCore4Comb) ≤ E 3 u ^ 26 :=
    pow_le_pow_right₀ hE1 (le_trans (combPosDeg_le_combHeight _)
      cpb_derivCore_sizeBound.combHeight_le)
  exact mul_le_mul hl hd (by positivity) (by norm_num)

/-- Derivative bound for `Q₄*`: `|(Q₄*)'(v)| ≤ 4033 E₃(v)²⁶` for `v ≥ 1`
(the `Q̃₄`-core bound plus the eq. `R7-tail` correction). -/
theorem cpb_abs_QrefLimitIterDeriv_four_le {v : ℝ} (hv : 1 ≤ v) :
    |QrefLimitIterDeriv 1 4 v| ≤ 4033 * E 3 v ^ 26 := by
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le one_pos hv
  have h1 := abs_QrefLimitIterDeriv_one_four_sub_deriv_core_le hv
  have h2 : deriv QrefCore4 v = evalComb (derivComb QrefCore4Comb) v :=
    deriv_QrefCore4_eq hv0
  have h3 := cpb_abs_eval_derivCore_le hv
  have hexp : Real.exp (-(3.7e6 : ℝ)) ≤ 1 := by
    calc Real.exp (-(3.7e6 : ℝ)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by norm_num)
      _ = 1 := Real.exp_zero
  have hE1 : (1 : ℝ) ≤ E 3 v ^ 26 :=
    one_le_pow₀ (one_le_E_of_one_le hv 3)
  have hsplit : |QrefLimitIterDeriv 1 4 v|
      ≤ |QrefLimitIterDeriv 1 4 v - deriv QrefCore4 v|
        + |deriv QrefCore4 v| := by
    have h := abs_add_le (QrefLimitIterDeriv 1 4 v - deriv QrefCore4 v)
      (deriv QrefCore4 v)
    rw [show QrefLimitIterDeriv 1 4 v - deriv QrefCore4 v + deriv QrefCore4 v
      = QrefLimitIterDeriv 1 4 v by ring] at h
    exact h
  have h3' : |deriv QrefCore4 v| ≤ 4032 * E 3 v ^ 26 := by
    rw [h2]
    exact h3
  calc |QrefLimitIterDeriv 1 4 v|
      ≤ Real.exp (-(3.7e6 : ℝ)) + 4032 * E 3 v ^ 26 := by
        linarith [hsplit, h1, h3']
    _ ≤ 4033 * E 3 v ^ 26 := by linarith

/-! ## The generic backward transfer step -/

/-- **One backward stability application with the limit references**
(`lem:backward-stability` instantiated at `H_s = H̄_s`, `Q_s = Q_s*`,
using `(Q_{s+1}*)' = a_s Q_s*` from `lem:backward-reference-convergence`):
on a window `[lo−h, hi+h] ⊂ (1, ∞)`, a bound `Zn` at depth `s+1` descends
to `ρB + C·Lip·h + 2Zn/(h·aInf)` at depth `s`. -/
theorem cpb_backward_step {C : ℝ} (hC : 0 ≤ C) {s : ℕ} (hs : 4 ≤ s)
    {lo hi h aInf : ℝ} (hh : 0 < h) (hlohi : lo ≤ hi) (hwin1 : 1 < lo - h)
    (haInf : 0 < aInf) (ha : ∀ v ∈ Set.Icc (lo - h) (hi + h), aInf ≤ a s v)
    {Lip : ℝ} (hLip : 0 ≤ Lip)
    (hQd : ∀ v ∈ Set.Icc (lo - h) (hi + h), |QrefLimitIterDeriv 1 s v| ≤ Lip)
    {ρB : ℝ} (hρB : ∀ v ∈ Set.Icc (lo - h) (hi + h), |rhoDepth s v| ≤ ρB)
    {Zn : ℝ} (hZn : ∀ v ∈ Set.Icc (lo - h) (hi + h),
      |Hbar (s + 1) v - C * QrefLimit (s + 1) v| ≤ Zn) :
    ∀ u ∈ Set.Icc lo hi,
      |Hbar s u - C * QrefLimit s u|
        ≤ ρB + C * Lip * h + 2 * Zn / (h * aInf) := by
  have hone : ∀ v ∈ Set.Icc (lo - h) (hi + h), (1 : ℝ) < v :=
    fun v hv => lt_of_lt_of_le hwin1 hv.1
  have hcont : ContinuousOn (fun t => a s t * QrefLimit s t)
      (Set.Icc (lo - h) (hi + h)) := fun t ht =>
    ((continuous_a s).continuousAt.mul
      ((hasDerivAt_QrefLimit hs (hone t ht)).differentiableAt.continuousAt)).continuousWithinAt
  have huIcc : Set.uIcc (lo - h) (hi + h) = Set.Icc (lo - h) (hi + h) :=
    Set.uIcc_of_le (by linarith)
  refine backward_stability hh hC (a s) (Hbar s) (QrefLimit s) (Hbar (s + 1))
    (QrefLimit (s + 1)) (rhoDepth s) haInf ha
    ((Hbar_mono s).monotoneOn _) hLip ?_ hρB ?_ ?_
    (intervalIntegrable_recurrenceIntegrand (by omega) (lo - h) (hi + h)) ?_ hZn
  · -- two-point Lipschitz bound for `Q_s*` from the derivative bound
    intro v hv v' hv'
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := QrefLimit s) (f' := QrefLimitIterDeriv 1 s)
      (s := Set.Icc (lo - h) (hi + h))
      (fun x hx => (hasDerivAt_QrefLimit hs (hone x hx)).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact hQd x hx)
      (convex_Icc _ _) hv' hv
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  · -- integral form of `H̄_{s+1}' = a_s (H̄_s + ρ_s)`
    intro x _ y _ hxy
    exact Hbar_succ_sub_eq_integral (by omega) hxy
  · -- integral form of `(Q_{s+1}*)' = a_s Q_s*` (FTC)
    intro x hx y hy hxy
    have hsub : Set.uIcc x y ⊆ Set.Icc (lo - h) (hi + h) := by
      rw [Set.uIcc_of_le hxy]
      exact Set.Icc_subset_Icc hx.1 hy.2
    have hderiv : ∀ t ∈ Set.uIcc x y,
        HasDerivAt (QrefLimit (s + 1)) (a s t * QrefLimit s t) t :=
      fun t ht => hasDerivAt_QrefLimit_succ hs (hone t (hsub ht))
    have hint : IntervalIntegrable (fun t => a s t * QrefLimit s t)
        MeasureTheory.volume x y :=
      (hcont.mono hsub).intervalIntegrable
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint).symm
  · -- integrability of `a_s Q_s*` on the window
    exact (hcont.mono huIcc.subset).intervalIntegrable

/-! ## The radii and slack of the nested intervals -/

/-- The paper's enlargement radii: `h₄ = exp(−w/100)`, `h₅ = exp(−w/20)`,
`h_s = E_{s-2}(a)^{-1/2} = exp(−E_{s-3}(a)/2)` for `s ≥ 6`, with
`w = E₃(a)`. -/
noncomputable def cpbRadius (aa : ℝ) (s : ℕ) : ℝ :=
  if s ≤ 4 then Real.exp (-(E 3 aa) / 100)
  else if s = 5 then Real.exp (-(E 3 aa) / 20)
  else Real.exp (-(E (s - 3) aa) / 2)

/-- Cumulative slack `σ_s = ∑_{j=4}^{s-1} h_j`: the total enlargement of
`I_s^{(R)}` over `I₄ = U`. -/
noncomputable def cpbSlack (aa : ℝ) (s : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 4 s, cpbRadius aa j

theorem cpb_radius_pos (aa : ℝ) (s : ℕ) : 0 < cpbRadius aa s := by
  unfold cpbRadius
  split
  · exact Real.exp_pos _
  · split <;> exact Real.exp_pos _

theorem cpb_radius_four (aa : ℝ) : cpbRadius aa 4 = Real.exp (-(E 3 aa) / 100) := by
  unfold cpbRadius
  norm_num

theorem cpb_radius_five (aa : ℝ) : cpbRadius aa 5 = Real.exp (-(E 3 aa) / 20) := by
  unfold cpbRadius
  norm_num

theorem cpb_radius_of_six_le (aa : ℝ) {s : ℕ} (hs : 6 ≤ s) :
    cpbRadius aa s = Real.exp (-(E (s - 3) aa) / 2) := by
  unfold cpbRadius
  rw [if_neg (by omega), if_neg (by omega)]

theorem cpb_slack_four (aa : ℝ) : cpbSlack aa 4 = 0 := by
  unfold cpbSlack
  rw [Finset.Ico_self, Finset.sum_empty]

theorem cpb_slack_succ (aa : ℝ) {s : ℕ} (hs : 4 ≤ s) :
    cpbSlack aa (s + 1) = cpbSlack aa s + cpbRadius aa s :=
  Finset.sum_Ico_succ_top hs _

theorem cpb_slack_nonneg (aa : ℝ) (s : ℕ) : 0 ≤ cpbSlack aa s :=
  Finset.sum_nonneg fun j _ => (cpb_radius_pos aa j).le

/-- The total slack is below `2 exp(−w/100)` (paper: "the sum of the radii
is less than `2exp(−w/100)`"). -/
theorem cpb_slack_le (aa : ℝ) (haa : 1 ≤ aa) (hw : 9.7e6 ≤ E 3 aa) (s : ℕ) :
    cpbSlack aa s ≤ 2 * Real.exp (-(E 3 aa) / 100) := by
  -- the tail over depths `≥ 6` is geometrically dominated
  have htail : ∀ t, 6 ≤ t →
      (∑ j ∈ Finset.Ico 6 t, cpbRadius aa j)
        + 2 * Real.exp (-(E (t - 3) aa) / 2)
      ≤ 2 * Real.exp (-(E 3 aa) / 2) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
        rw [Finset.Ico_self, Finset.sum_empty, zero_add]
    | succ n hn ih =>
        rw [Finset.sum_Ico_succ_top (by omega : 6 ≤ n)]
        have hrad : cpbRadius aa n = Real.exp (-(E (n - 3) aa) / 2) :=
          cpb_radius_of_six_le aa hn
        have hhalf : 2 * Real.exp (-(E (n + 1 - 3) aa) / 2)
            ≤ Real.exp (-(E (n - 3) aa) / 2) := by
          have hdouble : 2 * E (n - 3) aa ≤ E (n - 2) aa := by
            have h := two_mul_le_exp (cpb_E_nonneg (by linarith : (0:ℝ) ≤ aa)
              (j := n - 3))
            have hE : E (n - 2) aa = Real.exp (E (n - 3) aa) := by
              have h' := E_succ (n - 3) aa
              rwa [show n - 3 + 1 = n - 2 by omega] at h'
            rw [hE]
            exact h
          have hEbig : 9.7e6 ≤ E (n - 3) aa := by
            calc (9.7e6 : ℝ) ≤ E 3 aa := hw
              _ ≤ E (n - 3) aa := E_mono_depth haa (by omega)
          have hidx : n + 1 - 3 = n - 2 := by omega
          rw [hidx]
          calc 2 * Real.exp (-(E (n - 2) aa) / 2)
              ≤ 2 * Real.exp (-(2 * E (n - 3) aa) / 2) := by
                have := Real.exp_le_exp.mpr
                  (show -(E (n - 2) aa) / 2 ≤ -(2 * E (n - 3) aa) / 2 by linarith)
                linarith
            _ = 2 * (Real.exp (-(E (n - 3) aa) / 2)
                  * Real.exp (-(E (n - 3) aa) / 2)) := by
                rw [cpb_exp_mul_exp (show -(E (n - 3) aa) / 2
                  + -(E (n - 3) aa) / 2 = -(2 * E (n - 3) aa) / 2 by ring)]
            _ ≤ Real.exp (-(E (n - 3) aa) / 2) := by
                have hsm : Real.exp (-(E (n - 3) aa) / 2) ≤ 1 / 2 := by
                  calc Real.exp (-(E (n - 3) aa) / 2)
                      ≤ Real.exp (-1 : ℝ) :=
                        Real.exp_le_exp.mpr (by linarith)
                    _ ≤ 1 / 2 := cpb_exp_neg_one_le
                nlinarith [mul_le_mul_of_nonneg_left hsm
                  (Real.exp_pos (-(E (n - 3) aa) / 2)).le]
        rw [hrad]
        linarith
  -- monotone extension to all `s`
  have hmono : cpbSlack aa s ≤ cpbSlack aa (max s 6) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico le_rfl (le_max_left _ _))
      (fun j _ _ => (cpb_radius_pos aa j).le)
  have h6 : 6 ≤ max s 6 := le_max_right _ _
  have h56 : (∑ j ∈ Finset.Ico 4 6, cpbRadius aa j)
      = cpbRadius aa 4 + cpbRadius aa 5 := by
    have h1 : (∑ j ∈ Finset.Ico 4 6, cpbRadius aa j)
        = (∑ j ∈ Finset.Ico 4 5, cpbRadius aa j) + cpbRadius aa 5 :=
      Finset.sum_Ico_succ_top (by norm_num) _
    have h2 : (∑ j ∈ Finset.Ico 4 5, cpbRadius aa j)
        = (∑ j ∈ Finset.Ico 4 4, cpbRadius aa j) + cpbRadius aa 4 :=
      Finset.sum_Ico_succ_top (by norm_num) _
    rw [h1, h2, Finset.Ico_self, Finset.sum_empty, zero_add]
  have hsplit : cpbSlack aa (max s 6)
      = cpbRadius aa 4 + cpbRadius aa 5
        + ∑ j ∈ Finset.Ico 6 (max s 6), cpbRadius aa j := by
    unfold cpbSlack
    rw [← Finset.sum_Ico_consecutive _ (by omega : 4 ≤ 6) h6, h56]
  have htail' : ∑ j ∈ Finset.Ico 6 (max s 6), cpbRadius aa j
      ≤ 2 * Real.exp (-(E 3 aa) / 2) := by
    have h := htail (max s 6) h6
    have := (Real.exp_pos (-(E (max s 6 - 3) aa) / 2)).le
    linarith
  -- the scalar comparison at `w ≥ 9.7e6`
  have h20 : Real.exp (-(E 3 aa) / 20) ≤ (1 / 2) * Real.exp (-(E 3 aa) / 100) := by
    have h2exp : (2 : ℝ) ≤ Real.exp (E 3 aa / 25) := by
      have := Real.add_one_le_exp (E 3 aa / 25)
      linarith
    have hprod : Real.exp (-(E 3 aa) / 100)
        = Real.exp (E 3 aa / 25) * Real.exp (-(E 3 aa) / 20) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith [Real.exp_pos (-(E 3 aa) / 20)]
  have h2' : 2 * Real.exp (-(E 3 aa) / 2)
      ≤ (1 / 2) * Real.exp (-(E 3 aa) / 100) := by
    have h4exp : (4 : ℝ) ≤ Real.exp (E 3 aa * (49 / 100)) := by
      have := Real.add_one_le_exp (E 3 aa * (49 / 100))
      linarith
    have hprod : Real.exp (-(E 3 aa) / 100)
        = Real.exp (E 3 aa * (49 / 100)) * Real.exp (-(E 3 aa) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith [Real.exp_pos (-(E 3 aa) / 2)]
  calc cpbSlack aa s ≤ cpbSlack aa (max s 6) := hmono
    _ = cpbRadius aa 4 + cpbRadius aa 5
        + ∑ j ∈ Finset.Ico 6 (max s 6), cpbRadius aa j := hsplit
    _ ≤ Real.exp (-(E 3 aa) / 100) + (1 / 2) * Real.exp (-(E 3 aa) / 100)
        + (1 / 2) * Real.exp (-(E 3 aa) / 100) := by
        rw [cpb_radius_four, cpb_radius_five]
        have := htail'.trans h2'
        linarith
    _ = 2 * Real.exp (-(E 3 aa) / 100) := by ring

/-! ## The terminal bound at depth `R` -/

/-- **Terminal comparison** (paper eq. `terminal-error`, adapted to `Q_R*`):
under `Φ ≡ C`, on `[1, bb] ⊂ [1, 2]`,
`|H̄_R(v) − C·Q_R*(v)| ≤ (2C₀ + 10C)·D_{R-2}(bb)`. -/
theorem cpb_terminal_bound {C C₀ : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hconst : ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), phasePhi u = C)
    {r₁ R : ℕ}
    (htail : ∀ r, r₁ ≤ r → ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      |Hbar r u / J r u - phasePhi u| ≤ C₀ * q r u)
    (hR : 10 ≤ R) (hr₁ : r₁ ≤ R)
    {bb v : ℝ} (hbb2 : bb ≤ 2) (hv1 : 1 ≤ v) (hvbb : v ≤ bb) :
    |Hbar R v - C * QrefLimit R v| ≤ (2 * C₀ + 10 * C) * D (R - 2) bb := by
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le one_pos hv1
  have hbb1 : (1 : ℝ) ≤ bb := hv1.trans hvbb
  have hve : v ≤ Real.exp 1 := by linarith [cpb_two_le_exp_one]
  have hvIcc : v ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨hv1, hve⟩
  have hDbb : (1 : ℝ) ≤ D (R - 2) bb := one_le_D hbb1 _
  have hDvbb : D (R - 2) v ≤ D (R - 2) bb := cpb_D_mono _ (by linarith) hvbb
  have hJ : (0 : ℝ) < J R v := J_pos hv0 R
  have hq : (0 : ℝ) < q R v := q_pos hv0 R
  have hDq : D R v * q R v = D (R - 2) v := by
    rw [q_eq_D_ratio hv0 (by omega), mul_comm,
      div_mul_cancel₀ _ (D_pos hv0 R).ne']
  -- piece 1: `|H̄_R − C J_R| ≤ 2C₀ D_{R-2}(bb)`
  have ht := htail R hr₁ v hvIcc
  rw [hconst v hvIcc] at ht
  have h1 : |Hbar R v - C * J R v| ≤ 2 * C₀ * D (R - 2) bb := by
    have heq : Hbar R v - C * J R v = J R v * (Hbar R v / J R v - C) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hJ]
    calc J R v * |Hbar R v / J R v - C| ≤ J R v * (C₀ * q R v) :=
          mul_le_mul_of_nonneg_left ht hJ.le
      _ ≤ 2 * D R v * (C₀ * q R v) :=
          mul_le_mul_of_nonneg_right (J_le_two_D hv1 R) (by positivity)
      _ = 2 * C₀ * (D R v * q R v) := by ring
      _ = 2 * C₀ * D (R - 2) v := by rw [hDq]
      _ ≤ 2 * C₀ * D (R - 2) bb := by nlinarith
  -- piece 2: `|J_R − Q_R*| ≤ 10 D_{R-2}(bb)`
  have h2 : |J R v - QrefLimit R v| ≤ 10 * D (R - 2) bb := by
    have hQs := Qref_succ_eq (s := R) (by omega) v
    have hAJ := A_eq_J_add (r := R) (by omega) v
    have hRd : Qref R (R + 1) v - J R v = Rdefect R v := by
      rw [hQs, hAJ]
      unfold Rdefect
      ring
    have hRd_abs : |J R v - Qref R (R + 1) v| ≤ 6 * D (R - 2) v := by
      rw [abs_sub_comm, hRd, abs_of_nonneg (Rdefect_nonneg hv0 R)]
      calc Rdefect R v ≤ 3 * q R v * J R v :=
            Rdefect_le_three_q_mul_J (by omega) hv1
        _ ≤ 3 * q R v * (2 * D R v) := by
            nlinarith [J_le_two_D hv1 R]
        _ = 6 * (D R v * q R v) := by ring
        _ = 6 * D (R - 2) v := by rw [hDq]
    have hlim : |Qref R (R + 1) v - QrefLimit R v| ≤ 4 := by
      rw [abs_sub_comm]
      refine (abs_QrefLimit_sub_Qref (s := R) (R := R + 1) (by omega)
        (by omega) (by omega) hv1).trans ?_
      have hE0 : (0 : ℝ) ≤ E (R + 1 - 4) v := cpb_E_nonneg (by linarith)
      calc 4 * Real.exp (-(E (R + 1 - 4) v) / 2) ≤ 4 * Real.exp 0 := by
            have := Real.exp_le_exp.mpr
              (show -(E (R + 1 - 4) v) / 2 ≤ 0 by linarith)
            linarith
        _ = 4 := by rw [Real.exp_zero]; norm_num
    calc |J R v - QrefLimit R v|
        ≤ |J R v - Qref R (R + 1) v| + |Qref R (R + 1) v - QrefLimit R v| :=
          abs_sub_le _ _ _
      _ ≤ 6 * D (R - 2) v + 4 := add_le_add hRd_abs hlim
      _ ≤ 10 * D (R - 2) bb := by nlinarith
  have heq : Hbar R v - C * QrefLimit R v
      = (Hbar R v - C * J R v) + C * (J R v - QrefLimit R v) := by ring
  calc |Hbar R v - C * QrefLimit R v|
      ≤ |Hbar R v - C * J R v| + |C * (J R v - QrefLimit R v)| := by
        rw [heq]
        exact abs_add_le _ _
    _ ≤ 2 * C₀ * D (R - 2) bb + C * (10 * D (R - 2) bb) := by
        rw [abs_mul, abs_of_nonneg hC]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 hC)
    _ = (2 * C₀ + 10 * C) * D (R - 2) bb := by ring

/-! ## The generic depth-`s ≥ 6` induction step -/

/-- **One induction step of the backward propagation** at depth `s ≥ 6`,
with the explicit radius `exp(−E_{s-3}(a)/2)`: a bound `Zn` at depth `s+1`
on the enlarged window yields, at depth `s`,
`exp(−X) + C exp(−X/3) + 4·Zn·exp(−X/2)/D_s(a)` with `X = E_{s-3}(a)`
(the three per-step losses of eq. `backward-error-recurrence`). -/
theorem cpb_step_at_depth {C : ℝ} (hC : 0 ≤ C) {s : ℕ} (hs : 6 ≤ s)
    {aa bb lo hi : ℝ} (haa1 : 1 < aa) (haa2 : aa ≤ 2) (hbb2 : bb ≤ 2)
    (hw97 : 9.7e6 ≤ E 3 aa)
    (hlo : aa ≤ lo - Real.exp (-(E (s - 3) aa) / 2))
    (hhi : hi + Real.exp (-(E (s - 3) aa) / 2) ≤ bb)
    (hlohi : lo ≤ hi)
    {Zn : ℝ} (hZn0 : 0 ≤ Zn)
    (hZn : ∀ v ∈ Set.Icc (lo - Real.exp (-(E (s - 3) aa) / 2))
      (hi + Real.exp (-(E (s - 3) aa) / 2)),
      |Hbar (s + 1) v - C * QrefLimit (s + 1) v| ≤ Zn) :
    ∀ u ∈ Set.Icc lo hi,
      |Hbar s u - C * QrefLimit s u|
        ≤ Real.exp (-(E (s - 3) aa)) + C * Real.exp (-(E (s - 3) aa) / 3)
          + 4 * Zn * Real.exp (-(E (s - 3) aa) / 2) / D s aa := by
  set X := E (s - 3) aa with hXdef
  set h := Real.exp (-(X) / 2) with hhdef
  have haa0 : (0 : ℝ) < aa := by linarith
  have hbb1 : (1 : ℝ) ≤ bb := by
    have := Real.exp_pos (-(X) / 2)
    linarith
  have hX97 : 9.7e6 ≤ X := by
    rw [hXdef]
    calc (9.7e6 : ℝ) ≤ E 3 aa := hw97
      _ ≤ E (s - 3) aa := E_mono_depth haa1.le (by omega)
  have hE2X : E (s - 2) aa = Real.exp X := by
    rw [hXdef]
    have h' := E_succ (s - 3) aa
    rwa [show s - 3 + 1 = s - 2 by omega] at h'
  have hwindow : ∀ v ∈ Set.Icc (lo - h) (hi + h), aa ≤ v ∧ v ≤ bb :=
    fun v hv => ⟨le_trans hlo hv.1, le_trans hv.2 hhi⟩
  have hone : ∀ v ∈ Set.Icc (lo - h) (hi + h), (1 : ℝ) ≤ v :=
    fun v hv => le_trans haa1.le (hwindow v hv).1
  -- the three data bounds
  have hLip0 : (0 : ℝ) ≤ 34 * (A (s - 1) bb * a (s - 1) bb) + 4 := by
    have hA := A_pos (show (0:ℝ) < bb by linarith) (s - 1)
    have ha := a_pos (s - 1) bb
    nlinarith
  have hQd : ∀ v ∈ Set.Icc (lo - h) (hi + h),
      |QrefLimitIterDeriv 1 s v| ≤ 34 * (A (s - 1) bb * a (s - 1) bb) + 4 := by
    intro v hv
    refine (cpb_abs_QrefLimitIterDeriv_le (by omega) (hone v hv)).trans ?_
    have hv0 : (0 : ℝ) < v := lt_of_lt_of_le one_pos (hone v hv)
    have hAm : A (s - 1) v ≤ A (s - 1) bb :=
      cpb_A_mono _ hv0.le (hwindow v hv).2
    have ham : a (s - 1) v ≤ a (s - 1) bb := cpb_a_mono _ (hwindow v hv).2
    have := A_pos hv0 (s - 1)
    have := a_pos (s - 1) v
    nlinarith
  have hρB : ∀ v ∈ Set.Icc (lo - h) (hi + h),
      |rhoDepth s v| ≤ Real.exp (-(Real.exp X) / 2) := by
    intro v hv
    refine (cpb_rho_le (by omega) (hone v hv)).trans ?_
    refine Real.exp_le_exp.mpr ?_
    have hmono : E (s - 2) aa ≤ E (s - 2) v := E_mono _ (hwindow v hv).1
    rw [← hE2X]
    linarith
  -- the stability step
  have hstep := cpb_backward_step hC (by omega : 4 ≤ s)
    (Real.exp_pos _) hlohi (by linarith)
    (a_pos s aa) (fun v hv => cpb_a_mono s (hwindow v hv).1)
    hLip0 hQd hρB hZn
  intro u hu
  refine (hstep u hu).trans ?_
  -- (i) the ρ term
  have hXpos : (0 : ℝ) < X := by linarith
  have hterm1 : Real.exp (-(Real.exp X) / 2) ≤ Real.exp (-(X)) := by
    refine Real.exp_le_exp.mpr ?_
    have := two_mul_le_exp hXpos.le
    linarith
  -- (ii) the Lipschitz term
  have hterm2 : C * (34 * (A (s - 1) bb * a (s - 1) bb) + 4) * h
      ≤ C * Real.exp (-(X) / 3) := by
    have hLip : 34 * (A (s - 1) bb * a (s - 1) bb) + 4 ≤ Real.exp (X / 6) := by
      rw [hXdef]
      exact cpb_Lip_le_exp hs haa1.le hbb1 hbb2
    have hmul : (34 * (A (s - 1) bb * a (s - 1) bb) + 4) * h
        ≤ Real.exp (X / 6) * Real.exp (-(X) / 2) :=
      mul_le_mul hLip le_rfl (Real.exp_pos _).le (Real.exp_pos _).le
    have hcomb : Real.exp (X / 6) * Real.exp (-(X) / 2)
        = Real.exp (-(X) / 3) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc C * (34 * (A (s - 1) bb * a (s - 1) bb) + 4) * h
        = C * ((34 * (A (s - 1) bb * a (s - 1) bb) + 4) * h) := by ring
      _ ≤ C * Real.exp (-(X) / 3) := by
          rw [← hcomb]
          exact mul_le_mul_of_nonneg_left hmul hC
  -- (iii) the propagated term
  have hterm3 : 2 * Zn / (h * a s aa)
      ≤ 4 * Zn * Real.exp (-(X) / 2) / D s aa := by
    have hDpos : (0 : ℝ) < D s aa := D_pos haa0 s
    have haval : a s aa = D (s + 1) aa / aa :=
      a_eq_D_succ_div haa0.ne' (by omega)
    have hDsucc : D (s + 1) aa = D s aa * E (s - 2) aa := D_succ (by omega) aa
    have hage : D s aa * Real.exp X / 2 ≤ a s aa := by
      rw [haval, hDsucc, hE2X]
      exact div_le_div_of_nonneg_left (by positivity) haa0 haa2
    have hd0 : (0 : ℝ) < D s aa * Real.exp (X / 2) / 2 := by positivity
    have hdle : D s aa * Real.exp (X / 2) / 2 ≤ h * a s aa := by
      have hcomb : Real.exp (-(X) / 2) * Real.exp X = Real.exp (X / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc D s aa * Real.exp (X / 2) / 2
          = Real.exp (-(X) / 2) * (D s aa * Real.exp X / 2) := by
            rw [← hcomb]
            ring
        _ ≤ Real.exp (-(X) / 2) * a s aa :=
            mul_le_mul_of_nonneg_left hage (Real.exp_pos _).le
        _ = h * a s aa := by rw [hhdef]
    have hfrac : 2 * Zn / (h * a s aa)
        ≤ 2 * Zn / (D s aa * Real.exp (X / 2) / 2) :=
      div_le_div_of_nonneg_left (by linarith) hd0 hdle
    have heq : 2 * Zn / (D s aa * Real.exp (X / 2) / 2)
        = 4 * Zn * Real.exp (-(X) / 2) / D s aa := by
      have hprod : Real.exp (-(X) / 2) * Real.exp (X / 2) = 1 := by
        rw [cpb_exp_mul_exp (show -(X) / 2 + X / 2 = 0 by ring), Real.exp_zero]
      rw [div_eq_div_iff hd0.ne' (D_pos haa0 s).ne']
      linear_combination (-(2 * Zn * D s aa)) * hprod
    linarith [hfrac, heq.symm.le]
  linarith

/-! ## Scalar ledgers for the final two depths -/

/-- Depth-5 scalar ledger (paper: `e^{−w/2} + w e^{−w/20} + 2e^{−3w/20}
< e^{−w/25}` for `w ≥ 9.7·10⁶`; here with the propagated coefficient `1`
already absorbed). -/
theorem cpb_depth5_scalar {w : ℝ} (hw : 9.7e6 ≤ w) :
    Real.exp (-(w) / 2) + w * Real.exp (-(w) / 20) + Real.exp (-(3 * w) / 20)
      ≤ Real.exp (-(w) / 25) := by
  have hw200 : w ≤ Real.exp (w / 200) := by
    have hp := pow_div_factorial_le_exp (show (0 : ℝ) ≤ w / 200 by linarith) 2
    have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [hfac] at hp
    nlinarith
  have h1 : w * Real.exp (-(w) / 20) ≤ Real.exp (-(9 * w) / 200) := by
    have hmul : w * Real.exp (-(w) / 20)
        ≤ Real.exp (w / 200) * Real.exp (-(w) / 20) :=
      mul_le_mul_of_nonneg_right hw200 (Real.exp_pos _).le
    have hcomb : Real.exp (w / 200) * Real.exp (-(w) / 20)
        = Real.exp (-(9 * w) / 200) := by
      rw [← Real.exp_add]
      congr 1
      ring
    linarith
  have h2 : Real.exp (-(w) / 2) ≤ Real.exp (-(9 * w) / 200) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-(3 * w) / 20) ≤ Real.exp (-(9 * w) / 200) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4 : 3 * Real.exp (-(9 * w) / 200) ≤ Real.exp (-(w) / 25) := by
    have h3exp : (3 : ℝ) ≤ Real.exp (w / 200) := by
      have := Real.add_one_le_exp (w / 200)
      linarith
    have hcomb : Real.exp (w / 200) * Real.exp (-(9 * w) / 200)
        = Real.exp (-(w) / 25) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith [Real.exp_pos (-(9 * w) / 200)]
  linarith

/-- Depth-4 scalar ledger (paper: `w e^{−w/100} + 2e^{−3w/100}
< e^{−w₋/110}`; here with the explicit depth-4 Lipschitz constant
`4033·(1.3·10²⁸)²⁶`, and with denominator `109` so that, evaluated at the
buffered endpoint `w = 0.999·w₋`, it still implies the paper's
`e^{−w₋/110}` since `0.999/109 > 1/110`). -/
theorem cpb_depth4_scalar {w : ℝ} (hw : 9.7e6 ≤ w) :
    4033 * (1.3e28 : ℝ) ^ 26 * Real.exp (-(w) / 100)
      + 2 * Real.exp (-(3 * w) / 100)
      ≤ Real.exp (-(w) / 109) := by
  -- the Lipschitz constant is below `exp 2274`
  have hL : (4033 : ℝ) * (1.3e28 : ℝ) ^ 26 ≤ Real.exp 2274 := by
    have h1 : ((1.3e28 : ℝ)) ^ 26 ≤ ((1e29 : ℝ)) ^ 26 :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) 26
    have h2 : ((1e29 : ℝ)) ^ 26 = (10 : ℝ) ^ 754 := by
      rw [show (1e29 : ℝ) = 10 ^ 29 by norm_num, ← pow_mul]
    have h3 : (10 : ℝ) ^ 758 ≤ Real.exp 2274 := by
      calc (10 : ℝ) ^ 758 ≤ Real.exp 3 ^ 758 :=
            pow_le_pow_left₀ (by norm_num) cpb_ten_le_exp_three 758
        _ = Real.exp (758 * 3) := (Real.exp_nat_mul 3 758).symm.trans
            (by norm_num)
        _ = Real.exp 2274 := by norm_num
    calc (4033 : ℝ) * (1.3e28 : ℝ) ^ 26 ≤ 4033 * (10 : ℝ) ^ 754 := by
          rw [← h2]
          nlinarith [pow_nonneg (show (0:ℝ) ≤ 1.3e28 by norm_num) 26]
      _ ≤ (10 : ℝ) ^ 4 * (10 : ℝ) ^ 754 :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (10 : ℝ) ^ 758 := by rw [← pow_add]
      _ ≤ Real.exp 2274 := h3
  -- first term
  have hterm1 : 4033 * (1.3e28 : ℝ) ^ 26 * Real.exp (-(w) / 100)
      ≤ (1 / 2) * Real.exp (-(w) / 109) := by
    have hmul : 4033 * (1.3e28 : ℝ) ^ 26 * Real.exp (-(w) / 100)
        ≤ Real.exp 2274 * Real.exp (-(w) / 100) :=
      mul_le_mul_of_nonneg_right hL (Real.exp_pos _).le
    have hcomb : Real.exp (2274 : ℝ) * Real.exp (-(w) / 100)
        = Real.exp (2274 - w / 100) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have harg : (2274 : ℝ) - w / 100 ≤ -(w) / 109 + -1 := by
      have : 9 * w / 10900 ≥ 8009 := by linarith
      linarith
    have hsplit : Real.exp (-(w) / 109 + -1)
        = Real.exp (-(w) / 109) * Real.exp (-1 : ℝ) := Real.exp_add _ _
    have hhalf : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      calc (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
        _ ≤ Real.exp 1 := cpb_two_le_exp_one
    calc 4033 * (1.3e28 : ℝ) ^ 26 * Real.exp (-(w) / 100)
        ≤ Real.exp (2274 - w / 100) := by rw [← hcomb]; exact hmul
      _ ≤ Real.exp (-(w) / 109 + -1) := Real.exp_le_exp.mpr harg
      _ = Real.exp (-(w) / 109) * Real.exp (-1 : ℝ) := hsplit
      _ ≤ (1 / 2) * Real.exp (-(w) / 109) := by
          nlinarith [Real.exp_pos (-(w) / 109)]
  -- second term
  have hterm2 : 2 * Real.exp (-(3 * w) / 100)
      ≤ (1 / 2) * Real.exp (-(w) / 109) := by
    have h4exp : (4 : ℝ) ≤ Real.exp (w * (227 / 10900)) := by
      have := Real.add_one_le_exp (w * (227 / 10900))
      linarith
    have hcomb : Real.exp (w * (227 / 10900)) * Real.exp (-(3 * w) / 100)
        = Real.exp (-(w) / 109) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith [Real.exp_pos (-(3 * w) / 100)]
  linarith

/-! ## The main theorem -/

set_option maxHeartbeats 1600000 in
/-- **Backward propagation for a constant phase function**
(paper `prop:constant-phase-backward`, eq. `H4-Q4`).

If `Φ ≡ C` on `[1, e]`, then for every window `[w₋, w₊]` with
`0.999 w₋ ≥ 9.7·10⁶` and `1.001 w₊ ≤ 1.3·10²⁸`, and every bound `ρ4bound`
for `|ρ₄|` on the buffered phase interval
`U⁺ = [E₃⁻¹(0.999 w₋), E₃⁻¹(1.001 w₊)]`, the depth-4 comparison holds on
`U = [E₃⁻¹(w₋), E₃⁻¹(w₊)]`:

  `|H̄₄(u) − C·Q₄*(u)| ≤ ρ4bound + (1 + C)·exp(−w₋/110)`.

The phase intervals are spelled via `iteratedLog 3`, which on this window
is the honest inverse of `E 3` (`cpb_E3_iteratedLog3`); the paper's
`eq:backward-window-hypotheses` carries only the two numeric bounds, and
the placement `U⁺ ⊂ (1, 2)` is derived (in the paper's proof and here)
from `E₃(1) < 3.9·10⁶`, `E₃(2) > 1.3·10²⁸`. -/
theorem constant_phase_backward
    {C : ℝ} (hC : 0 ≤ C)
    (hconst : ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), phasePhi u = C)
    {wlo whi : ℝ} (hlo : (9.7e6 : ℝ) ≤ 0.999 * wlo) (hhi : 1.001 * whi ≤ 1.3e28)
    (hwin : wlo ≤ whi)
    {ρ4bound : ℝ}
    (hρ4 : ∀ v, iteratedLog 3 (0.999 * wlo) ≤ v →
      v ≤ iteratedLog 3 (1.001 * whi) → |rhoDepth 4 v| ≤ ρ4bound) :
    ∀ u, iteratedLog 3 wlo ≤ u → u ≤ iteratedLog 3 whi →
      |Hbar 4 u - C * QrefLimit 4 u|
        ≤ ρ4bound + (1 + C) * Real.exp (-(wlo) / 110) := by
  intro u hu1 hu2
  -- ### window bookkeeping
  set aa := iteratedLog 3 (0.999 * wlo) with haadef
  set bb := iteratedLog 3 (1.001 * whi) with hbbdef
  set uα := iteratedLog 3 wlo with hαdef
  set uβ := iteratedLog 3 whi with hβdef
  have hwlo_pos : (0 : ℝ) < wlo := by nlinarith
  have hwlo97 : (9.7e6 : ℝ) ≤ wlo := by nlinarith
  have hwhi97 : (9.7e6 : ℝ) ≤ whi := le_trans hwlo97 hwin
  have h1whi97 : (9.7e6 : ℝ) ≤ 1.001 * whi := by nlinarith
  have hwhi28 : whi ≤ 1.3e28 := by nlinarith
  have hwlo28 : wlo ≤ 1.3e28 := le_trans hwin hwhi28
  have hE3aa : E 3 aa = 0.999 * wlo := cpb_E3_iteratedLog3 hlo
  have hE3bb : E 3 bb = 1.001 * whi := cpb_E3_iteratedLog3 h1whi97
  have hw97 : (9.7e6 : ℝ) ≤ E 3 aa := by rw [hE3aa]; exact hlo
  have haa1 : 1 < aa := cpb_one_lt_iteratedLog3 hlo
  have haa0 : (0 : ℝ) < aa := by linarith
  have hbb2 : bb ≤ 2 := cpb_iteratedLog3_le_two h1whi97 hhi
  have haabb : aa ≤ bb := cpb_iteratedLog3_mono hlo (by nlinarith)
  have haa2 : aa ≤ 2 := le_trans haabb hbb2
  have hαβ : uα ≤ uβ := cpb_iteratedLog3_mono hwlo97 hwin
  -- ### buffer margins
  have hmargin_lo : (1 / 273000 : ℝ) ≤ uα - aa := by
    have h := cpb_iteratedLog3_sub_ge hlo (by nlinarith : 0.999 * wlo ≤ wlo)
      hwlo28
    have hlog : Real.log wlo - Real.log (0.999 * wlo) = -Real.log 0.999 := by
      rw [Real.log_mul (by norm_num) hwlo_pos.ne']
      ring
    have hl999 : Real.log 0.999 ≤ -(1 / 1000) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 0.999 by norm_num)
      linarith
    rw [hlog] at h
    have : (1 / 273000 : ℝ) ≤ -Real.log 0.999 / 273 := by linarith
    linarith
  have hmargin_hi : (1 / 273273 : ℝ) ≤ bb - uβ := by
    have hwhi_pos : (0 : ℝ) < whi := by linarith
    have h := cpb_iteratedLog3_sub_ge hwhi97
      (by nlinarith : whi ≤ 1.001 * whi) hhi
    have hlog : Real.log (1.001 * whi) - Real.log whi = Real.log 1.001 := by
      rw [Real.log_mul (by norm_num) hwhi_pos.ne']
      ring
    have hl1001 : (1 / 1001 : ℝ) ≤ Real.log 1.001 := by
      have hkey := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < (1.001)⁻¹ by norm_num)
      rw [Real.log_inv] at hkey
      have : ((1.001 : ℝ))⁻¹ - 1 = -(1 / 1001) := by norm_num
      linarith
    rw [hlog] at h
    have : (1 / 273273 : ℝ) ≤ Real.log 1.001 / 273 := by linarith
    linarith
  -- ### slack is below the margins
  have hslack : ∀ s, cpbSlack aa s ≤ 3e-6 := by
    intro s
    have h1 := cpb_slack_le aa haa1.le hw97 s
    have h2 : Real.exp (-(E 3 aa) / 100) ≤ 1 / 666667 := by
      have h3 : (666667 : ℝ) ≤ Real.exp (E 3 aa / 100) := by
        refine cpb_le_exp_fourteen.trans (Real.exp_le_exp.mpr ?_)
        linarith
      have h4 : Real.exp (-(E 3 aa) / 100) = 1 / Real.exp (E 3 aa / 100) := by
        rw [show -(E 3 aa) / 100 = -(E 3 aa / 100) by ring, Real.exp_neg,
          inv_eq_one_div]
      rw [h4]
      exact one_div_le_one_div_of_le (by norm_num) h3
    calc cpbSlack aa s ≤ 2 * Real.exp (-(E 3 aa) / 100) := h1
      _ ≤ 2 * (1 / 666667) := by linarith
      _ ≤ 3e-6 := by norm_num
  have hwin_lo : ∀ s, aa ≤ uα - cpbSlack aa s := by
    intro s
    have h1 : (3e-6 : ℝ) ≤ 1 / 273000 := by norm_num
    linarith [hslack s, hmargin_lo]
  have hwin_hi : ∀ s, uβ + cpbSlack aa s ≤ bb := by
    intro s
    have h1 : (3e-6 : ℝ) ≤ 1 / 273273 := by norm_num
    linarith [hslack s, hmargin_hi]
  have hwαβ : ∀ s, uα - cpbSlack aa s ≤ uβ + cpbSlack aa s := by
    intro s
    have := cpb_slack_nonneg aa s
    linarith
  -- ### the phase-iteration terminal data
  obtain ⟨C₀, r₁, hC₀, htail⟩ := abs_Hbar_div_J_sub_phasePhi_le
  set KT := 2 * C₀ + 10 * C with hKTdef
  have hKT0 : 0 ≤ KT := by rw [hKTdef]; linarith
  -- ### conclusion via `R → ∞`
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  set ε := c - (ρ4bound + (1 + C) * Real.exp (-(wlo) / 110)) with hεdef
  have hε0 : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨n, hn⟩ := exists_nat_ge (3 + 40 * KT / (3 * ε))
  set R := max n (max 10 r₁) with hRdef
  have hR10 : 10 ≤ R := le_trans (le_max_left 10 r₁) (le_max_right _ _)
  have hRr₁ : r₁ ≤ R := le_trans (le_max_right 10 r₁) (le_max_right _ _)
  have hRn : n ≤ R := le_max_left _ _
  set δ := 4 * KT * Real.exp (-(3 * E (R - 4) aa) / 10) with hδdef
  have hδ0 : 0 ≤ δ := by
    rw [hδdef]
    positivity
  have hδε : δ ≤ ε := by
    have hE1 : ((R : ℝ) - 3) ≤ E (R - 4) aa := by
      have h1 := cpb_nat_add_one_le_E (R - 4)
      have hcast : ((R - 4 : ℕ) : ℝ) = (R : ℝ) - 4 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have h2 : E (R - 4) 1 ≤ E (R - 4) aa := E_mono _ haa1.le
      rw [hcast] at h1
      linarith
    set y := (3 / 10 : ℝ) * ((R : ℝ) - 3) with hydef
    have hRn' : (n : ℝ) ≤ (R : ℝ) := Nat.cast_le.mpr hRn
    have hy1 : 4 * KT / ε ≤ y := by
      rw [hydef]
      have h1 : 3 + 40 * KT / (3 * ε) ≤ (R : ℝ) := le_trans hn hRn'
      have h2 : 40 * KT / (3 * ε) = (10 / 3) * (4 * KT / ε) := by
        field_simp
        ring
      rw [h2] at h1
      linarith
  -- `δ ≤ 4KT·exp(−y) ≤ ε`
    have hmono : Real.exp (-(3 * E (R - 4) aa) / 10) ≤ Real.exp (-y) := by
      refine Real.exp_le_exp.mpr ?_
      rw [hydef]
      linarith
    have hexpy : 4 * KT / ε ≤ Real.exp y := by
      have := Real.add_one_le_exp y
      have hy0 : 0 ≤ 4 * KT / ε := by positivity
      linarith
    have hkey : 4 * KT ≤ ε * Real.exp y := by
      have hcancel : ε * (4 * KT / ε) = 4 * KT := by
        rw [mul_comm, div_mul_cancel₀ _ hε0.ne']
      calc 4 * KT = ε * (4 * KT / ε) := hcancel.symm
        _ ≤ ε * Real.exp y := mul_le_mul_of_nonneg_left hexpy hε0.le
    have hprod : Real.exp y * Real.exp (-y) = 1 := by
      rw [← Real.exp_add]
      simp
    calc δ ≤ 4 * KT * Real.exp (-y) := by
          rw [hδdef]
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ ε * Real.exp y * Real.exp (-y) :=
          mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
      _ = ε := by rw [mul_assoc, hprod, mul_one]
  -- ### the downward induction over depths `R−1, …, 6`
  have hM0 : (0 : ℝ) ≤ 1 + C + δ := by linarith
  have main : ∀ k s, 6 ≤ s → s + k = R - 1 →
      ∀ v ∈ Set.Icc (uα - cpbSlack aa s) (uβ + cpbSlack aa s),
        |Hbar s v - C * QrefLimit s v|
          ≤ (1 + C + δ) * Real.exp (-(E (s - 3) aa) / 5) := by
    intro k
    induction k with
    | zero =>
        intro s hs6 hsR v hv
        -- base case `s = R − 1`: the terminal bound enters
        have hsR' : s + 1 = R := by omega
        have hrad : cpbRadius aa s = Real.exp (-(E (s - 3) aa) / 2) :=
          cpb_radius_of_six_le aa hs6
        have hσ : cpbSlack aa (s + 1) = cpbSlack aa s + cpbRadius aa s :=
          cpb_slack_succ aa (by omega)
        have hZn : ∀ w ∈ Set.Icc
            (uα - cpbSlack aa s - Real.exp (-(E (s - 3) aa) / 2))
            (uβ + cpbSlack aa s + Real.exp (-(E (s - 3) aa) / 2)),
            |Hbar (s + 1) w - C * QrefLimit (s + 1) w|
              ≤ KT * D (s - 1) bb := by
          intro w hw
          have hw_lo : aa ≤ w := by
            have := hwin_lo (s + 1)
            have h1 := hw.1
            rw [hσ, hrad] at this
            linarith
          have hw_hi : w ≤ bb := by
            have := hwin_hi (s + 1)
            have h2 := hw.2
            rw [hσ, hrad] at this
            linarith
          have hterm := cpb_terminal_bound hC hC₀ hconst htail hR10 hRr₁ hbb2
            (le_trans haa1.le hw_lo) hw_hi
          rw [hsR']
          have hidx : R - 2 = s - 1 := by omega
          rw [hidx] at hterm
          exact hterm
        have hstep := cpb_step_at_depth hC hs6 haa1 haa2 hbb2 hw97
          (by rw [← hrad]; have := hwin_lo (s + 1); rw [hσ] at this; linarith)
          (by rw [← hrad]; have := hwin_hi (s + 1); rw [hσ] at this; linarith)
          (hwαβ s)
          (mul_nonneg hKT0 (D_pos (lt_of_lt_of_le haa0 haabb) (s - 1)).le)
          hZn v hv
        -- fold the terminal term into `δ·exp(−X/5)`
        set X := E (s - 3) aa with hXdef
        have hX97 : 9.7e6 ≤ X := by
          rw [hXdef]
          calc (9.7e6 : ℝ) ≤ E 3 aa := hw97
            _ ≤ E (s - 3) aa := E_mono_depth haa1.le (by omega)
        have hDpos : (0 : ℝ) < D s aa := D_pos haa0 s
        have hterm3 : 4 * (KT * D (s - 1) bb) * Real.exp (-(X) / 2) / D s aa
            ≤ δ * Real.exp (-(X) / 5) := by
          have hDD : D (s - 1) bb ≤ D s aa := by
            have h := cpb_D_le_D_succ_shift (r := s - 1) (by omega) haa1.le
              (by linarith : (0 : ℝ) ≤ bb) hbb2
            rwa [show s - 1 + 1 = s by omega] at h
          have h1 : 4 * (KT * D (s - 1) bb) * Real.exp (-(X) / 2) / D s aa
              ≤ 4 * KT * Real.exp (-(X) / 2) := by
            rw [div_le_iff₀ hDpos]
            have h1' : KT * D (s - 1) bb ≤ KT * D s aa :=
              mul_le_mul_of_nonneg_left hDD hKT0
            have hmul := mul_le_mul_of_nonneg_right h1'
              (Real.exp_pos (-(X) / 2)).le
            linarith only [hmul]
          have h2 : 4 * KT * Real.exp (-(X) / 2) = δ * Real.exp (-(X) / 5) := by
            have hcomb : Real.exp (-(3 * X) / 10) * Real.exp (-(X) / 5)
                = Real.exp (-(X) / 2) := by
              rw [← Real.exp_add]
              congr 1
              ring
            rw [hδdef, show R - 4 = s - 3 by omega, ← hXdef, ← hcomb]
            ring
          linarith only [h1, h2]
        have hmono1 : Real.exp (-(X)) ≤ Real.exp (-(X) / 5) :=
          Real.exp_le_exp.mpr (by linarith only [hX97])
        have hmono2 : Real.exp (-(X) / 3) ≤ Real.exp (-(X) / 5) :=
          Real.exp_le_exp.mpr (by linarith only [hX97])
        have hCterm : C * Real.exp (-(X) / 3) ≤ C * Real.exp (-(X) / 5) :=
          mul_le_mul_of_nonneg_left hmono2 hC
        calc |Hbar s v - C * QrefLimit s v|
            ≤ Real.exp (-(X)) + C * Real.exp (-(X) / 3)
              + 4 * (KT * D (s - 1) bb) * Real.exp (-(X) / 2) / D s aa := hstep
          _ ≤ Real.exp (-(X) / 5) + C * Real.exp (-(X) / 5)
              + δ * Real.exp (-(X) / 5) := by
                linarith only [hterm3, hmono1, hCterm]
          _ = (1 + C + δ) * Real.exp (-(X) / 5) := by ring
    | succ k ih =>
        intro s hs6 hsR v hv
        -- inductive step: use the bound at depth `s + 1`
        have hrad : cpbRadius aa s = Real.exp (-(E (s - 3) aa) / 2) :=
          cpb_radius_of_six_le aa hs6
        have hσ : cpbSlack aa (s + 1) = cpbSlack aa s + cpbRadius aa s :=
          cpb_slack_succ aa (by omega)
        have hZprev := ih (s + 1) (by omega) (by omega)
        have hidx : s + 1 - 3 = s - 2 := by omega
        have hZn : ∀ w ∈ Set.Icc
            (uα - cpbSlack aa s - Real.exp (-(E (s - 3) aa) / 2))
            (uβ + cpbSlack aa s + Real.exp (-(E (s - 3) aa) / 2)),
            |Hbar (s + 1) w - C * QrefLimit (s + 1) w|
              ≤ (1 + C + δ) * Real.exp (-(E (s - 2) aa) / 5) := by
          intro w hw
          have hmem : w ∈ Set.Icc (uα - cpbSlack aa (s + 1))
              (uβ + cpbSlack aa (s + 1)) := by
            rw [hσ, hrad]
            exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
          have h := hZprev w hmem
          rwa [hidx] at h
        have hstep := cpb_step_at_depth hC hs6 haa1 haa2 hbb2 hw97
          (by rw [← hrad]; have := hwin_lo (s + 1); rw [hσ] at this; linarith)
          (by rw [← hrad]; have := hwin_hi (s + 1); rw [hσ] at this; linarith)
          (hwαβ s)
          (mul_nonneg hM0 (Real.exp_pos _).le)
          hZn v hv
        set X := E (s - 3) aa with hXdef
        have hX97 : 9.7e6 ≤ X := by
          rw [hXdef]
          calc (9.7e6 : ℝ) ≤ E 3 aa := hw97
            _ ≤ E (s - 3) aa := E_mono_depth haa1.le (by omega)
        have hE2X : E (s - 2) aa = Real.exp X := by
          rw [hXdef]
          have h' := E_succ (s - 3) aa
          rwa [show s - 3 + 1 = s - 2 by omega] at h'
        have hDpos : (0 : ℝ) < D s aa := D_pos haa0 s
        have hD1 : (1 : ℝ) ≤ D s aa := one_le_D haa1.le s
        -- the propagated term collapses to `(1+C+δ)·exp(−X/2)`
        have hterm3 : 4 * ((1 + C + δ) * Real.exp (-(E (s - 2) aa) / 5))
              * Real.exp (-(X) / 2) / D s aa
            ≤ (1 + C + δ) * Real.exp (-(X) / 2) := by
          have hsmall : 4 * Real.exp (-(E (s - 2) aa) / 5) ≤ 1 := by
            rw [hE2X]
            have hX2 : (3 : ℝ) ≤ Real.exp X / 5 := by
              have := two_mul_le_exp (show (0:ℝ) ≤ X by linarith)
              linarith
            have h4 : (4 : ℝ) ≤ Real.exp (Real.exp X / 5) := by
              have := Real.add_one_le_exp (Real.exp X / 5)
              linarith
            have hprod : Real.exp (-(Real.exp X) / 5)
                * Real.exp (Real.exp X / 5) = 1 := by
              rw [cpb_exp_mul_exp
                (show -(Real.exp X) / 5 + Real.exp X / 5 = 0 by ring),
                Real.exp_zero]
            have hmm := mul_le_mul_of_nonneg_left h4
              (Real.exp_pos (-(Real.exp X) / 5)).le
            linarith only [hmm, hprod]
          have hnum : 4 * ((1 + C + δ) * Real.exp (-(E (s - 2) aa) / 5))
                * Real.exp (-(X) / 2)
              ≤ (1 + C + δ) * Real.exp (-(X) / 2) := by
            linarith [mul_le_mul_of_nonneg_left hsmall
              (mul_nonneg hM0 (Real.exp_pos (-(X) / 2)).le)]
          calc 4 * ((1 + C + δ) * Real.exp (-(E (s - 2) aa) / 5))
                * Real.exp (-(X) / 2) / D s aa
              ≤ 4 * ((1 + C + δ) * Real.exp (-(E (s - 2) aa) / 5))
                * Real.exp (-(X) / 2) / 1 :=
                div_le_div_of_nonneg_left
                  (mul_nonneg (mul_nonneg (by norm_num)
                    (mul_nonneg hM0 (Real.exp_pos _).le)) (Real.exp_pos _).le)
                  one_pos hD1
            _ = 4 * ((1 + C + δ) * Real.exp (-(E (s - 2) aa) / 5))
                * Real.exp (-(X) / 2) := by rw [div_one]
            _ ≤ (1 + C + δ) * Real.exp (-(X) / 2) := hnum
        -- assemble: `e^{−X} + C e^{−X/3} + M e^{−X/2} ≤ M e^{−X/5}`
        have hmono1 : Real.exp (-(X)) ≤ Real.exp (-(X) / 3) :=
          Real.exp_le_exp.mpr (by linarith)
        have hmono2 : Real.exp (-(X) / 2) ≤ Real.exp (-(X) / 3) :=
          Real.exp_le_exp.mpr (by linarith)
        have hgeom : 2 * Real.exp (-(X) / 3) ≤ Real.exp (-(X) / 5) := by
          have h2exp : (2 : ℝ) ≤ Real.exp (X * (2 / 15)) := by
            have h := Real.add_one_le_exp (X * (2 / 15))
            linarith only [h, hX97]
          have hprod : Real.exp (X * (2 / 15)) * Real.exp (-(X) / 3)
              = Real.exp (-(X) / 5) :=
            cpb_exp_mul_exp (by ring)
          have hmm := mul_le_mul_of_nonneg_right h2exp
            (Real.exp_pos (-(X) / 3)).le
          linarith only [hmm, hprod]
        have hfin : Real.exp (-(X)) + C * Real.exp (-(X) / 3)
            + (1 + C + δ) * Real.exp (-(X) / 2)
            ≤ (1 + C + δ) * Real.exp (-(X) / 5) := by
          have e3pos : (0 : ℝ) < Real.exp (-(X) / 3) := Real.exp_pos _
          have hδe3 : 0 ≤ δ * Real.exp (-(X) / 3) := mul_nonneg hδ0 e3pos.le
          have h2 : (1 + C + δ) * Real.exp (-(X) / 2)
              ≤ (1 + C + δ) * Real.exp (-(X) / 3) :=
            mul_le_mul_of_nonneg_left hmono2 hM0
          have h4 : (1 + C + δ) * (2 * Real.exp (-(X) / 3))
              ≤ (1 + C + δ) * Real.exp (-(X) / 5) :=
            mul_le_mul_of_nonneg_left hgeom hM0
          linarith only [hmono1, hδe3, h2, h4, hC,
            mul_le_mul_of_nonneg_right hC e3pos.le]
        calc |Hbar s v - C * QrefLimit s v|
            ≤ Real.exp (-(X)) + C * Real.exp (-(X) / 3)
              + 4 * ((1 + C + δ) * Real.exp (-(E (s - 2) aa) / 5))
                * Real.exp (-(X) / 2) / D s aa := hstep
          _ ≤ Real.exp (-(X)) + C * Real.exp (-(X) / 3)
              + (1 + C + δ) * Real.exp (-(X) / 2) := by
                linarith only [hterm3]
          _ ≤ (1 + C + δ) * Real.exp (-(X) / 5) := hfin
  -- ### depth 6 → 5
  have h6 := main (R - 7) 6 (by omega) (by omega)
  have h6' : ∀ v ∈ Set.Icc (uα - cpbSlack aa 6) (uβ + cpbSlack aa 6),
      |Hbar 6 v - C * QrefLimit 6 v|
        ≤ (1 + C + δ) * Real.exp (-(E 3 aa) / 5) := by
    intro v hv
    have h := h6 v hv
    rwa [show (6 : ℕ) - 3 = 3 from rfl] at h
  have h5 : ∀ v ∈ Set.Icc (uα - cpbSlack aa 5) (uβ + cpbSlack aa 5),
      |Hbar 5 v - C * QrefLimit 5 v|
        ≤ (1 + C + δ) * Real.exp (-(E 3 aa) / 25) := by
    set w := E 3 aa with hwdef
    have hw97' : (9.7e6 : ℝ) ≤ w := hw97
    have hσ : cpbSlack aa 6 = cpbSlack aa 5 + cpbRadius aa 5 :=
      cpb_slack_succ aa (by omega)
    have hrad : cpbRadius aa 5 = Real.exp (-(w) / 20) := cpb_radius_five aa
    have hwindow : ∀ v ∈ Set.Icc (uα - cpbSlack aa 5 - Real.exp (-(w) / 20))
        (uβ + cpbSlack aa 5 + Real.exp (-(w) / 20)), aa ≤ v ∧ v ≤ bb := by
      intro v hv
      constructor
      · have := hwin_lo 6
        rw [hσ, hrad] at this
        linarith [hv.1]
      · have := hwin_hi 6
        rw [hσ, hrad] at this
        linarith [hv.2]
    have hone : ∀ v ∈ Set.Icc (uα - cpbSlack aa 5 - Real.exp (-(w) / 20))
        (uβ + cpbSlack aa 5 + Real.exp (-(w) / 20)), (1 : ℝ) ≤ v :=
      fun v hv => le_trans haa1.le (hwindow v hv).1
    -- numeric depth-5 Lipschitz constant
    have hLip5 : ∀ v ∈ Set.Icc (uα - cpbSlack aa 5 - Real.exp (-(w) / 20))
        (uβ + cpbSlack aa 5 + Real.exp (-(w) / 20)),
        |QrefLimitIterDeriv 1 5 v| ≤ 9.7e6 := by
      intro v hv
      have hv1 : (1 : ℝ) ≤ v := hone v hv
      have hv0 : (0 : ℝ) < v := by linarith
      refine (cpb_abs_QrefLimitIterDeriv_le (by norm_num) hv1).trans ?_
      rw [show (5 : ℕ) - 1 = 4 from rfl]
      have hE1v : E 1 v = Real.exp v := by
        have h1 : E 1 v = Real.exp (E 0 v) := E_succ 0 v
        rw [h1, E_zero]
      have hvbb : v ≤ bb := (hwindow v hv).2
      have hE1 : E 1 v ≤ 7.3890561 := by
        rw [hE1v]
        calc Real.exp v ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
          _ ≤ 7.3890561 := cpb_exp_two_le
      have hE1pos : (0 : ℝ) < E 1 v := E_pos_of_one_le (by norm_num) v
      have hE2 : E 2 v ≤ 1650 := by
        have h2 : E 2 v = Real.exp (E 1 v) := E_succ 1 v
        rw [h2, hE1v]
        calc Real.exp (Real.exp v) ≤ Real.exp (Real.exp 2) := by
              refine Real.exp_le_exp.mpr (Real.exp_le_exp.mpr ?_)
              linarith
          _ ≤ 1650 := cpb_exp_exp_two_le
      have hE2pos : (0 : ℝ) < E 2 v := E_pos_of_one_le (by norm_num) v
      have hv2 : v ≤ 2 := le_trans hvbb hbb2
      have hA4 : A 4 v ≤ 17.7781122 := by
        rw [A_four_eq]
        have hprod : v * E 1 v ≤ 2 * 7.3890561 :=
          mul_le_mul hv2 hE1 hE1pos.le (by norm_num)
        linarith only [hprod, hv2]
      have hA4pos : (0 : ℝ) < A 4 v := A_pos hv0 4
      have ha4 : a 4 v = E 1 v * E 2 v := by
        have h := a_succ (r := 3) (by norm_num) v
        rw [a_three] at h
        exact h
      have ha4le : a 4 v ≤ 7.3890561 * 1650 := by
        rw [ha4]
        exact mul_le_mul hE1 hE2 hE2pos.le (by norm_num)
      have ha4pos : (0 : ℝ) < a 4 v := a_pos 4 v
      have hAa : A 4 v * a 4 v ≤ 17.7781122 * (7.3890561 * 1650) :=
        mul_le_mul hA4 ha4le ha4pos.le (by norm_num)
      linarith only [hAa]
    have hρ5 : ∀ v ∈ Set.Icc (uα - cpbSlack aa 5 - Real.exp (-(w) / 20))
        (uβ + cpbSlack aa 5 + Real.exp (-(w) / 20)),
        |rhoDepth 5 v| ≤ Real.exp (-(w) / 2) := by
      intro v hv
      refine (cpb_rho_le (by norm_num) (hone v hv)).trans ?_
      refine Real.exp_le_exp.mpr ?_
      rw [show (5 : ℕ) - 2 = 3 from rfl, hwdef]
      linarith [E_mono 3 (hwindow v hv).1]
    have hZn6 : ∀ v ∈ Set.Icc (uα - cpbSlack aa 5 - Real.exp (-(w) / 20))
        (uβ + cpbSlack aa 5 + Real.exp (-(w) / 20)),
        |Hbar 6 v - C * QrefLimit 6 v|
          ≤ (1 + C + δ) * Real.exp (-(w) / 5) := by
      intro v hv
      refine h6' v ?_
      rw [hσ, hrad]
      exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hstep := cpb_backward_step hC (by norm_num : 4 ≤ 5)
      (Real.exp_pos (-(w) / 20)) (hwαβ 5)
      (by have := hwin_lo 6; rw [hσ, hrad] at this; linarith)
      (a_pos 5 aa) (fun v hv => cpb_a_mono 5 (hwindow v hv).1)
      (by norm_num : (0 : ℝ) ≤ 9.7e6) hLip5 hρ5 hZn6
    intro v hv
    refine (hstep v hv).trans ?_
    -- assemble the depth-5 arithmetic
    have hw0 : (0 : ℝ) < w := by linarith
    have ha5ge : w / 2 ≤ a 5 aa := by
      have hD6 : w ≤ D 6 aa := by
        have h1 : D 6 aa = D 5 aa * E 3 aa := D_succ (r := 5) (by norm_num) aa
        have h2 : (1 : ℝ) ≤ D 5 aa := one_le_D haa1.le 5
        have h3 : (0 : ℝ) < E 3 aa := E_pos_of_pos haa0 3
        have h4 := mul_le_mul_of_nonneg_right h2 h3.le
        rw [hwdef, h1]
        linarith only [h4]
      have hmul : a 5 aa * aa = D 6 aa := by
        rw [a_eq_D_succ_div haa0.ne' (show 2 ≤ 5 by norm_num)]
        field_simp
      have h5' := mul_le_mul_of_nonneg_left haa2 (a_pos 5 aa).le
      linarith only [hmul, hD6, h5']
    have hZn0' : (0 : ℝ) ≤ (1 + C + δ) * Real.exp (-(w) / 5) :=
      mul_nonneg hM0 (Real.exp_pos _).le
    -- the propagated term
    have hthird : 2 * ((1 + C + δ) * Real.exp (-(w) / 5))
        / (Real.exp (-(w) / 20) * a 5 aa)
        ≤ (1 + C + δ) * Real.exp (-(3 * w) / 20) := by
      have hd0 : (0 : ℝ) < Real.exp (-(w) / 20) * (w / 2) := by positivity
      have hdle : Real.exp (-(w) / 20) * (w / 2)
          ≤ Real.exp (-(w) / 20) * a 5 aa :=
        mul_le_mul_of_nonneg_left ha5ge (Real.exp_pos _).le
      have h1 : 2 * ((1 + C + δ) * Real.exp (-(w) / 5))
          / (Real.exp (-(w) / 20) * a 5 aa)
          ≤ 2 * ((1 + C + δ) * Real.exp (-(w) / 5))
            / (Real.exp (-(w) / 20) * (w / 2)) :=
        div_le_div_of_nonneg_left (by linarith) hd0 hdle
      have h3 : 2 * ((1 + C + δ) * Real.exp (-(w) / 5))
          / (Real.exp (-(w) / 20) * (w / 2))
          ≤ (1 + C + δ) * Real.exp (-(3 * w) / 20) := by
        rw [div_le_iff₀ hd0]
        have hcomb : Real.exp (-(3 * w) / 20) * Real.exp (-(w) / 20)
            = Real.exp (-(w) / 5) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hre : (1 + C + δ) * Real.exp (-(3 * w) / 20)
              * (Real.exp (-(w) / 20) * (w / 2))
            = (1 + C + δ)
              * (Real.exp (-(3 * w) / 20) * Real.exp (-(w) / 20)) * (w / 2) := by
          ring
        rw [hre, hcomb]
        have h2w : (2 : ℝ) ≤ w / 2 := by linarith only [hw97']
        have hmm := mul_le_mul_of_nonneg_left h2w hZn0'
        linarith only [hmm]
      exact h1.trans h3
    -- the Lipschitz term
    have hlip : C * 9.7e6 * Real.exp (-(w) / 20)
        ≤ C * (w * Real.exp (-(w) / 20)) := by
      have h1 : (9.7e6 : ℝ) * Real.exp (-(w) / 20) ≤ w * Real.exp (-(w) / 20) :=
        mul_le_mul_of_nonneg_right hw97' (Real.exp_pos _).le
      linarith only [mul_le_mul_of_nonneg_left h1 hC]
    -- final assembly with the scalar ledger
    have hsc := cpb_depth5_scalar hw97'
    have hM1 : (1 : ℝ) ≤ 1 + C + δ := by linarith
    have hmulsc := mul_le_mul_of_nonneg_left hsc hM0
    have hterm1 : Real.exp (-(w) / 2) ≤ (1 + C + δ) * Real.exp (-(w) / 2) :=
      le_mul_of_one_le_left (Real.exp_pos _).le hM1
    have hterm2 : C * (w * Real.exp (-(w) / 20))
        ≤ (1 + C + δ) * (w * Real.exp (-(w) / 20)) := by
      have hwe : (0 : ℝ) ≤ w * Real.exp (-(w) / 20) :=
        mul_nonneg hw0.le (Real.exp_pos _).le
      linarith only [hwe, mul_nonneg hδ0 hwe]
    have hexpand : (1 + C + δ) * (Real.exp (-(w) / 2)
          + w * Real.exp (-(w) / 20) + Real.exp (-(3 * w) / 20))
        = (1 + C + δ) * Real.exp (-(w) / 2)
          + (1 + C + δ) * (w * Real.exp (-(w) / 20))
          + (1 + C + δ) * Real.exp (-(3 * w) / 20) := by ring
    have hδ320 : (0 : ℝ) ≤ δ * Real.exp (-(3 * w) / 20) :=
      mul_nonneg hδ0 (Real.exp_pos _).le
    linarith only [hthird, hlip, hmulsc, hterm1, hterm2, hexpand, hδ320]
  -- ### depth 5 → 4
  have hσ5 : cpbSlack aa 5 = Real.exp (-(E 3 aa) / 100) := by
    have h : cpbSlack aa (4 + 1) = cpbSlack aa 4 + cpbRadius aa 4 :=
      cpb_slack_succ aa le_rfl
    rw [cpb_slack_four, cpb_radius_four, zero_add] at h
    exact h
  have hwindow4 : ∀ v ∈ Set.Icc (uα - Real.exp (-(E 3 aa) / 100))
      (uβ + Real.exp (-(E 3 aa) / 100)), aa ≤ v ∧ v ≤ bb := by
    intro v hv
    constructor
    · have h := hwin_lo 5
      rw [hσ5] at h
      linarith [hv.1]
    · have h := hwin_hi 5
      rw [hσ5] at h
      linarith [hv.2]
  have hQd4 : ∀ v ∈ Set.Icc (uα - Real.exp (-(E 3 aa) / 100))
      (uβ + Real.exp (-(E 3 aa) / 100)),
      |QrefLimitIterDeriv 1 4 v| ≤ 4033 * (1.3e28 : ℝ) ^ 26 := by
    intro v hv
    have hv1 : (1 : ℝ) ≤ v := le_trans haa1.le (hwindow4 v hv).1
    refine (cpb_abs_QrefLimitIterDeriv_four_le hv1).trans ?_
    have hE3v : E 3 v ≤ 1.3e28 := by
      calc E 3 v ≤ E 3 bb := E_mono 3 (hwindow4 v hv).2
        _ = 1.001 * whi := hE3bb
        _ ≤ 1.3e28 := hhi
    have hE3v0 : (0 : ℝ) ≤ E 3 v := cpb_E_nonneg (by linarith)
    have hpow : E 3 v ^ 26 ≤ (1.3e28 : ℝ) ^ 26 := pow_le_pow_left₀ hE3v0 hE3v 26
    linarith only [hpow]
  have hρ4' : ∀ v ∈ Set.Icc (uα - Real.exp (-(E 3 aa) / 100))
      (uβ + Real.exp (-(E 3 aa) / 100)), |rhoDepth 4 v| ≤ ρ4bound :=
    fun v hv => hρ4 v (hwindow4 v hv).1 (hwindow4 v hv).2
  have hZn5 : ∀ v ∈ Set.Icc (uα - Real.exp (-(E 3 aa) / 100))
      (uβ + Real.exp (-(E 3 aa) / 100)),
      |Hbar 5 v - C * QrefLimit 5 v|
        ≤ (1 + C + δ) * Real.exp (-(E 3 aa) / 25) := by
    intro v hv
    refine h5 v ?_
    rw [hσ5]
    exact hv
  have hstep4 := cpb_backward_step hC (le_refl 4)
    (Real.exp_pos (-(E 3 aa) / 100)) hαβ
    (by have h := hwin_lo 5; rw [hσ5] at h; linarith)
    (a_pos 4 aa) (fun v hv => cpb_a_mono 4 (hwindow4 v hv).1)
    (by positivity : (0 : ℝ) ≤ 4033 * (1.3e28 : ℝ) ^ 26) hQd4 hρ4' hZn5
  have h4final := hstep4 u ⟨hu1, hu2⟩
  -- ### depth-4 arithmetic and the limit `R → ∞`
  have ha41 : (1 : ℝ) ≤ a 4 aa := one_le_a haa1.le 4
  have hthird4 : 2 * ((1 + C + δ) * Real.exp (-(E 3 aa) / 25))
      / (Real.exp (-(E 3 aa) / 100) * a 4 aa)
      ≤ 2 * ((1 + C + δ) * Real.exp (-(3 * E 3 aa) / 100)) := by
    have hd : (0 : ℝ) < Real.exp (-(E 3 aa) / 100) * a 4 aa :=
      mul_pos (Real.exp_pos _) (a_pos 4 aa)
    rw [div_le_iff₀ hd]
    have hcomb : Real.exp (-(3 * E 3 aa) / 100) * Real.exp (-(E 3 aa) / 100)
        = Real.exp (-(E 3 aa) / 25) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hre : 2 * ((1 + C + δ) * Real.exp (-(3 * E 3 aa) / 100))
          * (Real.exp (-(E 3 aa) / 100) * a 4 aa)
        = 2 * ((1 + C + δ)
            * (Real.exp (-(3 * E 3 aa) / 100) * Real.exp (-(E 3 aa) / 100)))
          * a 4 aa := by ring
    have hM25 : (0 : ℝ) ≤ (1 + C + δ) * Real.exp (-(E 3 aa) / 25) :=
      mul_nonneg hM0 (Real.exp_pos _).le
    rw [hre, hcomb]
    exact le_mul_of_one_le_right (mul_nonneg (by norm_num) hM25) ha41
  have hsc4 := cpb_depth4_scalar hw97
  have hLp : C * (4033 * (1.3e28 : ℝ) ^ 26) * Real.exp (-(E 3 aa) / 100)
      + 2 * (1 + C) * Real.exp (-(3 * E 3 aa) / 100)
      ≤ (1 + C) * Real.exp (-(E 3 aa) / 109) := by
    have hL0 : (0 : ℝ) ≤ 4033 * (1.3e28 : ℝ) ^ 26 := by positivity
    have h1 : C * (4033 * (1.3e28 : ℝ) ^ 26) * Real.exp (-(E 3 aa) / 100)
        ≤ (1 + C) * (4033 * (1.3e28 : ℝ) ^ 26 * Real.exp (-(E 3 aa) / 100)) := by
      linarith only [mul_nonneg hL0 (Real.exp_pos (-(E 3 aa) / 100)).le]
    have h2 := mul_le_mul_of_nonneg_left hsc4
      (show (0 : ℝ) ≤ 1 + C by linarith only [hC])
    have hexpand : (1 + C) * (4033 * (1.3e28 : ℝ) ^ 26
          * Real.exp (-(E 3 aa) / 100) + 2 * Real.exp (-(3 * E 3 aa) / 100))
        = (1 + C) * (4033 * (1.3e28 : ℝ) ^ 26 * Real.exp (-(E 3 aa) / 100))
          + 2 * (1 + C) * Real.exp (-(3 * E 3 aa) / 100) := by ring
    linarith only [h1, h2, hexpand]
  have hδp : 2 * δ * Real.exp (-(3 * E 3 aa) / 100) ≤ δ := by
    have h2e : 2 * Real.exp (-(3 * E 3 aa) / 100) ≤ 1 := by
      have h2exp : (2 : ℝ) ≤ Real.exp (3 * E 3 aa / 100) := by
        have h := Real.add_one_le_exp (3 * E 3 aa / 100)
        have hE30 : (0 : ℝ) ≤ E 3 aa := cpb_E_nonneg haa0.le
        linarith only [h, hE30, hw97]
      have hprod : Real.exp (-(3 * E 3 aa) / 100) * Real.exp (3 * E 3 aa / 100)
          = 1 := by
        rw [cpb_exp_mul_exp
          (show -(3 * E 3 aa) / 100 + 3 * E 3 aa / 100 = 0 by ring),
          Real.exp_zero]
      have hmm := mul_le_mul_of_nonneg_left h2exp
        (Real.exp_pos (-(3 * E 3 aa) / 100)).le
      linarith only [hmm, hprod]
    linarith only [mul_le_mul_of_nonneg_left h2e hδ0]
  have hfinal : |Hbar 4 u - C * QrefLimit 4 u|
      ≤ ρ4bound + (1 + C) * Real.exp (-(E 3 aa) / 109) + δ := by
    have hsplit : 2 * ((1 + C + δ) * Real.exp (-(3 * E 3 aa) / 100))
        = 2 * (1 + C) * Real.exp (-(3 * E 3 aa) / 100)
          + 2 * δ * Real.exp (-(3 * E 3 aa) / 100) := by ring
    linarith only [h4final, hthird4, hLp, hδp, hsplit]
  rw [hE3aa] at hfinal
  -- the buffered-endpoint tail is below the paper's `exp(−w₋/110)` since
  -- `0.999/109 > 1/110`
  have htighten : Real.exp (-(0.999 * wlo) / 109) ≤ Real.exp (-(wlo) / 110) :=
    Real.exp_le_exp.mpr (by linarith)
  have hCtighten := mul_le_mul_of_nonneg_left htighten
    (show (0 : ℝ) ≤ 1 + C by linarith)
  linarith only [hfinal, hδε, hεdef, hCtighten]
