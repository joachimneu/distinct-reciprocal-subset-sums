import Erdos320.Lemmas.BackwardReferenceConvergence
import Erdos320.Lemmas.IterationLocalization
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The limiting backward reference functions (§6, `lem:backward-reference-convergence`, conclusion)

This file finishes the paper's Lemma "Convergence of the reference
functions" (`lem:backward-reference-convergence`) on top of
`Erdos320.Lemmas.BackwardReferenceConvergence`:

* **The `A_s`-proximity derivative bound** (eq. `reference-derivative-bound`):
  `abs_deriv_Qref_sub_A_le` — for `s ≥ 5`, `R ≥ s+1`,
  `u ≥ 1`, `|(Q_s^{[R]} − A_s)'| ≤ 32 A_{s-1} E_{s-3}'/E_{s-2}` (the paper's
  `E_{s-3}' = a_{s-1}`).  The exceptional increment `Δ_{5,7}` (the paper's
  "at `s = 5`, exact use of eq. `laurent-derivative`") is handled by running
  the size induction at the terminal depth `R = 7` explicitly
  (`abs_evalComb_derivIter_DeltaComb_five_seven_le`); the paper's sharp
  bound `156·E₃⁷/E₄` is not needed — the wasteful generic constants already
  fit the margin.
* **Derivative bookkeeping for `B_j = A_j'/a_j`**
  (eq. `Bj-derivative-bound`): `hasDerivAt_Bref` and `abs_deriv_Bref_le`
  (`|B_j'| ≤ 4 A_{j-1} x_{j-3}'/x_{j-2}`), which
  `Erdos320.Lemmas.BackwardReference` leaves open.
* **The limit's derivatives** — `QrefLimitIterDeriv m s` (the `m`-th
  derivative of `Q_s^*` as an explicit convergent series), with
  `hasDerivAt_QrefLimitIterDeriv` / `hasDerivAt_QrefLimit` on the *open*
  phase set `1 < u`, and the quantitative tails
  `abs_QrefLimitIterDeriv_sub_evalComb_le` (eq. `reference-increment`
  summed, for `m ≤ 2` — the paper's `C²` convergence).
* **The limit recurrence** (eq. `reference-recurrence`):
  `hasDerivAt_QrefLimit_succ` — `(Q_{s+1}^*)' = a_s Q_s^*` for `s ≥ 4`,
  `u > 1`.
* **The exact `R = 7` splitting** (behind eq. `Q47-exact`):
  `Qref_four_seven_add_correction` — `Q₄^{[7]} + 𝓛₄((A₅−B₅)/E₄) = Q̃₄` on
  positive phase, from the exact terminal identity
  `Q₅^{[7]} = A₅ + B₅ − (A₅−B₅)/E₄`.
* **The numerical tail** (eqs. `first-reference-bound`,
  `Q47-tail-majorant`, `R7-tail`): `abs_QrefLimit_four_sub_QrefCore4_le`
  and its first/second-derivative companions — the `‖Q₄^* − Q̃₄‖_{C²}`
  pieces of the paper's `< exp(−3.7·10⁶)` bound (eq. `R7-tail`) — plus the
  depth-3 value companion `‖Q₃^* − Q̃₃‖_{C⁰}` (with no displayed
  counterpart: the paper obtains its depth-3 estimates by applying `𝓛₃` to
  the C² enclosure rather than from a separate convergence statement).

Paper-vs-Lean notes:

* The paper's bounds are stated uniformly on `u ∈ [1, e]`; all *value-level*
  statements here need only `1 ≤ u` (strictly stronger).  The
  *derivative-existence* statements for the limit (`hasDerivAt_QrefLimit*`,
  the recurrence) are proved for `1 < u`: the term-by-term differentiation
  theorem (`hasDerivAt_tsum_of_isPreconnected`) needs an *open* set on which
  the uniform increment bounds hold, and those bounds are available for
  `u ≥ 1` only.  This suffices for the paper's downstream use (§8 evaluates
  the reference profile on windows `E₃⁻¹(W)`, compact subintervals of
  `(1, 2)` at positive distance from the endpoint `u = 1`); the endpoint
  values themselves are still
  controlled by the value-level bounds.
* Where the paper records an integer table for `∂^k(Q₄^{[7]} − Q̃₄)`, `U₄,₇`,
  `V₄,₇` (tab. `derivative-bounds`), this development runs the generic
  size induction at `R = 7` instead; the resulting constants are (much)
  larger than the paper's sharp `1299·E₃¹⁰/E₄ + 2758·E₄¹⁵/E₅`
  (eq. `first-reference-bound`) but still clear the `exp(−3.7·10⁶)` margin
  with room to spare, so the sharp table is not load-bearing for eq. `R7-tail`.
-/

namespace Erdos320

/-! ## Elementary comparison helpers -/

/-- `A_s ≥ 1` on positive phase (the cumulative sum is `1` plus positive
terms). -/
theorem one_le_A {u : ℝ} (hu : 0 < u) (s : ℕ) : (1 : ℝ) ≤ A s u := by
  unfold A
  have h : 0 ≤ ∑ j ∈ Finset.Icc 3 s, D j u :=
    Finset.sum_nonneg fun j _ => (D_pos hu j).le
  linarith

/-- `a_r ≥ 1` for `u ≥ 1` (every factor `E_j ≥ 1`). -/
theorem one_le_a {u : ℝ} (hu : 1 ≤ u) (r : ℕ) : (1 : ℝ) ≤ a r u := by
  unfold a
  have h := Finset.prod_le_prod (f := fun _ : ℕ => (1 : ℝ))
    (g := fun j => E j u) (s := Finset.Icc 1 (r - 2))
    (fun i _ => zero_le_one) (fun i _ => one_le_E_of_one_le hu i)
  simpa using h

/-- `D_r ≤ A_r` for `r ≥ 3` on positive phase (`D_r` is one of the summands
of `A_r`). -/
theorem D_le_A {r : ℕ} (hr : 3 ≤ r) {u : ℝ} (hu : 0 < u) : D r u ≤ A r u := by
  unfold A
  have h : D r u ≤ ∑ j ∈ Finset.Icc 3 r, D j u :=
    Finset.single_le_sum (fun j _ => (D_pos hu j).le)
      (Finset.mem_Icc.mpr ⟨hr, le_rfl⟩)
  linarith

/-- `A_s ≤ (1 + E_{s-3}) A_{s-1}` for `s ≥ 4` (the paper's
"use `A_s ≤ (1 + x_{s-3}) A_{s-1}`", proof of
`lem:backward-reference-convergence`). -/
theorem A_le_one_add_E_mul {s : ℕ} (hs : 4 ≤ s) {u : ℝ} (hu : 0 < u) :
    A s u ≤ (1 + E (s - 3) u) * A (s - 1) u := by
  have hA : A s u = A (s - 1) u + D s u := by
    have h := A_succ (s := s - 1) (by omega) u
    rw [show s - 1 + 1 = s by omega] at h
    exact h
  have hD : D s u = D (s - 1) u * E (s - 3) u := by
    have h := D_succ (r := s - 1) (by omega) u
    rw [show s - 1 + 1 = s by omega, show s - 1 - 2 = s - 3 by omega] at h
    exact h
  have hDA : D (s - 1) u ≤ A (s - 1) u := D_le_A (by omega) hu
  have hE : (0 : ℝ) < E (s - 3) u := E_pos_of_pos hu _
  nlinarith [A_pos hu (s - 1)]

/-- `3.8·10⁶ ≤ E_j(u)` for `j ≥ 3`, `u ≥ 1` (via the certified
`E₃(1) > 3.8·10⁶`). -/
theorem big_le_E {j : ℕ} (hj : 3 ≤ j) {u : ℝ} (hu : 1 ≤ u) :
    (3.8e6 : ℝ) ≤ E j u :=
  calc (3.8e6 : ℝ) ≤ E 3 1 := E_three_one_gt.le
    _ ≤ E 3 u := E_mono 3 hu
    _ ≤ E j u := E_mono_depth hu hj

/-! ## Elementary exponential estimates

The "elementary inequality" the paper invokes with `x = x_{s-3}`,
`X = e^x`, `Y = e^X`: `(x + 2) X² ≤ Y` (proof of
`lem:backward-reference-convergence`; the paper asks for `x ≥ e^e`, here
`x ≥ 15` suffices). -/

/-- `(x + 2) (e^x)² ≤ e^{e^x}` for `x ≥ 15`. -/
theorem add_two_mul_exp_sq_le_exp_exp {x : ℝ} (hx : 15 ≤ x) :
    (x + 2) * Real.exp x ^ 2 ≤ Real.exp (Real.exp x) := by
  set X := Real.exp x
  have hX0 : (0 : ℝ) < X := Real.exp_pos x
  have h2x : 2 * x ≤ X := two_mul_le_exp (by linarith)
  have hquart : X ^ 4 / 24 ≤ Real.exp X := by
    have h := pow_div_factorial_le_exp hX0.le 4
    have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num
    rwa [hfac] at h
  have h6 : 24 * (x + 2) ≤ X ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ X - 2 * x)
      (by linarith : (0 : ℝ) ≤ X + 2 * x)]
  have h7 : 24 * (x + 2) * X ^ 2 ≤ X ^ 2 * X ^ 2 :=
    mul_le_mul_of_nonneg_right h6 (sq_nonneg X)
  nlinarith [h7, hquart]

/-- `T¹⁰² ≤ e^{T/100}` once `T ≥ 3.8·10⁶` (via `T ≤ e^{T/10200}`): the
"take logarithms" step for the `R = 7` numerics (eq. `Q47-tail-majorant`). -/
theorem pow_hundredtwo_le_exp_div_hundred {T : ℝ} (hT : 3.8e6 ≤ T) :
    T ^ 102 ≤ Real.exp (T / 100) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hy0 : (0 : ℝ) ≤ T / 10200 := by positivity
  have hcube : (T / 10200) ^ 3 / 6 ≤ Real.exp (T / 10200) := by
    have h := pow_div_factorial_le_exp hy0 3
    have hfac : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num
    rwa [hfac] at h
  have hT2 : (6367248000000 : ℝ) ≤ T ^ 2 := by nlinarith
  have h2 : (6367248000000 : ℝ) * T ≤ T ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hT2 hT0.le]
  have hTle : T ≤ Real.exp (T / 10200) := by
    have h3 : (T / 10200) ^ 3 / 6 = T ^ 3 / 6367248000000 := by ring
    have h4 : T ≤ T ^ 3 / 6367248000000 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6367248000000)]
      linarith
    linarith [hcube, h3 ▸ hcube]
  calc T ^ 102 ≤ Real.exp (T / 10200) ^ 102 :=
        pow_le_pow_left₀ hT0.le hTle 102
    _ = Real.exp ((102 : ℕ) * (T / 10200)) := (Real.exp_nat_mul _ 102).symm
    _ = Real.exp (T / 100) := by
        congr 1
        push_cast
        ring

/-- `e^{-5} ≤ 1/32` (from `2⁵ ≤ e⁵`). -/
theorem exp_neg_five_le : Real.exp (-5 : ℝ) ≤ 1 / 32 := by
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h32 : (32 : ℝ) ≤ Real.exp 5 := by
    have h1 : (2 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h2e 5
    have h2 : Real.exp 1 ^ 5 = Real.exp ((5 : ℕ) * 1) := (Real.exp_nat_mul _ 5).symm
    norm_num at h1 h2
    linarith
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 32) h32
  rwa [Real.exp_neg, inv_eq_one_div]

/-- **Master numeric estimate** for the `R = 7` tail: any error of the shape
`C·Tⁿ/e^T` with `T ≥ 3.8·10⁶`, `n ≤ 100`, `C ≤ T²` is below an eighth of
the target `exp(−3.7·10⁶)` of eq. `R7-tail`. -/
theorem poly_div_exp_le_target {T C : ℝ} (hT : 3.8e6 ≤ T) {n : ℕ}
    (hn : n ≤ 100) (hC : C ≤ T ^ 2) :
    C * T ^ n / Real.exp T ≤ Real.exp (-(3.7e6 : ℝ)) / 8 := by
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hnum : C * T ^ n ≤ T ^ 102 := by
    calc C * T ^ n ≤ T ^ 2 * T ^ 100 :=
          mul_le_mul hC (pow_le_pow_right₀ hT1 hn) (pow_nonneg hT0.le n)
            (by positivity)
      _ = T ^ 102 := by ring
  have h6 : Real.exp (-(3.7e6 : ℝ)) * Real.exp (-5 : ℝ)
      ≤ Real.exp (-(3.7e6 : ℝ)) / 8 := by
    have h32 := mul_le_mul_of_nonneg_left exp_neg_five_le
      (Real.exp_pos (-(3.7e6 : ℝ))).le
    have hp := (Real.exp_pos (-(3.7e6 : ℝ))).le
    linarith
  calc C * T ^ n / Real.exp T
      ≤ Real.exp (T / 100) / Real.exp T :=
        div_le_div_of_nonneg_right
          (hnum.trans (pow_hundredtwo_le_exp_div_hundred hT)) (Real.exp_pos T).le
    _ = Real.exp (T / 100 - T) := (Real.exp_sub _ _).symm
    _ ≤ Real.exp (-(3.7e6 : ℝ) - 5) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(3.7e6 : ℝ)) * Real.exp (-5 : ℝ) := by
        rw [sub_eq_add_neg, Real.exp_add]
    _ ≤ Real.exp (-(3.7e6 : ℝ)) / 8 := h6

/-- The residual increments beyond `R = 8` are below the eq. `R7-tail`
target: `4 e^{-E₄(u)/2} ≤ exp(−3.7·10⁶)/8` for `u ≥ 1`. -/
theorem four_mul_exp_neg_E_four_half_le_target {u : ℝ} (hu : 1 ≤ u) :
    4 * Real.exp (-(E 4 u) / 2) ≤ Real.exp (-(3.7e6 : ℝ)) / 8 := by
  have hT : (3.8e6 : ℝ) ≤ E 3 u := big_le_E (by omega) hu
  have hE4 : E 4 u = Real.exp (E 3 u) := E_succ 3 u
  have hsq : E 3 u ^ 2 / 2 ≤ Real.exp (E 3 u) := by
    have h := pow_div_factorial_le_exp (by linarith : (0 : ℝ) ≤ E 3 u) 2
    have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
    rwa [hfac] at h
  have hbig : 2 * ((3.7e6 : ℝ) + 5) ≤ Real.exp (E 3 u) := by nlinarith
  have h3 : -(E 4 u) / 2 ≤ -(3.7e6 : ℝ) - 5 := by rw [hE4]; linarith
  have h4 : Real.exp (-(E 4 u) / 2) ≤ Real.exp (-(3.7e6 : ℝ) - 5) :=
    Real.exp_le_exp.mpr h3
  have h5 : Real.exp (-(3.7e6 : ℝ) - 5)
      = Real.exp (-(3.7e6 : ℝ)) * Real.exp (-5 : ℝ) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have h6 : 4 * (Real.exp (-(3.7e6 : ℝ)) * Real.exp (-5 : ℝ))
      ≤ Real.exp (-(3.7e6 : ℝ)) / 8 := by
    have hp := (Real.exp_pos (-(3.7e6 : ℝ))).le
    nlinarith [exp_neg_five_le, Real.exp_pos (-5 : ℝ)]
  calc 4 * Real.exp (-(E 4 u) / 2) ≤ 4 * Real.exp (-(3.7e6 : ℝ) - 5) := by
        linarith
    _ = 4 * (Real.exp (-(3.7e6 : ℝ)) * Real.exp (-5 : ℝ)) := by rw [h5]
    _ ≤ Real.exp (-(3.7e6 : ℝ)) / 8 := h6

/-- `4 e^{-E_j(u)/2} ≤ 1/E_j(u)` for `j ≥ 3`, `u ≥ 1`: absorbs the residual
increment series into a single `b_s`-sized quantity
(eq. `reference-derivative-bound` bookkeeping). -/
theorem four_mul_exp_neg_E_half_le_inv {j : ℕ} (hj : 3 ≤ j) {u : ℝ}
    (hu : 1 ≤ u) :
    4 * Real.exp (-(E j u) / 2) ≤ 1 / E j u := by
  have hT : (20 : ℝ) ≤ E j u := twenty_le_E hj hu
  have hsq : E j u ^ 2 ≤ Real.exp (E j u / 2) := sq_le_exp_half hT
  have hpos : (0 : ℝ) < E j u := by linarith
  have h1 : Real.exp (-(E j u) / 2) = (Real.exp (E j u / 2))⁻¹ := by
    rw [neg_div, Real.exp_neg]
  have h2 : (Real.exp (E j u / 2))⁻¹ ≤ (E j u ^ 2)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hsq
  have h3 : 4 * (E j u ^ 2)⁻¹ ≤ 1 / E j u := by
    rw [inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity) hpos]
    nlinarith
  calc 4 * Real.exp (-(E j u) / 2) = 4 * (Real.exp (E j u / 2))⁻¹ := by rw [h1]
    _ ≤ 4 * (E j u ^ 2)⁻¹ := by linarith [h2]
    _ ≤ 1 / E j u := h3

/-! ## The derivative bound for `B_j` (eq. `Bj-derivative-bound`)

`Erdos320.Lemmas.BackwardReference` proved the value bounds
`0 ≤ B_j ≤ A_{j-1}` (`Bref_nonneg`, `Bref_le_A_pred`); here we add the
derivative bound
`|B_j'| ≤ 4 A_{j-1} x_{j-3}'/x_{j-2}` (with `x_{j-3}' = a_{j-1}`), via the
formal Laurent representation of `B_j`. -/

/-- `BrefComb j`: the normalized derivative `B_j = A_j'/a_j = 𝓛_j A_j` as a
formal Laurent combination. -/
noncomputable def BrefComb (j : ℕ) : LaurentComb :=
  shiftComb (aVec j) (derivComb (AComb j))

/-- `A_s` is the evaluation of its formal representation (as functions; all
exponents are nonnegative, so no positivity of the phase is needed). -/
theorem A_eq_evalComb (s : ℕ) : A s = evalComb (AComb s) :=
  funext fun u => (evalComb_AComb s u).symm

/-- On positive phase, `B_j` evaluates its comb representation. -/
theorem Bref_eq_evalComb {j : ℕ} {u : ℝ} (hu : 0 < u) :
    Bref j u = evalComb (BrefComb j) u := by
  have h : Bref j u = Lop j (A j) u := rfl
  rw [h, A_eq_evalComb j]
  unfold BrefComb
  exact Lop_evalComb j (AComb j) hu

/-- `B_j` is differentiable at every positive phase, with derivative the
evaluation of the formally differentiated comb. -/
theorem hasDerivAt_Bref (j : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (Bref j) (evalComb (derivComb (BrefComb j)) u) u := by
  refine (hasDerivAt_evalComb hu (BrefComb j)).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact Bref_eq_evalComb hv

/-- `B₃ = 1/E₁` in closed form. -/
theorem Bref_three_eq : Bref 3 = fun v => 1 / E 1 v := by
  funext v
  unfold Bref
  rw [(hasDerivAt_A 3 v).deriv, Finset.Icc_self, Finset.sum_singleton,
    show (3 : ℕ) - 1 = 2 from rfl, a_two, A_two, mul_one, a_three]

/-- **The derivative bound of eq. `Bj-derivative-bound`**:
`|B_j'| ≤ 4 A_{j-1} a_{j-1} / E_{j-2}` for `j ≥ 3`, `u ≥ 1` (the paper's
`x_{j-3}'` is `a_{j-1}`; the paper starts the induction at `j = 4`, but the
same form already holds at `j = 3`). -/
theorem abs_deriv_Bref_le {j : ℕ} (hj : 3 ≤ j) {u : ℝ} (hu : 1 ≤ u) :
    |deriv (Bref j) u| ≤ 4 * A (j - 1) u * a (j - 1) u / E (j - 2) u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  induction j, hj using Nat.le_induction with
  | base =>
      have hE1 : HasDerivAt (E 1) (a 3 u) u := hasDerivAt_E_sub_two 3 u
      have hE1pos : (0 : ℝ) < E 1 u := E_pos_of_one_le (by omega) u
      have hD : HasDerivAt (Bref 3) ((0 * E 1 u - 1 * a 3 u) / E 1 u ^ 2) u := by
        rw [Bref_three_eq]
        exact (hasDerivAt_const u (1 : ℝ)).div hE1 hE1pos.ne'
      have hval : (0 * E 1 u - 1 * a 3 u) / E 1 u ^ 2 = -(E 1 u / E 1 u ^ 2) := by
        rw [a_three]
        ring
      rw [hD.deriv, hval, show (3 : ℕ) - 1 = 2 from rfl,
        show (3 : ℕ) - 2 = 1 from rfl, A_two, a_two, abs_neg,
        abs_of_pos (by positivity : (0 : ℝ) < E 1 u / E 1 u ^ 2),
        div_le_div_iff₀ (by positivity) hE1pos]
      nlinarith
  | succ j hj ih =>
      -- the recursion `B_{j+1} = (A_j + B_j)/E_{j-1}` as a function identity
      have hrec : Bref (j + 1) = fun v => (A j v + Bref j v) / E (j - 1) v := by
        funext v
        have h := Bref_recursion (j := j + 1) (by omega) v
        rw [show j + 1 - 1 = j by omega, show j + 1 - 2 = j - 1 by omega] at h
        exact h
      have hBd : HasDerivAt (Bref j) (deriv (Bref j) u) u :=
        (hasDerivAt_Bref j hu0).differentiableAt.hasDerivAt
      have hE : HasDerivAt (E (j - 1)) (a (j + 1) u) u := by
        have h := hasDerivAt_E_sub_two (j + 1) u
        rw [show j + 1 - 2 = j - 1 by omega] at h
        exact h
      have hYpos : (0 : ℝ) < E (j - 1) u := E_pos_of_one_le (by omega) u
      have hD : HasDerivAt (Bref (j + 1))
          (((a j u * Bref j u + deriv (Bref j) u) * E (j - 1) u
              - (A j u + Bref j u) * a (j + 1) u) / E (j - 1) u ^ 2) u := by
        rw [hrec]
        exact ((hasDerivAt_A_Bref j u).add hBd).div hE hYpos.ne'
      rw [hD.deriv, show j + 1 - 1 = j by omega, show j + 1 - 2 = j - 1 by omega]
      -- notation
      have haj : a (j + 1) u = a j u * E (j - 1) u := a_succ (by omega) u
      have hajX : a j u = a (j - 1) u * E (j - 2) u := by
        have h := a_succ (r := j - 1) (by omega) u
        rw [show j - 1 + 1 = j by omega, show j - 1 - 1 = j - 2 by omega] at h
        exact h
      have hXpos : (0 : ℝ) < E (j - 2) u := E_pos_of_one_le (by omega) u
      have hX2 : (2 : ℝ) ≤ E (j - 2) u := two_le_E (by omega) hu
      have hapos : (0 : ℝ) < a j u := a_pos j u
      have hapos' : (0 : ℝ) < a (j - 1) u := a_pos (j - 1) u
      have hApos : (0 : ℝ) < A j u := A_pos hu0 j
      have hApos' : (0 : ℝ) < A (j - 1) u := A_pos hu0 (j - 1)
      have hB0 : 0 ≤ Bref j u := Bref_nonneg hu0 j
      have hBA : Bref j u ≤ A (j - 1) u := Bref_le_A_pred (by omega) hu
      have hAA : A (j - 1) u ≤ A j u := A_mono_index hu0 (by omega)
      -- simplify the derivative value
      have hval : ((a j u * Bref j u + deriv (Bref j) u) * E (j - 1) u
            - (A j u + Bref j u) * a (j + 1) u) / E (j - 1) u ^ 2
          = (a j u * Bref j u + deriv (Bref j) u) / E (j - 1) u
            - (A j u + Bref j u) * a j u / E (j - 1) u := by
        rw [haj]
        field_simp
      rw [hval]
      -- bound the two pieces
      have hIH2 : |deriv (Bref j) u| ≤ A j u * a j u := by
        refine ih.trans ?_
        rw [div_le_iff₀ hXpos]
        have hX4 : (4 : ℝ) ≤ E (j - 2) u ^ 2 := by nlinarith
        have he1 : A j u * a j u * E (j - 2) u
            = A j u * a (j - 1) u * E (j - 2) u ^ 2 := by
          rw [hajX]
          ring
        rw [he1]
        calc 4 * A (j - 1) u * a (j - 1) u
            = A (j - 1) u * a (j - 1) u * 4 := by ring
          _ ≤ A (j - 1) u * a (j - 1) u * E (j - 2) u ^ 2 :=
              mul_le_mul_of_nonneg_left hX4 (by positivity)
          _ ≤ A j u * a (j - 1) u * E (j - 2) u ^ 2 := by
              have h := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hAA hapos'.le)
                (by positivity : (0 : ℝ) ≤ E (j - 2) u ^ 2)
              linarith
      have hterm1 : |(a j u * Bref j u + deriv (Bref j) u) / E (j - 1) u|
          ≤ 2 * (A j u * a j u) / E (j - 1) u := by
        rw [abs_div, abs_of_pos hYpos]
        refine div_le_div_of_nonneg_right ?_ hYpos.le
        calc |a j u * Bref j u + deriv (Bref j) u|
            ≤ |a j u * Bref j u| + |deriv (Bref j) u| := abs_add_le _ _
          _ ≤ A j u * a j u + A j u * a j u := by
              refine add_le_add ?_ hIH2
              rw [abs_of_nonneg (mul_nonneg hapos.le hB0)]
              nlinarith
          _ = 2 * (A j u * a j u) := by ring
      have hterm2 : |(A j u + Bref j u) * a j u / E (j - 1) u|
          ≤ 2 * (A j u * a j u) / E (j - 1) u := by
        rw [abs_div, abs_of_pos hYpos]
        refine div_le_div_of_nonneg_right ?_ hYpos.le
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (A j u + Bref j u) * a j u)]
        nlinarith
      calc |(a j u * Bref j u + deriv (Bref j) u) / E (j - 1) u
            - (A j u + Bref j u) * a j u / E (j - 1) u|
          ≤ |(a j u * Bref j u + deriv (Bref j) u) / E (j - 1) u|
            + |(A j u + Bref j u) * a j u / E (j - 1) u| := abs_sub _ _
        _ ≤ 2 * (A j u * a j u) / E (j - 1) u
            + 2 * (A j u * a j u) / E (j - 1) u := add_le_add hterm1 hterm2
        _ = 4 * A j u * a j u / E (j - 1) u := by ring

/-! ## Size-invariant helpers

Extensions of the `CombSizeBound` calculus of
`Erdos320.Lemmas.BackwardReferenceConvergence` needed to run the size
induction at the exceptional terminal depth `R = 7` and on the reference
core correction (eqs. `first-reference-bound`, `Q47-tail-majorant`). -/

/-- Relaxing the index bound of the bundled size invariant. -/
theorem CombSizeBound.mono_t {t t' h l : ℕ} {P : LaurentComb}
    (hP : CombSizeBound t h l P) (ht : t ≤ t') : CombSizeBound t' h l P :=
  ⟨le_trans hP.maxIdx_le ht,
    fun ν hν j hj => le_trans (hP.pos_index_le ν hν j hj) ht,
    hP.combHeight_le, hP.l1Norm_le⟩

/-- The size invariant of a sum of combinations. -/
theorem CombSizeBound.add {t h₁ h₂ l₁ l₂ : ℕ} {P Q : LaurentComb}
    (hP : CombSizeBound t h₁ l₁ P) (hQ : CombSizeBound t h₂ l₂ Q) :
    CombSizeBound t (max h₁ h₂) (l₁ + l₂) (P + Q) := by
  have hsupp : ∀ ν ∈ (P + Q).support, ν ∈ P.support ∨ ν ∈ Q.support :=
    fun ν hν => Finset.mem_union.mp (Finsupp.support_add hν)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Finset.sup_le fun ν hν => ?_
    rcases hsupp ν hν with h | h
    · exact le_trans (Finset.le_sup h) hP.maxIdx_le
    · exact le_trans (Finset.le_sup h) hQ.maxIdx_le
  · intro ν hν j hj
    rcases hsupp ν hν with h | h
    · exact hP.pos_index_le ν h j hj
    · exact hQ.pos_index_le ν h j hj
  · refine Finset.sup_le fun ν hν => ?_
    rcases hsupp ν hν with h | h
    · exact le_trans (height_le_combHeight h)
        (le_trans hP.combHeight_le (le_max_left _ _))
    · exact le_trans (height_le_combHeight h)
        (le_trans hQ.combHeight_le (le_max_right _ _))
  · exact le_trans (l1Norm_add_le P Q) (Nat.add_le_add hP.l1Norm_le hQ.l1Norm_le)

/-- Negation preserves the coefficient ℓ¹-norm. -/
theorem l1Norm_neg (P : LaurentComb) : l1Norm (-P) = l1Norm P := by
  unfold l1Norm
  rw [Finsupp.support_neg]
  exact Finset.sum_congr rfl fun ν _ => by rw [Finsupp.neg_apply, Int.natAbs_neg]

/-- The size invariant is preserved by negation (same support, same
exponent vectors, same coefficient magnitudes). -/
theorem CombSizeBound.neg {t h l : ℕ} {P : LaurentComb}
    (hP : CombSizeBound t h l P) : CombSizeBound t h l (-P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show maxIdx (-P) ≤ t
    unfold maxIdx
    rw [Finsupp.support_neg]
    exact hP.maxIdx_le
  · intro ν hν j hj
    rw [Finsupp.support_neg] at hν
    exact hP.pos_index_le ν hν j hj
  · show combHeight (-P) ≤ h
    unfold combHeight
    rw [Finsupp.support_neg]
    exact hP.combHeight_le
  · rw [l1Norm_neg]
    exact hP.l1Norm_le

/-- The size invariant of a difference of combinations. -/
theorem CombSizeBound.sub {t h₁ h₂ l₁ l₂ : ℕ} {P Q : LaurentComb}
    (hP : CombSizeBound t h₁ l₁ P) (hQ : CombSizeBound t h₂ l₂ Q) :
    CombSizeBound t (max h₁ h₂) (l₁ + l₂) (P - Q) := by
  rw [sub_eq_add_neg]
  exact hP.add hQ.neg

/-- Division by a single variable `x_j` with `j ≤ t`: height grows by one,
the norm and the index invariants persist. -/
theorem CombSizeBound.shift_single {t h l : ℕ} {P : LaurentComb}
    (hP : CombSizeBound t h l P) {j : ℕ} (hj : j ≤ t) :
    CombSizeBound t (h + 1) l (shiftComb (Finsupp.single j 1) P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans (maxIdx_shiftComb_le _ _) (max_le hP.maxIdx_le ?_)
    exact le_trans (vecMaxIdx_single_le _ _) hj
  · intro ν' hν' i hi
    obtain ⟨ν, hν, rfl⟩ := mem_shiftComb_support hν'
    rw [Finsupp.sub_apply] at hi
    have hnn : (0 : ℤ) ≤ (Finsupp.single j (1 : ℤ)) i := by
      rw [Finsupp.single_apply]
      split <;> omega
    exact hP.pos_index_le ν hν i (by omega)
  · refine le_trans (combHeight_shiftComb_le _ _) ?_
    have h1 := hP.combHeight_le
    have h2 : height (Finsupp.single j (1 : ℤ)) = 1 := by
      rw [height_single]
      rfl
    omega
  · rw [l1Norm_shiftComb]
    exact hP.l1Norm_le

/-- Size invariant of the seed `AComb s` (the paper's size induction: the initial
Laurent polynomials have coefficient norm and height below `R`). -/
theorem AComb_sizeBound {s : ℕ} (hs : 2 ≤ s) :
    CombSizeBound (s - 2) (s - 2) (s - 1) (AComb s) := by
  refine ⟨le_trans (maxIdx_AComb_le s) (by omega), ?_,
    combHeight_AComb_le s, l1Norm_AComb_le hs⟩
  intro ν hν j hj
  have hjmem : j ∈ ν.support := Finsupp.mem_support_iff.mpr (by omega)
  have h := AComb_support_index_le hν j hjmem
  omega

/-- Evaluation bound from a bundled size invariant with a persistent
terminal inverse factor `x_t^{-1}`:
`|evalComb P u| ≤ l · E_{t-1}(u)^h / E_t(u)` (the paper's passage from the
bookkeeping table to eqs. `late-U-bound`/`late-V-bound` and
`first-reference-bound`). -/
theorem abs_evalComb_le_of_sizeBound {t h l : ℕ} {P : LaurentComb}
    (hP : CombSizeBound t h l P) (hneg : ∀ ν ∈ P.support, ν t ≤ -1)
    {u : ℝ} (hu : 1 ≤ u) :
    |evalComb P u| ≤ (l : ℝ) * E (t - 1) u ^ h / E t u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hxmax : (1 : ℝ) ≤ E (t - 1) u := one_le_E_of_one_le hu _
  have hbound : ∀ ν ∈ P.support, ∀ j ∈ ν.support, 0 < ν j
      → E j u ≤ E (t - 1) u := by
    intro ν hν j _ hj
    have h := hP.pos_index_le ν hν j hj
    exact E_mono_depth hu (by omega)
  refine (abs_evalComb_le_div hu hxmax hbound hneg).trans ?_
  refine div_le_div_of_nonneg_right ?_ (E_pos_of_pos hu0 t).le
  have hl : (l1Norm P : ℝ) ≤ (l : ℝ) := Nat.cast_le.mpr hP.l1Norm_le
  have hpd : combPosDeg P ≤ h :=
    le_trans (combPosDeg_le_combHeight P) hP.combHeight_le
  exact mul_le_mul hl (pow_le_pow_right₀ hxmax hpd)
    (pow_nonneg (by linarith) _) (Nat.cast_nonneg l)

/-! ## The exceptional terminal depth `R = 7`

The general size induction of `BackwardReferenceConvergence` is packaged
with the hypothesis `8 ≤ R` (which is all the paper's all-depth argument
needs); the finitely many backward steps at `R = 7` are unrolled here by
hand — three `backward_step`s from the seeds, exactly the computation the
paper's symbolic program performs (`sec:reproducibility`), but with the
generic, deliberately wasteful constants. -/

private theorem UCombAux_zero_seven_sizeBound :
    CombSizeBound 4 3 4 (UCombAux 0 7) := by
  rw [UCombAux_zero]
  exact (AComb_sizeBound (by norm_num : 2 ≤ 5)).mono_t (by norm_num)

private theorem UCombAux_one_seven_sizeBound :
    CombSizeBound 4 12 12 (UCombAux 1 7) := by
  have h := UCombAux_zero_seven_sizeBound.backward_step
    (r := 7 - (0 + 1)) (by norm_num)
  rw [← UCombAux_succ] at h
  exact h

private theorem UCombAux_two_seven_sizeBound :
    CombSizeBound 4 21 144 (UCombAux 2 7) := by
  have h := UCombAux_one_seven_sizeBound.backward_step
    (r := 7 - (1 + 1)) (by norm_num)
  rw [← UCombAux_succ] at h
  exact h

private theorem UCombAux_three_seven_sizeBound :
    CombSizeBound 4 30 3024 (UCombAux 3 7) := by
  have h := UCombAux_two_seven_sizeBound.backward_step
    (r := 7 - (2 + 1)) (by norm_num)
  rw [← UCombAux_succ] at h
  exact h

private theorem VCombAux_zero_seven_sizeBound :
    CombSizeBound 5 5 5 (VCombAux 0 7) := by
  rw [VCombAux_zero]
  exact ((AComb_sizeBound (by norm_num : 2 ≤ 6)).mono_t
    (by norm_num)).shift_single (by norm_num)

private theorem VCombAux_one_seven_sizeBound :
    CombSizeBound 5 16 25 (VCombAux 1 7) := by
  have h := VCombAux_zero_seven_sizeBound.backward_step
    (r := 7 - (0 + 1)) (by norm_num)
  rw [← VCombAux_succ] at h
  exact h

private theorem VCombAux_two_seven_sizeBound :
    CombSizeBound 5 27 400 (VCombAux 2 7) := by
  have h := VCombAux_one_seven_sizeBound.backward_step
    (r := 7 - (1 + 1)) (by norm_num)
  rw [← VCombAux_succ] at h
  exact h

private theorem VCombAux_three_seven_sizeBound :
    CombSizeBound 5 38 10800 (VCombAux 3 7) := by
  have h := VCombAux_two_seven_sizeBound.backward_step
    (r := 7 - (2 + 1)) (by norm_num)
  rw [← VCombAux_succ] at h
  exact h

private theorem UCombAux_one_seven_neg :
    ∀ μ ∈ (UCombAux 1 7).support, μ 4 ≤ -1 := by
  intro μ hμ
  rw [UCombAux_succ, UCombAux_zero] at hμ
  obtain ⟨ν', hν', rfl⟩ := mem_shiftComb_support hμ
  have hν4 : ν' 4 ≤ 0 := by
    obtain ⟨ν, hν, i, hi, rfl⟩ := exists_of_mem_derivComb_support hν'
    have h0 : ν 4 = 0 := AComb_apply_eq_zero hν (by norm_num)
    have hi2 : i ≤ 4 := by
      have h := AComb_support_index_le hν i hi
      omega
    have hds := derivShift_apply_nonpos hi2
    rw [Finsupp.add_apply]
    omega
  have haV : aVec (7 - (0 + 1)) 4 = 1 := by
    show stairVec (7 - (0 + 1) - 2) 4 = 1
    rw [stairVec_apply, if_pos (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)]
  rw [Finsupp.sub_apply, haV]
  omega

private theorem UCombAux_two_seven_neg :
    ∀ μ ∈ (UCombAux 2 7).support, μ 4 ≤ -1 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, UCombAux_succ]
  exact shiftComb_apply_le_neg_one (aVec_apply_nonneg _ _)
    (derivComb_apply_le_neg_one UCombAux_one_seven_sizeBound.maxIdx_le
      UCombAux_one_seven_neg)

private theorem UCombAux_three_seven_neg :
    ∀ μ ∈ (UCombAux 3 7).support, μ 4 ≤ -1 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, UCombAux_succ]
  exact shiftComb_apply_le_neg_one (aVec_apply_nonneg _ _)
    (derivComb_apply_le_neg_one UCombAux_two_seven_sizeBound.maxIdx_le
      UCombAux_two_seven_neg)

private theorem VCombAux_zero_seven_neg :
    ∀ μ ∈ (VCombAux 0 7).support, μ 5 ≤ -1 := by
  intro μ hμ
  rw [VCombAux_zero] at hμ
  obtain ⟨ν, hν, rfl⟩ := mem_shiftComb_support hμ
  have h0 : ν 5 = 0 := AComb_apply_eq_zero hν (by norm_num)
  have h1 : (Finsupp.single (7 - 2 : ℕ) (1 : ℤ)) 5 = 1 := by
    rw [show (7 : ℕ) - 2 = 5 from rfl, Finsupp.single_eq_same]
  rw [Finsupp.sub_apply, h0, h1]
  norm_num

private theorem VCombAux_one_seven_neg :
    ∀ μ ∈ (VCombAux 1 7).support, μ 5 ≤ -1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, VCombAux_succ]
  exact shiftComb_apply_le_neg_one (aVec_apply_nonneg _ _)
    (derivComb_apply_le_neg_one VCombAux_zero_seven_sizeBound.maxIdx_le
      VCombAux_zero_seven_neg)

private theorem VCombAux_two_seven_neg :
    ∀ μ ∈ (VCombAux 2 7).support, μ 5 ≤ -1 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, VCombAux_succ]
  exact shiftComb_apply_le_neg_one (aVec_apply_nonneg _ _)
    (derivComb_apply_le_neg_one VCombAux_one_seven_sizeBound.maxIdx_le
      VCombAux_one_seven_neg)

private theorem VCombAux_three_seven_neg :
    ∀ μ ∈ (VCombAux 3 7).support, μ 5 ≤ -1 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, VCombAux_succ]
  exact shiftComb_apply_le_neg_one (aVec_apply_nonneg _ _)
    (derivComb_apply_le_neg_one VCombAux_two_seven_sizeBound.maxIdx_le
      VCombAux_two_seven_neg)

/-- Any `C·E_j(u)ⁿ/E_{j+1}(u)` with `j ≥ 3`, `n ≤ 100`, `2C ≤ E_j(u)²` is
below `e^{-E_j(u)/2}/2` (the "take logarithms" absorption at depth `7`). -/
theorem poly_div_E_succ_le_exp_neg_half {j : ℕ} (hj : 3 ≤ j) {u : ℝ}
    (hu : 1 ≤ u) {C : ℝ} {n : ℕ} (hn : n ≤ 100) (hC : 2 * C ≤ E j u ^ 2) :
    C * E j u ^ n / E (j + 1) u ≤ Real.exp (-(E j u) / 2) / 2 := by
  have hT : (3.8e6 : ℝ) ≤ E j u := big_le_E hj hu
  have hT1 : (1 : ℝ) ≤ E j u := by linarith
  have hE : E (j + 1) u = Real.exp (E j u) := E_succ j u
  have h1 : 2 * C * E j u ^ n ≤ E j u ^ 102 := by
    calc 2 * C * E j u ^ n ≤ E j u ^ 2 * E j u ^ 100 :=
          mul_le_mul hC (pow_le_pow_right₀ hT1 hn)
            (pow_nonneg (by linarith) n) (by positivity)
      _ = E j u ^ 102 := by ring
  have h2 : E j u ^ 102 ≤ Real.exp (E j u / 2) :=
    (pow_hundredtwo_le_exp_div_hundred hT).trans
      (Real.exp_le_exp.mpr (by linarith))
  rw [hE, div_le_div_iff₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2)]
  have h4 : Real.exp (-(E j u) / 2) * Real.exp (E j u)
      = Real.exp (E j u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h4]
  linarith

/-- **The exceptional increment `Δ₅,₇` and its derivatives** (the paper's
"At `s = 5`, exact use of eq. `laurent-derivative` gives
`|∂_u Δ_{5,7}| ≤ 156 E₃⁷/E₄`"): with the generic (wasteful) constants,
`|∂^m Δ_{5,7}| ≤ e^{-E₃(u)/2}` for `m ≤ 2`, `u ≥ 1` — which is all the
`b₅`-margin needs. -/
theorem abs_evalComb_derivIter_DeltaComb_five_seven_le {m : ℕ} (hm : m ≤ 2)
    {u : ℝ} (hu : 1 ≤ u) :
    |evalComb (derivComb^[m] (DeltaComb 5 7)) u|
      ≤ Real.exp (-(E 3 u) / 2) := by
  have hT3 : (3.8e6 : ℝ) ≤ E 3 u := big_le_E (by omega) hu
  have hT4 : (3.8e6 : ℝ) ≤ E 4 u := big_le_E (by omega) hu
  have hsplit : derivComb^[m] (DeltaComb 5 7)
      = derivComb^[m] (UCombAux 2 7) + derivComb^[m] (VCombAux 2 7) := by
    rw [show DeltaComb 5 7 = DeltaCombAux 2 7 from rfl,
      DeltaCombAux_eq_UCombAux_add_VCombAux, derivComb_iterate_add]
  have hUSB : CombSizeBound 4 31 78624 (derivComb^[m] (UCombAux 2 7)) := by
    interval_cases m
    · simpa using UCombAux_two_seven_sizeBound.mono (by norm_num) (by norm_num)
    · rw [Function.iterate_one]
      exact UCombAux_two_seven_sizeBound.derivComb_step.mono
        (by norm_num) (by norm_num)
    · rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
        Function.iterate_one]
      exact UCombAux_two_seven_sizeBound.derivComb_step.derivComb_step.mono
        (by norm_num) (by norm_num)
  have hVSB : CombSizeBound 5 39 356400 (derivComb^[m] (VCombAux 2 7)) := by
    interval_cases m
    · simpa using VCombAux_two_seven_sizeBound.mono (by norm_num) (by norm_num)
    · rw [Function.iterate_one]
      exact VCombAux_two_seven_sizeBound.derivComb_step.mono
        (by norm_num) (by norm_num)
    · rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
        Function.iterate_one]
      exact VCombAux_two_seven_sizeBound.derivComb_step.derivComb_step.mono
        (by norm_num) (by norm_num)
  have hUneg : ∀ ν ∈ (derivComb^[m] (UCombAux 2 7)).support, ν 4 ≤ -1 :=
    derivComb_iterate_apply_le_neg_one UCombAux_two_seven_sizeBound.maxIdx_le
      UCombAux_two_seven_neg m
  have hVneg : ∀ ν ∈ (derivComb^[m] (VCombAux 2 7)).support, ν 5 ≤ -1 :=
    derivComb_iterate_apply_le_neg_one VCombAux_two_seven_sizeBound.maxIdx_le
      VCombAux_two_seven_neg m
  have hU : |evalComb (derivComb^[m] (UCombAux 2 7)) u|
      ≤ Real.exp (-(E 3 u) / 2) / 2 := by
    refine (abs_evalComb_le_of_sizeBound hUSB hUneg hu).trans ?_
    rw [show (4 : ℕ) - 1 = 3 from rfl]
    exact poly_div_E_succ_le_exp_neg_half (by omega) hu (by norm_num)
      (by push_cast; nlinarith)
  have hV : |evalComb (derivComb^[m] (VCombAux 2 7)) u|
      ≤ Real.exp (-(E 3 u) / 2) / 2 := by
    refine (abs_evalComb_le_of_sizeBound hVSB hVneg hu).trans ?_
    rw [show (5 : ℕ) - 1 = 4 from rfl]
    refine (poly_div_E_succ_le_exp_neg_half (by omega) hu (by norm_num)
      (by push_cast; nlinarith)).trans ?_
    have hEE : E 3 u ≤ E 4 u := E_mono_depth hu (by omega)
    have h := Real.exp_le_exp.mpr (by linarith : -(E 4 u) / 2 ≤ -(E 3 u) / 2)
    linarith
  rw [hsplit, evalComb_add]
  calc |evalComb (derivComb^[m] (UCombAux 2 7)) u
        + evalComb (derivComb^[m] (VCombAux 2 7)) u|
      ≤ |evalComb (derivComb^[m] (UCombAux 2 7)) u|
        + |evalComb (derivComb^[m] (VCombAux 2 7)) u| := abs_add_le _ _
    _ ≤ Real.exp (-(E 3 u) / 2) / 2 + Real.exp (-(E 3 u) / 2) / 2 :=
        add_le_add hU hV
    _ = Real.exp (-(E 3 u) / 2) := by ring

/-- The increment `Δ₄,₇` and its first two derivatives are below a quarter
of the eq. `R7-tail` target (`Δ₄,₇ = 𝓛₄ Δ₅,₇`; paper table rows `U₄,₇`,
`V₄,₇` of tab. `derivative-bounds`, with the generic constants). -/
theorem abs_evalComb_derivIter_DeltaComb_four_seven_le {m : ℕ} (hm : m ≤ 2)
    {u : ℝ} (hu : 1 ≤ u) :
    |evalComb (derivComb^[m] (DeltaComb 4 7)) u|
      ≤ Real.exp (-(3.7e6 : ℝ)) / 4 := by
  have hT3 : (3.8e6 : ℝ) ≤ E 3 u := big_le_E (by omega) hu
  have hT4 : (3.8e6 : ℝ) ≤ E 4 u := big_le_E (by omega) hu
  have hsplit : derivComb^[m] (DeltaComb 4 7)
      = derivComb^[m] (UCombAux 3 7) + derivComb^[m] (VCombAux 3 7) := by
    rw [show DeltaComb 4 7 = DeltaCombAux 3 7 from rfl,
      DeltaCombAux_eq_UCombAux_add_VCombAux, derivComb_iterate_add]
  have hUSB : CombSizeBound 4 40 3175200 (derivComb^[m] (UCombAux 3 7)) := by
    interval_cases m
    · simpa using UCombAux_three_seven_sizeBound.mono (by norm_num) (by norm_num)
    · rw [Function.iterate_one]
      exact UCombAux_three_seven_sizeBound.derivComb_step.mono
        (by norm_num) (by norm_num)
    · rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
        Function.iterate_one]
      exact UCombAux_three_seven_sizeBound.derivComb_step.derivComb_step.mono
        (by norm_num) (by norm_num)
  have hVSB : CombSizeBound 5 50 18057600 (derivComb^[m] (VCombAux 3 7)) := by
    interval_cases m
    · simpa using VCombAux_three_seven_sizeBound.mono (by norm_num) (by norm_num)
    · rw [Function.iterate_one]
      exact VCombAux_three_seven_sizeBound.derivComb_step.mono
        (by norm_num) (by norm_num)
    · rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
        Function.iterate_one]
      exact VCombAux_three_seven_sizeBound.derivComb_step.derivComb_step.mono
        (by norm_num) (by norm_num)
  have hUneg : ∀ ν ∈ (derivComb^[m] (UCombAux 3 7)).support, ν 4 ≤ -1 :=
    derivComb_iterate_apply_le_neg_one UCombAux_three_seven_sizeBound.maxIdx_le
      UCombAux_three_seven_neg m
  have hVneg : ∀ ν ∈ (derivComb^[m] (VCombAux 3 7)).support, ν 5 ≤ -1 :=
    derivComb_iterate_apply_le_neg_one VCombAux_three_seven_sizeBound.maxIdx_le
      VCombAux_three_seven_neg m
  have hU : |evalComb (derivComb^[m] (UCombAux 3 7)) u|
      ≤ Real.exp (-(3.7e6 : ℝ)) / 8 := by
    refine (abs_evalComb_le_of_sizeBound hUSB hUneg hu).trans ?_
    have hE4 : E 4 u = Real.exp (E 3 u) := E_succ 3 u
    rw [show (4 : ℕ) - 1 = 3 from rfl, hE4]
    exact poly_div_exp_le_target hT3 (by norm_num) (by push_cast; nlinarith)
  have hV : |evalComb (derivComb^[m] (VCombAux 3 7)) u|
      ≤ Real.exp (-(3.7e6 : ℝ)) / 8 := by
    refine (abs_evalComb_le_of_sizeBound hVSB hVneg hu).trans ?_
    have hE5 : E 5 u = Real.exp (E 4 u) := E_succ 4 u
    rw [show (5 : ℕ) - 1 = 4 from rfl, hE5]
    exact poly_div_exp_le_target hT4 (by norm_num) (by push_cast; nlinarith)
  rw [hsplit, evalComb_add]
  calc |evalComb (derivComb^[m] (UCombAux 3 7)) u
        + evalComb (derivComb^[m] (VCombAux 3 7)) u|
      ≤ |evalComb (derivComb^[m] (UCombAux 3 7)) u|
        + |evalComb (derivComb^[m] (VCombAux 3 7)) u| := abs_add_le _ _
    _ ≤ Real.exp (-(3.7e6 : ℝ)) / 8 + Real.exp (-(3.7e6 : ℝ)) / 8 :=
        add_le_add hU hV
    _ = Real.exp (-(3.7e6 : ℝ)) / 4 := by ring

/-! ## Derivatives of the limit: the `m`-differentiated increment calculus

The paper's `C²[1, e]`-convergence claim: the exact increment identity, the
summability, and the quantitative tail of
`Erdos320.Lemmas.BackwardReferenceConvergence`, redone for the formally
differentiated increments (`m ≤ 2` throughout, matching the paper's
`0 ≤ k ≤ 2` in eq. `reference-increment`). -/

/-- The `m`-differentiated exact increment identity (eq. `reference-defect`
after `∂_u^m`): `∂^m Δ_{s,R} = ∂^m Q_s^{[R+1]} − ∂^m Q_s^{[R]}`, at the
level of evaluated combs, for `4 ≤ s ≤ R` and positive phase. -/
theorem evalComb_derivIter_DeltaComb_eq {s R : ℕ} (hs : 4 ≤ s) (hsR : s ≤ R)
    (m : ℕ) :
    ∀ {u : ℝ}, 0 < u →
      evalComb (derivComb^[m] (DeltaComb s R)) u
        = evalComb (derivComb^[m] (QrefComb s (R + 1))) u
          - evalComb (derivComb^[m] (QrefComb s R)) u := by
  induction m with
  | zero =>
      intro u hu
      simp only [Function.iterate_zero_apply]
      rw [← Qref_eq_evalComb hu, ← Qref_eq_evalComb hu]
      exact (Qref_succ_sub_eval hs hsR hu).symm
  | succ m ih =>
      intro u hu
      have hev : evalComb (derivComb^[m] (DeltaComb s R)) =ᶠ[nhds u]
          fun v => evalComb (derivComb^[m] (QrefComb s (R + 1))) v
            - evalComb (derivComb^[m] (QrefComb s R)) v := by
        filter_upwards [Ioi_mem_nhds hu] with v hv
        exact ih hv
      have hΔ : HasDerivAt (evalComb (derivComb^[m] (DeltaComb s R)))
          (evalComb (derivComb^[m + 1] (QrefComb s (R + 1))) u
            - evalComb (derivComb^[m + 1] (QrefComb s R)) u) u :=
        ((hasDerivAt_evalComb_iterate hu (QrefComb s (R + 1)) m).sub
          (hasDerivAt_evalComb_iterate hu (QrefComb s R) m)).congr_of_eventuallyEq
          hev
      exact (hasDerivAt_evalComb_iterate hu (DeltaComb s R) m).unique hΔ

/-- Telescoping the `m`-differentiated increments (the `∂^m`-image of
`Qref_eq_add_sum_DeltaComb`). -/
theorem sum_evalComb_derivIter_DeltaComb {s : ℕ} (hs : 4 ≤ s) (m n : ℕ)
    {u : ℝ} (hu : 0 < u) :
    ∑ k ∈ Finset.range n, evalComb (derivComb^[m] (DeltaComb s (s + 1 + k))) u
      = evalComb (derivComb^[m] (QrefComb s (s + 1 + n))) u
        - evalComb (derivComb^[m] (QrefComb s (s + 1))) u := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih,
        evalComb_derivIter_DeltaComb_eq hs (by omega) m hu,
        show s + 1 + n + 1 = s + 1 + (n + 1) by omega]
      ring

/-- Summability of the `m`-differentiated increment series (`m ≤ 2`,
`u ≥ 1`; comparison with a geometric series via
eq. `reference-increment`). -/
theorem summable_evalComb_derivIter_DeltaComb {s : ℕ} (hs : 4 ≤ s) {m : ℕ}
    (hm : m ≤ 2) {u : ℝ} (hu : 1 ≤ u) :
    Summable fun k : ℕ =>
      evalComb (derivComb^[m] (DeltaComb s (s + 1 + k))) u := by
  rw [← summable_nat_add_iff 7]
  refine Summable.of_abs ?_
  have hg : Summable fun k : ℕ =>
      2 * Real.exp (-(E (s + 4) u) / 2) * (1 / 2 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hg
  have hb := abs_evalComb_derivIter_DeltaComb_le (s := s)
    (R := s + 1 + (k + 7)) (by omega) hs (by omega) hm hu
  have hidx : s + 1 + (k + 7) - 4 = (s + 4) + k := by omega
  rw [hidx] at hb
  refine hb.trans ?_
  have hdecay := exp_neg_E_add_le hu (j := s + 4) (by omega) k
  linarith

/-- The tail of the `m`-differentiated increment series is dominated by
twice its first term (`m`-version of `abs_tsum_DeltaComb_tail_le`). -/
theorem abs_tsum_derivIter_DeltaComb_tail_le {s n : ℕ} (hs : 4 ≤ s)
    (hR : 8 ≤ s + 1 + n) {m : ℕ} (hm : m ≤ 2) {u : ℝ} (hu : 1 ≤ u) :
    |∑' k : ℕ, evalComb (derivComb^[m] (DeltaComb s (s + 1 + (k + n)))) u|
      ≤ 4 * Real.exp (-(E (s + 1 + n - 4) u) / 2) := by
  have hsum := summable_evalComb_derivIter_DeltaComb hs hm hu
  have hshift : Summable fun k : ℕ =>
      evalComb (derivComb^[m] (DeltaComb s (s + 1 + (k + n)))) u :=
    (summable_nat_add_iff (f := fun k : ℕ =>
      evalComb (derivComb^[m] (DeltaComb s (s + 1 + k))) u) n).mpr hsum
  have habs : Summable fun k : ℕ =>
      |evalComb (derivComb^[m] (DeltaComb s (s + 1 + (k + n)))) u| := hshift.abs
  have hterm : ∀ k : ℕ,
      |evalComb (derivComb^[m] (DeltaComb s (s + 1 + (k + n)))) u|
      ≤ 2 * Real.exp (-(E (s + 1 + n - 4) u) / 2) * (1 / 2 : ℝ) ^ k := by
    intro k
    have hb := abs_evalComb_derivIter_DeltaComb_le (s := s)
      (R := s + 1 + (k + n)) (by omega) hs (by omega) hm hu
    have hidx : s + 1 + (k + n) - 4 = (s + 1 + n - 4) + k := by omega
    rw [hidx] at hb
    have hdecay := exp_neg_E_add_le hu (j := s + 1 + n - 4) (by omega) k
    linarith [hb, hdecay]
  have hgsum : Summable fun k : ℕ =>
      2 * Real.exp (-(E (s + 1 + n - 4) u) / 2) * (1 / 2 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hnorm : ‖∑' k : ℕ,
        evalComb (derivComb^[m] (DeltaComb s (s + 1 + (k + n)))) u‖
      ≤ ∑' k : ℕ,
        ‖evalComb (derivComb^[m] (DeltaComb s (s + 1 + (k + n)))) u‖ :=
    norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs] using habs)
  simp only [Real.norm_eq_abs] at hnorm
  calc |∑' k : ℕ, evalComb (derivComb^[m] (DeltaComb s (s + 1 + (k + n)))) u|
      ≤ ∑' k : ℕ,
        |evalComb (derivComb^[m] (DeltaComb s (s + 1 + (k + n)))) u| := hnorm
    _ ≤ ∑' k : ℕ, 2 * Real.exp (-(E (s + 1 + n - 4) u) / 2) * (1 / 2 : ℝ) ^ k :=
        habs.tsum_le_tsum hterm hgsum
    _ = 2 * Real.exp (-(E (s + 1 + n - 4) u) / 2) * ∑' k : ℕ, (1 / 2 : ℝ) ^ k :=
        tsum_mul_left
    _ = 4 * Real.exp (-(E (s + 1 + n - 4) u) / 2) := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
        ring

/-- `QrefLimitIterDeriv m s`: the `m`-th derivative of the limiting backward
reference function `Q_s^*` of `lem:backward-reference-convergence`, realized
as the explicit convergent series `∂^m Q_s^{[s+1]} + ∑_R ∂^m Δ_{s,R}`.  For
`m = 0` it agrees with `QrefLimit s` on positive phase
(`QrefLimit_eq_iterDeriv_zero`); that it is genuinely the `m`-th derivative
on `1 < u` is `hasDerivAt_QrefLimit` / `hasDerivAt_QrefLimitIterDeriv`. -/
noncomputable def QrefLimitIterDeriv (m s : ℕ) : ℝ → ℝ := fun u =>
  evalComb (derivComb^[m] (QrefComb s (s + 1))) u
    + ∑' k : ℕ, evalComb (derivComb^[m] (DeltaComb s (s + 1 + k))) u

/-- On positive phase, `QrefLimitIterDeriv 0 s` is `QrefLimit s = Q_s^*`. -/
theorem QrefLimit_eq_iterDeriv_zero (s : ℕ) {u : ℝ} (hu : 0 < u) :
    QrefLimit s u = QrefLimitIterDeriv 0 s u := by
  unfold QrefLimit QrefLimitIterDeriv
  simp only [Function.iterate_zero_apply]
  rw [Qref_eq_evalComb hu]

/-- Pointwise `C²`-convergence of the finite reference functions: for
`s ≥ 4`, `m ≤ 2`, `u ≥ 1`, `∂^m Q_s^{[R]}(u) → ∂^m Q_s^*(u)` as `R → ∞`
("the series of increments … converges locally uniformly together with its
first two derivatives"). -/
theorem tendsto_evalComb_derivIter_QrefComb {s : ℕ} (hs : 4 ≤ s) {m : ℕ}
    (hm : m ≤ 2) {u : ℝ} (hu : 1 ≤ u) :
    Filter.Tendsto (fun R : ℕ => evalComb (derivComb^[m] (QrefComb s R)) u)
      Filter.atTop (nhds (QrefLimitIterDeriv m s u)) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hsum := summable_evalComb_derivIter_DeltaComb hs hm hu
  have hcomp := hsum.hasSum.tendsto_sum_nat.comp
    (Filter.tendsto_sub_atTop_nat (s + 1))
  have hadd := hcomp.const_add
    (evalComb (derivComb^[m] (QrefComb s (s + 1))) u)
  refine Filter.Tendsto.congr' ?_ hadd
  filter_upwards [Filter.eventually_ge_atTop (s + 1)] with R hR
  have h := sum_evalComb_derivIter_DeltaComb hs m (R - (s + 1)) hu0
  rw [show s + 1 + (R - (s + 1)) = R by omega] at h
  simp only [Function.comp_apply]
  linarith

/-- **Quantitative `C²` tail** (`m`-version of `abs_QrefLimit_sub_Qref`):
for `s ≥ 4`, `R ≥ max 8 (s+1)`, `m ≤ 2`, `u ≥ 1`,
`|∂^m Q_s^*(u) − ∂^m Q_s^{[R]}(u)| ≤ 4 exp(−E_{R−4}(u)/2)`. -/
theorem abs_QrefLimitIterDeriv_sub_evalComb_le {s R : ℕ} (hs : 4 ≤ s)
    (hR : 8 ≤ R) (hsR : s + 1 ≤ R) {m : ℕ} (hm : m ≤ 2) {u : ℝ}
    (hu : 1 ≤ u) :
    |QrefLimitIterDeriv m s u - evalComb (derivComb^[m] (QrefComb s R)) u|
      ≤ 4 * Real.exp (-(E (R - 4) u) / 2) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  obtain ⟨n, rfl⟩ : ∃ n, R = s + 1 + n := ⟨R - (s + 1), by omega⟩
  have hsum := summable_evalComb_derivIter_DeltaComb hs hm hu
  have hQ := sum_evalComb_derivIter_DeltaComb hs m n hu0
  have hsplit : (∑ k ∈ Finset.range n,
        evalComb (derivComb^[m] (DeltaComb s (s + 1 + k))) u)
      + ∑' k : ℕ, evalComb (derivComb^[m] (DeltaComb s (s + 1 + (k + n)))) u
      = ∑' k : ℕ, evalComb (derivComb^[m] (DeltaComb s (s + 1 + k))) u :=
    Summable.sum_add_tsum_nat_add (f := fun k : ℕ =>
      evalComb (derivComb^[m] (DeltaComb s (s + 1 + k))) u) n hsum
  have hdiff : QrefLimitIterDeriv m s u
        - evalComb (derivComb^[m] (QrefComb s (s + 1 + n))) u
      = ∑' k : ℕ,
        evalComb (derivComb^[m] (DeltaComb s (s + 1 + (k + n)))) u := by
    unfold QrefLimitIterDeriv
    linarith [hQ, hsplit]
  rw [hdiff]
  exact abs_tsum_derivIter_DeltaComb_tail_le hs (by omega) hm hu

/-! ## The `A_s`-proximity derivative bound (eq. `reference-derivative-bound`)

`|(Q_s^{[R]} − A_s)'| ≤ 32 A_{s-1} a_{s-1}/E_{s-2}`, uniformly in
`R ≥ s + 1`, `s ≥ 5`, `u ≥ 1` (the paper's uniformity is `u ∈ [1, e]`;
`u ≤ e` is not needed).  The paper's `E_{s-3}'` is `a_{s-1}`. -/

/-- Derivative error of the first exact terminal identity:
`|(Q_s^{[s+1]} − A_s)'| ≤ 2 A_{s-1} a_{s-1}/E_{s-2}` for `s ≥ 4`, `u ≥ 1`
(the paper's "derivative errors at most `2 b_s v_s`", with
`v_s = x_{s-3}' = a_{s-1}`). -/
theorem abs_deriv_Qref_succ_sub_A_le {s : ℕ} (hs : 4 ≤ s) {u : ℝ}
    (hu : 1 ≤ u) :
    |deriv (fun v => Qref s (s + 1) v - A s v) u|
      ≤ 2 * A (s - 1) u * a (s - 1) u / E (s - 2) u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hXpos : (0 : ℝ) < E (s - 2) u := E_pos_of_one_le (by omega) u
  have hfun : (fun v => Qref s (s + 1) v - A s v)
      = fun v => A (s - 1) v / E (s - 2) v := by
    funext v
    rw [Qref_succ_eq hs v]
    ring
  have hD : HasDerivAt (fun v => A (s - 1) v / E (s - 2) v)
      ((a (s - 1) u * Bref (s - 1) u * E (s - 2) u - A (s - 1) u * a s u)
        / E (s - 2) u ^ 2) u :=
    (hasDerivAt_A_Bref (s - 1) u).div (hasDerivAt_E_sub_two s u) hXpos.ne'
  rw [hfun, hD.deriv]
  have has : a s u = a (s - 1) u * E (s - 2) u := by
    have h := a_succ (r := s - 1) (by omega) u
    rw [show s - 1 + 1 = s by omega, show s - 1 - 1 = s - 2 by omega] at h
    exact h
  have hval : (a (s - 1) u * Bref (s - 1) u * E (s - 2) u
        - A (s - 1) u * a s u) / E (s - 2) u ^ 2
      = a (s - 1) u * (Bref (s - 1) u - A (s - 1) u) / E (s - 2) u := by
    rw [has]
    field_simp
  rw [hval, abs_div, abs_of_pos hXpos]
  refine div_le_div_of_nonneg_right ?_ hXpos.le
  have hB0 : 0 ≤ Bref (s - 1) u := Bref_nonneg hu0 _
  have hBA : Bref (s - 1) u ≤ A (s - 1) u := by
    have h := Bref_le_A_pred (j := s - 1) (by omega) hu
    rw [show s - 1 - 1 = s - 2 by omega] at h
    exact le_trans h (A_mono_index hu0 (by omega))
  have habs : |Bref (s - 1) u - A (s - 1) u| ≤ A (s - 1) u := by
    rw [abs_le]
    exact ⟨by linarith, by linarith [A_pos hu0 (s - 1)]⟩
  rw [abs_mul, abs_of_pos (a_pos _ u)]
  calc a (s - 1) u * |Bref (s - 1) u - A (s - 1) u|
      ≤ a (s - 1) u * A (s - 1) u :=
        mul_le_mul_of_nonneg_left habs (a_pos _ u).le
    _ ≤ 2 * A (s - 1) u * a (s - 1) u := by
        nlinarith [A_pos hu0 (s - 1), a_pos (s - 1) u]

/-- Derivative error of the second exact terminal identity:
`|(Q_s^{[s+2]} − A_s)'| ≤ 8 A_{s-1} a_{s-1}/E_{s-2}` for `s ≥ 5`, `u ≥ 1`
(the paper's `6 b_s v_s`, with slack). -/
theorem abs_deriv_Qref_succ_succ_sub_A_le {s : ℕ} (hs : 5 ≤ s) {u : ℝ}
    (hu : 1 ≤ u) :
    |deriv (fun v => Qref s (s + 2) v - A s v) u|
      ≤ 8 * A (s - 1) u * a (s - 1) u / E (s - 2) u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hXpos : (0 : ℝ) < E (s - 2) u := E_pos_of_one_le (by omega) u
  have hYpos : (0 : ℝ) < E (s - 1) u := E_pos_of_one_le (by omega) u
  have hApos : (0 : ℝ) < A (s - 1) u := A_pos hu0 _
  have hapos : (0 : ℝ) < a (s - 1) u := a_pos _ u
  have hfun : (fun v => Qref s (s + 2) v - A s v)
      = fun v => Bref s v - (A s v - Bref s v) / E (s - 1) v := by
    funext v
    rw [Qref_succ_succ_eq (by omega) v]
    ring
  have hBd : HasDerivAt (Bref s) (deriv (Bref s) u) u :=
    (hasDerivAt_Bref s hu0).differentiableAt.hasDerivAt
  have hE : HasDerivAt (E (s - 1)) (a (s + 1) u) u := by
    have h := hasDerivAt_E_sub_two (s + 1) u
    rw [show s + 1 - 2 = s - 1 by omega] at h
    exact h
  have hD : HasDerivAt (fun v => Bref s v - (A s v - Bref s v) / E (s - 1) v)
      (deriv (Bref s) u
        - ((a s u * Bref s u - deriv (Bref s) u) * E (s - 1) u
            - (A s u - Bref s u) * a (s + 1) u) / E (s - 1) u ^ 2) u :=
    hBd.sub (((hasDerivAt_A_Bref s u).sub hBd).div hE hYpos.ne')
  rw [hfun, hD.deriv]
  have haY : a (s + 1) u = a s u * E (s - 1) u := a_succ (by omega) u
  have hval : deriv (Bref s) u
        - ((a s u * Bref s u - deriv (Bref s) u) * E (s - 1) u
            - (A s u - Bref s u) * a (s + 1) u) / E (s - 1) u ^ 2
      = deriv (Bref s) u
        - (a s u * Bref s u - deriv (Bref s) u) / E (s - 1) u
        + (A s u - Bref s u) * a s u / E (s - 1) u := by
    rw [haY]
    field_simp
    ring
  rw [hval]
  -- notation and elementary facts
  have has : a s u = a (s - 1) u * E (s - 2) u := by
    have h := a_succ (r := s - 1) (by omega) u
    rw [show s - 1 + 1 = s by omega, show s - 1 - 1 = s - 2 by omega] at h
    exact h
  have hB0 : 0 ≤ Bref s u := Bref_nonneg hu0 s
  have hBA' : Bref s u ≤ A (s - 1) u := Bref_le_A_pred (by omega) hu
  have hBAs : Bref s u ≤ A s u :=
    le_trans hBA' (A_mono_index hu0 (by omega))
  have hY2 : (2 : ℝ) ≤ E (s - 1) u := two_le_E (by omega) hu
  have hX2Y : E (s - 2) u ^ 2 ≤ E (s - 1) u := by
    have h20 : (20 : ℝ) ≤ E (s - 2) u := twenty_le_E (by omega) hu
    have h1 : E (s - 2) u ^ 2 ≤ Real.exp (E (s - 2) u / 2) := sq_le_exp_half h20
    have h2 : E (s - 1) u = Real.exp (E (s - 2) u) := by
      rw [show s - 1 = (s - 2) + 1 by omega, E_succ]
    rw [h2]
    exact h1.trans (Real.exp_le_exp.mpr (by linarith))
  -- piece 1: |B_s'| ≤ 4 b_s v_s
  have hdB : |deriv (Bref s) u| ≤ 4 * A (s - 1) u * a (s - 1) u / E (s - 2) u :=
    abs_deriv_Bref_le (by omega) hu
  have hbv0 : (0 : ℝ) < A (s - 1) u * a (s - 1) u / E (s - 2) u :=
    div_pos (mul_pos hApos hapos) hXpos
  -- piece 2: `a_s B_s / Y ≤ b_s v_s`
  have hT2 : a s u * Bref s u / E (s - 1) u
      ≤ A (s - 1) u * a (s - 1) u / E (s - 2) u := by
    rw [div_le_div_iff₀ hYpos hXpos, has]
    have e1 : a (s - 1) u * Bref s u * E (s - 2) u ^ 2
        ≤ a (s - 1) u * A (s - 1) u * E (s - 2) u ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBA' hapos.le) (by positivity)
    have e2 : a (s - 1) u * A (s - 1) u * E (s - 2) u ^ 2
        ≤ a (s - 1) u * A (s - 1) u * E (s - 1) u :=
      mul_le_mul_of_nonneg_left hX2Y (by positivity)
    nlinarith [e1, e2]
  -- piece 3: `(A_s − B_s) a_s / Y ≤ b_s v_s` from `(x + 2) X² ≤ Y`
  have hT4 : (A s u - Bref s u) * a s u / E (s - 1) u
      ≤ A (s - 1) u * a (s - 1) u / E (s - 2) u := by
    have hx15 : (15 : ℝ) ≤ E (s - 3) u := fifteen_le_E (by omega) hu
    have hX : E (s - 2) u = Real.exp (E (s - 3) u) := by
      rw [show s - 2 = (s - 3) + 1 by omega, E_succ]
    have hY : E (s - 1) u = Real.exp (E (s - 2) u) := by
      rw [show s - 1 = (s - 2) + 1 by omega, E_succ]
    have hkey2 : (E (s - 3) u + 2) * E (s - 2) u ^ 2 ≤ E (s - 1) u := by
      rw [hY, hX]
      exact add_two_mul_exp_sq_le_exp_exp hx15
    have hAle : A s u ≤ (1 + E (s - 3) u) * A (s - 1) u :=
      A_le_one_add_E_mul (by omega) hu0
    rw [div_le_div_iff₀ hYpos hXpos]
    have hprod : (0 : ℝ) ≤ A (s - 1) u * a (s - 1) u * E (s - 2) u ^ 2 := by
      positivity
    calc (A s u - Bref s u) * a s u * E (s - 2) u
        ≤ A s u * a s u * E (s - 2) u := by
          have h := mul_le_mul_of_nonneg_right
            (show A s u - Bref s u ≤ A s u by linarith)
            (mul_nonneg (a_pos s u).le hXpos.le)
          nlinarith [h]
      _ = A s u * a (s - 1) u * E (s - 2) u ^ 2 := by rw [has]; ring
      _ ≤ (1 + E (s - 3) u) * A (s - 1) u * a (s - 1) u * E (s - 2) u ^ 2 := by
          have h := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hAle hapos.le)
            (by positivity : (0 : ℝ) ≤ E (s - 2) u ^ 2)
          nlinarith [h]
      _ ≤ A (s - 1) u * a (s - 1) u * ((E (s - 3) u + 2) * E (s - 2) u ^ 2) := by
          nlinarith [hprod]
      _ ≤ A (s - 1) u * a (s - 1) u * E (s - 1) u :=
          mul_le_mul_of_nonneg_left hkey2 (by positivity)
  -- piece 4: `|a_s B_s − B_s'| / Y ≤ 3 b_s v_s`
  have hW : |(a s u * Bref s u - deriv (Bref s) u) / E (s - 1) u|
      ≤ 3 * (A (s - 1) u * a (s - 1) u / E (s - 2) u) := by
    rw [abs_div, abs_of_pos hYpos]
    have hnum : |a s u * Bref s u - deriv (Bref s) u|
        ≤ a s u * Bref s u + |deriv (Bref s) u| := by
      refine le_trans (abs_sub _ _) ?_
      rw [abs_of_nonneg (mul_nonneg (a_pos s u).le hB0)]
    have hdBY : |deriv (Bref s) u| / E (s - 1) u
        ≤ 2 * (A (s - 1) u * a (s - 1) u / E (s - 2) u) := by
      have h1 : |deriv (Bref s) u| / E (s - 1) u ≤ |deriv (Bref s) u| / 2 := by
        exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hY2
      refine h1.trans ?_
      ring_nf at hdB ⊢
      linarith
    have hsplit : (a s u * Bref s u + |deriv (Bref s) u|) / E (s - 1) u
        = a s u * Bref s u / E (s - 1) u
          + |deriv (Bref s) u| / E (s - 1) u := add_div _ _ _
    calc |a s u * Bref s u - deriv (Bref s) u| / E (s - 1) u
        ≤ (a s u * Bref s u + |deriv (Bref s) u|) / E (s - 1) u :=
          div_le_div_of_nonneg_right hnum hYpos.le
      _ = a s u * Bref s u / E (s - 1) u
          + |deriv (Bref s) u| / E (s - 1) u := hsplit
      _ ≤ 3 * (A (s - 1) u * a (s - 1) u / E (s - 2) u) := by
          ring_nf at hT2 hdBY ⊢
          linarith
  -- combine
  have hV0 : 0 ≤ (A s u - Bref s u) * a s u / E (s - 1) u :=
    div_nonneg (mul_nonneg (by linarith) (a_pos s u).le) hYpos.le
  have hfinal : 8 * A (s - 1) u * a (s - 1) u / E (s - 2) u
      = 8 * (A (s - 1) u * a (s - 1) u / E (s - 2) u) := by ring
  rw [hfinal]
  calc |deriv (Bref s) u
        - (a s u * Bref s u - deriv (Bref s) u) / E (s - 1) u
        + (A s u - Bref s u) * a s u / E (s - 1) u|
      ≤ |deriv (Bref s) u
          - (a s u * Bref s u - deriv (Bref s) u) / E (s - 1) u|
        + |(A s u - Bref s u) * a s u / E (s - 1) u| := abs_add_le _ _
    _ ≤ |deriv (Bref s) u|
        + |(a s u * Bref s u - deriv (Bref s) u) / E (s - 1) u|
        + |(A s u - Bref s u) * a s u / E (s - 1) u| := by
        linarith [abs_sub (deriv (Bref s) u)
          ((a s u * Bref s u - deriv (Bref s) u) / E (s - 1) u)]
    _ ≤ 8 * (A (s - 1) u * a (s - 1) u / E (s - 2) u) := by
        rw [abs_of_nonneg hV0]
        ring_nf at hdB hW hT4 ⊢
        linarith

/-- **Eq. `reference-derivative-bound`, derivative half**: uniformly for
`s ≥ 5`, `R ≥ s + 1`, `u ≥ 1`,
`|(Q_s^{[R]} − A_s)'| ≤ 32 A_{s-1} a_{s-1}/E_{s-2}` (the paper's
`E_{s-3}'` is `a_{s-1}`). -/
theorem abs_deriv_Qref_sub_A_le {s R : ℕ} (hs : 5 ≤ s) (hR : s + 1 ≤ R)
    {u : ℝ} (hu : 1 ≤ u) :
    |deriv (fun v => Qref s R v - A s v) u|
      ≤ 32 * A (s - 1) u * a (s - 1) u / E (s - 2) u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hXpos : (0 : ℝ) < E (s - 2) u := E_pos_of_one_le (by omega) u
  have hApos : (0 : ℝ) < A (s - 1) u := A_pos hu0 _
  have hapos : (0 : ℝ) < a (s - 1) u := a_pos _ u
  have hAa1 : (1 : ℝ) ≤ A (s - 1) u * a (s - 1) u := by
    have h1 := one_le_A hu0 (s - 1)
    have h2 := one_le_a hu (s - 1)
    nlinarith
  have hinv : 1 / E (s - 2) u ≤ A (s - 1) u * a (s - 1) u / E (s - 2) u :=
    div_le_div_of_nonneg_right hAa1 hXpos.le
  have hbv0 : (0 : ℝ) < A (s - 1) u * a (s - 1) u / E (s - 2) u :=
    div_pos (mul_pos hApos hapos) hXpos
  have h32 : 32 * A (s - 1) u * a (s - 1) u / E (s - 2) u
      = 32 * (A (s - 1) u * a (s - 1) u / E (s - 2) u) := by ring
  rcases eq_or_lt_of_le hR with hR1 | hR2
  · -- R = s + 1
    rw [← hR1, h32]
    have h := abs_deriv_Qref_succ_sub_A_le (s := s) (by omega) hu
    ring_nf at h hbv0 ⊢
    linarith
  · rcases eq_or_lt_of_le (show s + 2 ≤ R by omega) with hR2' | hR3
    · -- R = s + 2
      rw [← hR2', h32]
      have h := abs_deriv_Qref_succ_succ_sub_A_le hs hu
      ring_nf at h hbv0 ⊢
      linarith
    · -- R ≥ s + 3 (hence R ≥ 8): route through the C¹-limit
      have hQd : HasDerivAt (fun v => Qref s R v - A s v)
          (evalComb (derivComb (QrefComb s R)) u - a s u * Bref s u) u :=
        (hasDerivAt_Qref hu0).sub (hasDerivAt_A_Bref s u)
      have hQd2 : HasDerivAt (fun v => Qref s (s + 2) v - A s v)
          (evalComb (derivComb (QrefComb s (s + 2))) u - a s u * Bref s u) u :=
        (hasDerivAt_Qref hu0).sub (hasDerivAt_A_Bref s u)
      have h2 : |evalComb (derivComb (QrefComb s (s + 2))) u
            - a s u * Bref s u|
          ≤ 8 * (A (s - 1) u * a (s - 1) u / E (s - 2) u) := by
        have h := abs_deriv_Qref_succ_succ_sub_A_le hs hu
        rw [hQd2.deriv] at h
        ring_nf at h ⊢
        linarith
      -- the C¹ tail at `R` and at `s + 2`
      have htailR : |QrefLimitIterDeriv 1 s u
            - evalComb (derivComb (QrefComb s R)) u|
          ≤ 1 / E (s - 2) u := by
        have h := abs_QrefLimitIterDeriv_sub_evalComb_le (s := s) (R := R)
          (by omega) (by omega) (by omega) (m := 1) (by omega) hu
        rw [Function.iterate_one] at h
        refine h.trans ?_
        refine le_trans ?_ (four_mul_exp_neg_E_half_le_inv (by omega) hu)
        have hmono : E (s - 2) u ≤ E (R - 4) u := E_mono_depth hu (by omega)
        have hh := Real.exp_le_exp.mpr
          (show -(E (R - 4) u) / 2 ≤ -(E (s - 2) u) / 2 by linarith)
        linarith
      have htail2 : |QrefLimitIterDeriv 1 s u
            - evalComb (derivComb (QrefComb s (s + 2))) u|
          ≤ 2 / E (s - 2) u := by
        rcases eq_or_lt_of_le hs with hs5 | hs6
        · -- s = 5: through `R = 8` and the exceptional `Δ_{5,7}`
          subst hs5
          rw [show (5 : ℕ) + 2 = 7 from rfl, show (5 : ℕ) - 2 = 3 from rfl]
          have hA : |QrefLimitIterDeriv 1 5 u
                - evalComb (derivComb (QrefComb 5 8)) u| ≤ 1 / E 3 u := by
            have h := abs_QrefLimitIterDeriv_sub_evalComb_le (s := 5) (R := 8)
              (by omega) (by omega) (by omega) (m := 1) (by omega) hu
            rw [Function.iterate_one, show (8 : ℕ) - 4 = 4 from rfl] at h
            refine h.trans ?_
            refine le_trans ?_ (four_mul_exp_neg_E_half_le_inv
              (j := 3) (by omega) hu)
            have hmono : E 3 u ≤ E 4 u := E_mono_depth hu (by omega)
            have hh := Real.exp_le_exp.mpr
              (show -(E 4 u) / 2 ≤ -(E 3 u) / 2 by linarith)
            linarith
          have hB : evalComb (derivComb (QrefComb 5 8)) u
              - evalComb (derivComb (QrefComb 5 7)) u
              = evalComb (derivComb (DeltaComb 5 7)) u := by
            have h := evalComb_derivIter_DeltaComb_eq (s := 5) (R := 7)
              (by omega) (by omega) 1 hu0
            rw [Function.iterate_one] at h
            rw [h]
          have hC : |evalComb (derivComb (DeltaComb 5 7)) u| ≤ 1 / E 3 u := by
            have h := abs_evalComb_derivIter_DeltaComb_five_seven_le
              (m := 1) (by omega) hu
            rw [Function.iterate_one] at h
            refine h.trans ?_
            have hh := four_mul_exp_neg_E_half_le_inv (j := 3) (by omega) hu
            have hp := Real.exp_pos (-(E 3 u) / 2)
            linarith
          have hkey : QrefLimitIterDeriv 1 5 u
                - evalComb (derivComb (QrefComb 5 7)) u
              = (QrefLimitIterDeriv 1 5 u
                  - evalComb (derivComb (QrefComb 5 8)) u)
                + evalComb (derivComb (DeltaComb 5 7)) u := by
            rw [← hB]
            ring
          rw [hkey]
          calc |(QrefLimitIterDeriv 1 5 u
                - evalComb (derivComb (QrefComb 5 8)) u)
              + evalComb (derivComb (DeltaComb 5 7)) u|
              ≤ |QrefLimitIterDeriv 1 5 u
                  - evalComb (derivComb (QrefComb 5 8)) u|
                + |evalComb (derivComb (DeltaComb 5 7)) u| := abs_add_le _ _
            _ ≤ 2 / E 3 u := by
                rw [show (2 : ℝ) / E 3 u = 1 / E 3 u + 1 / E 3 u from by ring]
                exact add_le_add hA hC
        · -- s ≥ 6
          have h := abs_QrefLimitIterDeriv_sub_evalComb_le (s := s)
            (R := s + 2) (by omega) (by omega) (by omega) (m := 1)
            (by omega) hu
          rw [Function.iterate_one, show s + 2 - 4 = s - 2 by omega] at h
          refine h.trans ?_
          have hh := four_mul_exp_neg_E_half_le_inv (j := s - 2) (by omega) hu
          have hp : (0 : ℝ) < 1 / E (s - 2) u := by positivity
          ring_nf at hh hp ⊢
          linarith
      -- combine
      rw [hQd.deriv]
      have hkey : evalComb (derivComb (QrefComb s R)) u - a s u * Bref s u
          = (evalComb (derivComb (QrefComb s (s + 2))) u - a s u * Bref s u)
            + (QrefLimitIterDeriv 1 s u
                - evalComb (derivComb (QrefComb s (s + 2))) u)
            - (QrefLimitIterDeriv 1 s u
                - evalComb (derivComb (QrefComb s R)) u) := by ring
      rw [hkey]
      calc |(evalComb (derivComb (QrefComb s (s + 2))) u - a s u * Bref s u)
            + (QrefLimitIterDeriv 1 s u
                - evalComb (derivComb (QrefComb s (s + 2))) u)
            - (QrefLimitIterDeriv 1 s u
                - evalComb (derivComb (QrefComb s R)) u)|
          ≤ |(evalComb (derivComb (QrefComb s (s + 2))) u - a s u * Bref s u)
              + (QrefLimitIterDeriv 1 s u
                  - evalComb (derivComb (QrefComb s (s + 2))) u)|
            + |QrefLimitIterDeriv 1 s u
                - evalComb (derivComb (QrefComb s R)) u| := abs_sub _ _
        _ ≤ |evalComb (derivComb (QrefComb s (s + 2))) u - a s u * Bref s u|
            + |QrefLimitIterDeriv 1 s u
                - evalComb (derivComb (QrefComb s (s + 2))) u|
            + |QrefLimitIterDeriv 1 s u
                - evalComb (derivComb (QrefComb s R)) u| := by
            linarith [abs_add_le
              (evalComb (derivComb (QrefComb s (s + 2))) u - a s u * Bref s u)
              (QrefLimitIterDeriv 1 s u
                - evalComb (derivComb (QrefComb s (s + 2))) u)]
        _ ≤ 32 * A (s - 1) u * a (s - 1) u / E (s - 2) u := by
            ring_nf at h2 htail2 htailR hinv hbv0 ⊢
            linarith

/-! ## The exact `R = 7` identity (eq. `Q47-exact`) and the reference-core
correction -/

/-- Evaluation of a difference of combinations is the difference of
evaluations. -/
theorem evalComb_sub (P Q : LaurentComb) (u : ℝ) :
    evalComb (P - Q) u = evalComb P u - evalComb Q u := by
  have h : P - Q = P + (-1 : ℤ) • Q := by
    rw [neg_one_smul, sub_eq_add_neg]
  rw [h, evalComb_add, evalComb_smul]
  push_cast
  ring

/-- `QrefCore4Comb`: the reference core `Q̃₄ = 𝓛₄(A₅ + B₅)`
(eq. `reference-core`) as a formal Laurent combination. -/
noncomputable def QrefCore4Comb : LaurentComb :=
  shiftComb (aVec 4) (derivComb (AComb 5 + BrefComb 5))

/-- On positive phase, `Q̃₄` evaluates its comb representation. -/
theorem QrefCore4_eq_evalComb {u : ℝ} (hu : 0 < u) :
    QrefCore4 u = evalComb QrefCore4Comb u := by
  have hev : (fun v => A 5 v + Bref 5 v) =ᶠ[nhds u]
      evalComb (AComb 5 + BrefComb 5) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    rw [evalComb_add, evalComb_AComb, ← Bref_eq_evalComb hv]
  have h1 : QrefCore4 u = deriv (fun v => A 5 v + Bref 5 v) u / a 4 u := rfl
  rw [h1, hev.deriv_eq]
  exact Lop_evalComb 4 (AComb 5 + BrefComb 5) hu

/-- `referenceGapComb`: the exact defect `(A₅ − B₅)/E₄` separating
`Q₅^{[7]}` from `A₅ + B₅` (source of eq. `Q47-exact`). -/
noncomputable def referenceGapComb : LaurentComb :=
  shiftComb (Finsupp.single 4 1) (AComb 5 - BrefComb 5)

/-- `referenceCorrectionComb = 𝓛₄((A₅ − B₅)/E₄)`: the exact correction with
`Q̃₄ = Q₄^{[7]} + 𝓛₄((A₅−B₅)/E₄)` (eq. `Q47-exact` rearranged). -/
noncomputable def referenceCorrectionComb : LaurentComb :=
  shiftComb (aVec 4) (derivComb referenceGapComb)

/-- On positive phase the gap comb evaluates to `(A₅ − B₅)/E₄`. -/
theorem evalComb_referenceGapComb {u : ℝ} (hu : 0 < u) :
    evalComb referenceGapComb u = (A 5 u - Bref 5 u) / E 4 u := by
  unfold referenceGapComb
  rw [evalComb_shiftComb hu, evalComb_sub, evalComb_AComb,
    ← Bref_eq_evalComb hu, evalMon_single, zpow_one]

/-- **The exact splitting behind eq. `Q47-exact`**:
`Q₄^{[7]} + 𝓛₄((A₅−B₅)/E₄) = Q̃₄` on positive phase (from the exact
terminal identity `Q₅^{[7]} = A₅ + B₅ − (A₅−B₅)/E₄`). -/
theorem Qref_four_seven_add_correction {u : ℝ} (hu : 0 < u) :
    Qref 4 7 u + evalComb referenceCorrectionComb u = QrefCore4 u := by
  have hA : HasDerivAt (A 5) (a 5 u * Bref 5 u) u := hasDerivAt_A_Bref 5 u
  have hB : HasDerivAt (Bref 5) (evalComb (derivComb (BrefComb 5)) u) u :=
    hasDerivAt_Bref 5 hu
  have hG : HasDerivAt (evalComb referenceGapComb)
      (evalComb (derivComb referenceGapComb) u) u :=
    hasDerivAt_evalComb hu _
  have hev : Qref 5 7 =ᶠ[nhds u]
      fun v => A 5 v + Bref 5 v - evalComb referenceGapComb v := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    have h := Qref_succ_succ_eq (s := 5) (by omega) v
    rw [show (5 : ℕ) + 2 = 7 from rfl, show (5 : ℕ) - 1 = 4 from rfl] at h
    rw [h, evalComb_referenceGapComb hv]
  have h57 : HasDerivAt (Qref 5 7)
      (a 5 u * Bref 5 u + evalComb (derivComb (BrefComb 5)) u
        - evalComb (derivComb referenceGapComb) u) u :=
    ((hA.add hB).sub hG).congr_of_eventuallyEq hev
  have hQ47 : Qref 4 7 u
      = (a 5 u * Bref 5 u + evalComb (derivComb (BrefComb 5)) u
          - evalComb (derivComb referenceGapComb) u) / a 4 u := by
    rw [Qref_of_lt (show 4 < 7 by omega)]
    exact Lop_eq_of_hasDerivAt h57
  have hcorr : evalComb referenceCorrectionComb u
      = evalComb (derivComb referenceGapComb) u / a 4 u := by
    unfold referenceCorrectionComb
    rw [evalComb_shiftComb hu, evalMon_aVec]
  have hcore : QrefCore4 u
      = (a 5 u * Bref 5 u + evalComb (derivComb (BrefComb 5)) u) / a 4 u :=
    Lop_eq_of_hasDerivAt (hA.add hB)
  rw [hQ47, hcorr, hcore]
  ring

/-- Two combinations with equal evaluations on positive phase have equal
iterated-derivative evaluations there (repeated `HasDerivAt` uniqueness). -/
theorem evalComb_derivIter_congr {P Q : LaurentComb}
    (h : ∀ v : ℝ, 0 < v → evalComb P v = evalComb Q v) (m : ℕ) :
    ∀ {u : ℝ}, 0 < u →
      evalComb (derivComb^[m] P) u = evalComb (derivComb^[m] Q) u := by
  induction m with
  | zero =>
      intro u hu
      simpa using h u hu
  | succ m ih =>
      intro u hu
      have hev : evalComb (derivComb^[m] P) =ᶠ[nhds u]
          evalComb (derivComb^[m] Q) := by
        filter_upwards [Ioi_mem_nhds hu] with v hv
        exact ih hv
      have hQ : HasDerivAt (evalComb (derivComb^[m] P))
          (evalComb (derivComb^[m + 1] Q) u) u :=
        (hasDerivAt_evalComb_iterate hu Q m).congr_of_eventuallyEq hev
      exact (hasDerivAt_evalComb_iterate hu P m).unique hQ

/-- The `∂^m`-images of the eq. `Q47-exact` splitting:
`∂^m Q₄^{[7]} + ∂^m(correction) = ∂^m Q̃₄` on positive phase. -/
theorem evalComb_derivIter_Q47_correction (m : ℕ) {u : ℝ} (hu : 0 < u) :
    evalComb (derivComb^[m] (QrefComb 4 7)) u
      + evalComb (derivComb^[m] referenceCorrectionComb) u
      = evalComb (derivComb^[m] QrefCore4Comb) u := by
  have hpt : ∀ v : ℝ, 0 < v →
      evalComb (QrefComb 4 7 + referenceCorrectionComb) v
        = evalComb QrefCore4Comb v := by
    intro v hv
    rw [evalComb_add, ← Qref_eq_evalComb hv, ← QrefCore4_eq_evalComb hv]
    exact Qref_four_seven_add_correction hv
  have h := evalComb_derivIter_congr hpt m hu
  rw [derivComb_iterate_add, evalComb_add] at h
  exact h

/-! ### Size bounds for the correction (paper's tab. `derivative-bounds`,
row `Q₄^{[7]} − Q̃₄`, with generic constants) -/

private theorem BrefComb_five_sizeBound : CombSizeBound 4 12 12 (BrefComb 5) :=
  ((AComb_sizeBound (by norm_num : 2 ≤ 5)).mono_t
    (by norm_num)).backward_step (by norm_num)

private theorem referenceGapComb_sizeBound :
    CombSizeBound 4 13 16 referenceGapComb :=
  (((AComb_sizeBound (by norm_num : 2 ≤ 5)).mono_t (by norm_num)).sub
    BrefComb_five_sizeBound).shift_single (by norm_num)

private theorem referenceCorrectionComb_sizeBound :
    CombSizeBound 4 22 208 referenceCorrectionComb :=
  referenceGapComb_sizeBound.backward_step (by norm_num)

private theorem gap_base_apply_le_zero :
    ∀ ν ∈ (AComb 5 - BrefComb 5).support, ν 4 ≤ 0 := by
  intro ν hν
  rcases Finset.mem_union.mp (Finsupp.support_sub hν) with h | h
  · exact le_of_eq (AComb_apply_eq_zero h (by norm_num))
  · obtain ⟨ν', hν', rfl⟩ := mem_shiftComb_support
      (P := derivComb (AComb 5)) (μ := aVec 5) h
    obtain ⟨ν₀, hν₀, i, hi, rfl⟩ := exists_of_mem_derivComb_support hν'
    have h0 : ν₀ 4 = 0 := AComb_apply_eq_zero hν₀ (by norm_num)
    have hi2 : i ≤ 4 := by
      have h := AComb_support_index_le hν₀ i hi
      omega
    have hds : derivShift i 4 ≤ 0 := derivShift_apply_nonpos hi2
    have haV : 0 ≤ aVec 5 4 := aVec_apply_nonneg 5 4
    rw [Finsupp.sub_apply, Finsupp.add_apply]
    omega

private theorem referenceGapComb_neg :
    ∀ ν ∈ referenceGapComb.support, ν 4 ≤ -1 := by
  intro ν hν
  obtain ⟨ν', hν', rfl⟩ := mem_shiftComb_support
    (P := AComb 5 - BrefComb 5) (μ := Finsupp.single 4 1) hν
  have h0 := gap_base_apply_le_zero ν' hν'
  rw [Finsupp.sub_apply, Finsupp.single_eq_same]
  omega

private theorem referenceCorrectionComb_neg :
    ∀ ν ∈ referenceCorrectionComb.support, ν 4 ≤ -1 :=
  shiftComb_apply_le_neg_one (aVec_apply_nonneg _ _)
    (derivComb_apply_le_neg_one referenceGapComb_sizeBound.maxIdx_le
      referenceGapComb_neg)

/-- The correction and its first two derivatives are below an eighth of the
eq. `R7-tail` target (paper: `|∂^k(Q₄^{[7]} − Q̃₄)| ≤ 1299 E₃¹⁰/E₄`; here
with the generic constants `123552·E₃³²/E₄`). -/
theorem abs_evalComb_derivIter_referenceCorrection_le {m : ℕ} (hm : m ≤ 2)
    {u : ℝ} (hu : 1 ≤ u) :
    |evalComb (derivComb^[m] referenceCorrectionComb) u|
      ≤ Real.exp (-(3.7e6 : ℝ)) / 8 := by
  have hT3 : (3.8e6 : ℝ) ≤ E 3 u := big_le_E (by omega) hu
  have hSB : CombSizeBound 4 32 123552
      (derivComb^[m] referenceCorrectionComb) := by
    interval_cases m
    · simpa using referenceCorrectionComb_sizeBound.mono
        (by norm_num) (by norm_num)
    · rw [Function.iterate_one]
      exact referenceCorrectionComb_sizeBound.derivComb_step.mono
        (by norm_num) (by norm_num)
    · rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
        Function.iterate_one]
      exact referenceCorrectionComb_sizeBound.derivComb_step.derivComb_step.mono
        (by norm_num) (by norm_num)
  have hneg : ∀ ν ∈ (derivComb^[m] referenceCorrectionComb).support,
      ν 4 ≤ -1 :=
    derivComb_iterate_apply_le_neg_one
      referenceCorrectionComb_sizeBound.maxIdx_le referenceCorrectionComb_neg m
  refine (abs_evalComb_le_of_sizeBound hSB hneg hu).trans ?_
  have hE4 : E 4 u = Real.exp (E 3 u) := E_succ 3 u
  rw [show (4 : ℕ) - 1 = 3 from rfl, hE4]
  exact poly_div_exp_le_target hT3 (by norm_num) (by push_cast; nlinarith)

/-! ### The numerical tail (eqs. `Q47-tail-majorant`, `R7-tail`) -/

/-- **Eq. `Q47-tail-majorant` / eq. `R7-tail`, master form**: for `m ≤ 2`
and `u ≥ 1`,
`|∂^m Q₄^* − ∂^m Q̃₄| ≤ exp(−3.7·10⁶)/2` (at the level of the explicit
series `QrefLimitIterDeriv` and the comb representation of `Q̃₄`). -/
theorem abs_QrefLimitIterDeriv_four_sub_core_le {m : ℕ} (hm : m ≤ 2) {u : ℝ}
    (hu : 1 ≤ u) :
    |QrefLimitIterDeriv m 4 u - evalComb (derivComb^[m] QrefCore4Comb) u|
      ≤ Real.exp (-(3.7e6 : ℝ)) / 2 := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have h1 : |QrefLimitIterDeriv m 4 u
        - evalComb (derivComb^[m] (QrefComb 4 8)) u|
      ≤ Real.exp (-(3.7e6 : ℝ)) / 8 := by
    have h := abs_QrefLimitIterDeriv_sub_evalComb_le (s := 4) (R := 8)
      (by omega) (by omega) (by omega) hm hu
    rw [show (8 : ℕ) - 4 = 4 from rfl] at h
    exact h.trans (four_mul_exp_neg_E_four_half_le_target hu)
  have h2 : evalComb (derivComb^[m] (QrefComb 4 8)) u
        - evalComb (derivComb^[m] (QrefComb 4 7)) u
      = evalComb (derivComb^[m] (DeltaComb 4 7)) u :=
    (evalComb_derivIter_DeltaComb_eq (s := 4) (R := 7) (by omega) (by omega)
      m hu0).symm
  have h3 := abs_evalComb_derivIter_DeltaComb_four_seven_le hm hu
  have h4 := evalComb_derivIter_Q47_correction m hu0
  have h5 := abs_evalComb_derivIter_referenceCorrection_le hm hu
  have hkey : QrefLimitIterDeriv m 4 u
        - evalComb (derivComb^[m] QrefCore4Comb) u
      = (QrefLimitIterDeriv m 4 u - evalComb (derivComb^[m] (QrefComb 4 8)) u)
        + evalComb (derivComb^[m] (DeltaComb 4 7)) u
        - evalComb (derivComb^[m] referenceCorrectionComb) u := by
    linarith [h2, h4]
  rw [hkey]
  have habs1 : |(QrefLimitIterDeriv m 4 u
        - evalComb (derivComb^[m] (QrefComb 4 8)) u)
        + evalComb (derivComb^[m] (DeltaComb 4 7)) u|
      ≤ |QrefLimitIterDeriv m 4 u
          - evalComb (derivComb^[m] (QrefComb 4 8)) u|
        + |evalComb (derivComb^[m] (DeltaComb 4 7)) u| := abs_add_le _ _
  calc |(QrefLimitIterDeriv m 4 u
        - evalComb (derivComb^[m] (QrefComb 4 8)) u)
        + evalComb (derivComb^[m] (DeltaComb 4 7)) u
        - evalComb (derivComb^[m] referenceCorrectionComb) u|
      ≤ |(QrefLimitIterDeriv m 4 u
          - evalComb (derivComb^[m] (QrefComb 4 8)) u)
          + evalComb (derivComb^[m] (DeltaComb 4 7)) u|
        + |evalComb (derivComb^[m] referenceCorrectionComb) u| := abs_sub _ _
    _ ≤ Real.exp (-(3.7e6 : ℝ)) / 2 := by linarith [habs1, h1, h3, h5]

/-- **Eq. `R7-tail`, value piece**: `|Q₄^*(u) − Q̃₄(u)| ≤ exp(−3.7·10⁶)`
for `u ≥ 1`. -/
theorem abs_QrefLimit_four_sub_QrefCore4_le {u : ℝ} (hu : 1 ≤ u) :
    |QrefLimit 4 u - QrefCore4 u| ≤ Real.exp (-(3.7e6 : ℝ)) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have h := abs_QrefLimitIterDeriv_four_sub_core_le (m := 0) (by omega) hu
  simp only [Function.iterate_zero_apply] at h
  rw [← QrefLimit_eq_iterDeriv_zero 4 hu0, ← QrefCore4_eq_evalComb hu0] at h
  have hp := (Real.exp_pos (-(3.7e6 : ℝ))).le
  linarith

/-- The first derivative of `Q̃₄` is the evaluation of the formally
differentiated core comb (positive phase). -/
theorem deriv_QrefCore4_eq {u : ℝ} (hu : 0 < u) :
    deriv QrefCore4 u = evalComb (derivComb QrefCore4Comb) u := by
  have hev : QrefCore4 =ᶠ[nhds u] evalComb QrefCore4Comb := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact QrefCore4_eq_evalComb hv
  rw [hev.deriv_eq, (hasDerivAt_evalComb hu QrefCore4Comb).deriv]

/-- The second derivative of `Q̃₄` as an evaluated comb (positive phase). -/
theorem deriv2_QrefCore4_eq {u : ℝ} (hu : 0 < u) :
    deriv (deriv QrefCore4) u = evalComb (derivComb^[2] QrefCore4Comb) u := by
  have hev : deriv QrefCore4 =ᶠ[nhds u] evalComb (derivComb QrefCore4Comb) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact deriv_QrefCore4_eq hv
  rw [hev.deriv_eq, (hasDerivAt_evalComb hu (derivComb QrefCore4Comb)).deriv,
    show derivComb^[2] QrefCore4Comb = derivComb (derivComb QrefCore4Comb) from
      by rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
        Function.iterate_one]]

/-- **Eq. `R7-tail`, first-derivative piece**:
`|(Q₄^*)'(u) − Q̃₄'(u)| ≤ exp(−3.7·10⁶)` for `u ≥ 1` (with `(Q₄^*)'`
realized by the explicit series `QrefLimitIterDeriv 1 4`; see
`hasDerivAt_QrefLimit` for the identification on `1 < u`). -/
theorem abs_QrefLimitIterDeriv_one_four_sub_deriv_core_le {u : ℝ}
    (hu : 1 ≤ u) :
    |QrefLimitIterDeriv 1 4 u - deriv QrefCore4 u|
      ≤ Real.exp (-(3.7e6 : ℝ)) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have h := abs_QrefLimitIterDeriv_four_sub_core_le (m := 1) (by omega) hu
  rw [Function.iterate_one] at h
  rw [deriv_QrefCore4_eq hu0]
  have hp := (Real.exp_pos (-(3.7e6 : ℝ))).le
  linarith

/-- **Eq. `R7-tail`, second-derivative piece**:
`|(Q₄^*)''(u) − Q̃₄''(u)| ≤ exp(−3.7·10⁶)` for `u ≥ 1` (with `(Q₄^*)''`
realized by the explicit series `QrefLimitIterDeriv 2 4`; see
`hasDerivAt_QrefLimitIterDeriv` for the identification on `1 < u`). -/
theorem abs_QrefLimitIterDeriv_two_four_sub_deriv2_core_le {u : ℝ}
    (hu : 1 ≤ u) :
    |QrefLimitIterDeriv 2 4 u - deriv (deriv QrefCore4) u|
      ≤ Real.exp (-(3.7e6 : ℝ)) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have h := abs_QrefLimitIterDeriv_four_sub_core_le (m := 2) (by omega) hu
  rw [deriv2_QrefCore4_eq hu0]
  have hp := (Real.exp_pos (-(3.7e6 : ℝ))).le
  linarith

/-! ## Differentiability of the limit and the recurrence
(eq. `reference-recurrence`)

Term-by-term differentiation of the increment series, on the *open* phase
set `1 < u` (see the file docstring for why the endpoint `u = 1` is
excluded here, and why that suffices for the paper's downstream use). -/

/-- The `m`-th derivative series is differentiable on `1 < u`, with
derivative the `(m+1)`-st series (the paper's "converges locally uniformly
together with its first two derivatives"). -/
theorem hasDerivAt_QrefLimitIterDeriv {s : ℕ} (hs : 4 ≤ s) {m : ℕ}
    (hm : m + 1 ≤ 2) {u : ℝ} (hu : 1 < u) :
    HasDerivAt (QrefLimitIterDeriv m s) (QrefLimitIterDeriv (m + 1) s u) u := by
  have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
  have hu1 : (1 : ℝ) ≤ u := hu.le
  -- the head term
  have hhead : HasDerivAt (evalComb (derivComb^[m] (QrefComb s (s + 1))))
      (evalComb (derivComb^[m + 1] (QrefComb s (s + 1))) u) u :=
    hasDerivAt_evalComb_iterate hu0 _ m
  -- the first seven increments (whose depth may fall below `R = 8`)
  have hfin : HasDerivAt
      (fun v => ∑ k ∈ Finset.range 7,
        evalComb (derivComb^[m] (DeltaComb s (s + 1 + k))) v)
      (∑ k ∈ Finset.range 7,
        evalComb (derivComb^[m + 1] (DeltaComb s (s + 1 + k))) u) u :=
    HasDerivAt.fun_sum fun k _ => hasDerivAt_evalComb_iterate hu0 _ m
  -- the tail: term-by-term differentiation on the open set `Ioi 1`
  have htail : HasDerivAt
      (fun v => ∑' k : ℕ,
        evalComb (derivComb^[m] (DeltaComb s (s + 1 + (k + 7)))) v)
      (∑' k : ℕ,
        evalComb (derivComb^[m + 1] (DeltaComb s (s + 1 + (k + 7)))) u) u := by
    have hcsum : Summable fun k : ℕ =>
        2 * Real.exp (-(E (s + 4 + k) 1) / 2) := by
      have hg : Summable fun k : ℕ =>
          2 * Real.exp (-(E (s + 4) 1) / 2) * (1 / 2 : ℝ) ^ k :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      refine Summable.of_nonneg_of_le (fun k => by positivity)
        (fun k => ?_) hg
      have h := exp_neg_E_add_le (le_refl (1 : ℝ)) (j := s + 4) (by omega) k
      linarith
    refine hasDerivAt_tsum_of_isPreconnected hcsum isOpen_Ioi
      isPreconnected_Ioi ?_ ?_ (Set.mem_Ioi.mpr hu) ?_ (Set.mem_Ioi.mpr hu)
    · intro k y hy
      exact hasDerivAt_evalComb_iterate
        (lt_trans one_pos (Set.mem_Ioi.mp hy)) _ m
    · intro k y hy
      have hy1 : (1 : ℝ) ≤ y := (Set.mem_Ioi.mp hy).le
      have hb := abs_evalComb_derivIter_DeltaComb_le (s := s)
        (R := s + 1 + (k + 7)) (by omega) hs (by omega) (by omega) hy1
      rw [show s + 1 + (k + 7) - 4 = s + 4 + k by omega] at hb
      rw [Real.norm_eq_abs]
      refine hb.trans ?_
      have hmono : E (s + 4 + k) 1 ≤ E (s + 4 + k) y := E_mono _ hy1
      have h := Real.exp_le_exp.mpr
        (show -(E (s + 4 + k) y) / 2 ≤ -(E (s + 4 + k) 1) / 2 by linarith)
      linarith
    · exact (summable_nat_add_iff (f := fun k : ℕ =>
        evalComb (derivComb^[m] (DeltaComb s (s + 1 + k))) u) 7).mpr
        (summable_evalComb_derivIter_DeltaComb hs (by omega) hu1)
  -- reassemble the split series
  have hval : evalComb (derivComb^[m + 1] (QrefComb s (s + 1))) u
        + ∑ k ∈ Finset.range 7,
            evalComb (derivComb^[m + 1] (DeltaComb s (s + 1 + k))) u
        + ∑' k : ℕ,
            evalComb (derivComb^[m + 1] (DeltaComb s (s + 1 + (k + 7)))) u
      = QrefLimitIterDeriv (m + 1) s u := by
    have hsplit := Summable.sum_add_tsum_nat_add (f := fun k : ℕ =>
      evalComb (derivComb^[m + 1] (DeltaComb s (s + 1 + k))) u) 7
      (summable_evalComb_derivIter_DeltaComb hs (by omega) hu1)
    unfold QrefLimitIterDeriv
    linarith
  rw [← hval]
  refine ((hhead.add hfin).add htail).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hu] with v hv
  have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
  show QrefLimitIterDeriv m s v
      = evalComb (derivComb^[m] (QrefComb s (s + 1))) v
        + (∑ k ∈ Finset.range 7,
            evalComb (derivComb^[m] (DeltaComb s (s + 1 + k))) v)
        + ∑' k : ℕ,
            evalComb (derivComb^[m] (DeltaComb s (s + 1 + (k + 7)))) v
  have hsplit := Summable.sum_add_tsum_nat_add (f := fun k : ℕ =>
    evalComb (derivComb^[m] (DeltaComb s (s + 1 + k))) v) 7
    (summable_evalComb_derivIter_DeltaComb hs (by omega) hv1)
  unfold QrefLimitIterDeriv
  linarith

/-- **`C¹` half of `lem:backward-reference-convergence`**: the limit
`Q_s^*` is differentiable at every `u > 1`, with derivative the explicit
series `QrefLimitIterDeriv 1 s`. -/
theorem hasDerivAt_QrefLimit {s : ℕ} (hs : 4 ≤ s) {u : ℝ} (hu : 1 < u) :
    HasDerivAt (QrefLimit s) (QrefLimitIterDeriv 1 s u) u := by
  have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
  have h := hasDerivAt_QrefLimitIterDeriv hs (m := 0) (by omega) hu
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hu0] with v hv
  exact QrefLimit_eq_iterDeriv_zero s hv

/-- The identification `(Q_{s+1}^*)' = a_s Q_s^*` at the level of the
explicit series (limit of `(Q_{s+1}^{[R]})' = a_s Q_s^{[R]}`). -/
theorem QrefLimitIterDeriv_one_succ_eq {s : ℕ} (hs : 4 ≤ s) {u : ℝ}
    (hu : 1 ≤ u) :
    QrefLimitIterDeriv 1 (s + 1) u = a s u * QrefLimit s u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have h1 := tendsto_evalComb_derivIter_QrefComb (s := s + 1) (by omega)
    (m := 1) (by omega) hu
  have h2 : Filter.Tendsto (fun R : ℕ => a s u * Qref s R u) Filter.atTop
      (nhds (a s u * QrefLimit s u)) :=
    (Qref_tendsto_QrefLimit hs hu).const_mul _
  refine tendsto_nhds_unique h1 (Filter.Tendsto.congr' ?_ h2)
  filter_upwards [Filter.eventually_ge_atTop (s + 1)] with R hR
  have hQ : HasDerivAt (Qref (s + 1) R)
      (evalComb (derivComb (QrefComb (s + 1) R)) u) u := hasDerivAt_Qref hu0
  have h3 : Qref s R u
      = evalComb (derivComb (QrefComb (s + 1) R)) u / a s u := by
    rw [Qref_of_lt (show s < R by omega)]
    exact Lop_eq_of_hasDerivAt hQ
  rw [Function.iterate_one, h3, mul_div_cancel₀ _ (a_pos s u).ne']

/-- **Eq. `reference-recurrence`**: `(Q_{s+1}^*)' = a_s Q_s^*` for `s ≥ 4`
and `u > 1`. -/
theorem hasDerivAt_QrefLimit_succ {s : ℕ} (hs : 4 ≤ s) {u : ℝ} (hu : 1 < u) :
    HasDerivAt (QrefLimit (s + 1)) (a s u * QrefLimit s u) u := by
  have h := hasDerivAt_QrefLimit (s := s + 1) (by omega) hu
  rwa [QrefLimitIterDeriv_one_succ_eq hs hu.le] at h

/-! ## Depth 3 (eq. `R7-tail`, the `Q₃^* − Q̃₃` half)

`QrefLimit`'s machinery starts at `s = 4` (the defect identity behind the
increments fails at depth 3, see `Erdos320.Lemmas.BackwardReference`);
the depth-3 limit is *defined* through the recurrence,
`Q₃^* = 𝓛₃ Q₄^* = (Q₄^*)'/a₃`. -/

/-- `Q₃^*`: the depth-3 limiting reference function, defined through the
recurrence as `(Q₄^*)'/a₃`. -/
noncomputable def QrefLimit3 : ℝ → ℝ := fun u =>
  QrefLimitIterDeriv 1 4 u / a 3 u

/-- **Eq. `R7-tail`, depth-3 value piece**:
`|Q₃^*(u) − Q̃₃(u)| ≤ exp(−3.7·10⁶)` for `u ≥ 1`. -/
theorem abs_QrefLimit3_sub_QrefCore3_le {u : ℝ} (hu : 1 ≤ u) :
    |QrefLimit3 u - QrefCore3 u| ≤ Real.exp (-(3.7e6 : ℝ)) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hkey : QrefLimit3 u - QrefCore3 u
      = (QrefLimitIterDeriv 1 4 u - deriv QrefCore4 u) / a 3 u := by
    unfold QrefLimit3 QrefCore3 Lop
    ring
  rw [hkey, abs_div, abs_of_pos (a_pos 3 u)]
  have h := abs_QrefLimitIterDeriv_one_four_sub_deriv_core_le hu
  have ha1 : (1 : ℝ) ≤ a 3 u := one_le_a hu 3
  calc |QrefLimitIterDeriv 1 4 u - deriv QrefCore4 u| / a 3 u
      ≤ |QrefLimitIterDeriv 1 4 u - deriv QrefCore4 u| / 1 :=
        div_le_div_of_nonneg_left (abs_nonneg _) one_pos ha1
    _ = |QrefLimitIterDeriv 1 4 u - deriv QrefCore4 u| := div_one _
    _ ≤ Real.exp (-(3.7e6 : ℝ)) := h

end Erdos320
