import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Iterated exponentials and the normalizing products of the exponential-scale iteration

The manuscript's exponential-scale bookkeeping
(§ `sec:exponential-iteration`; eq. `D-J`, `a-rho`):
```
E₀(u) = u,   E_{j+1}(u) = exp (E_j(u)),
D_r(u) = ∏_{j=0}^{r-3} E_j(u)  (r ≥ 3),  D₂ = 1,
J_r(u) = D_r(u) + D_{r-1}(u),
a_r(u) = E_{r-2}'(u) = ∏_{j=1}^{r-2} E_j(u),
A_s(u) = 1 + ∑_{j=3}^{s} D_j(u),
q_r(u) = D_{r-2}(u)/D_r(u) = 1/(E_{r-3}(u)·E_{r-4}(u)).
```
The names `E`, `D`, `J`, `a`, `A`, `q` deliberately mirror the paper's
notation (see the notation table at the end of its overview section,
§ `sec:overview`); each is documented here with its paper meaning.

Everything is defined for all natural indices; the paper's side conditions
(`r ≥ 3` etc.) appear as hypotheses of the lemmas that need them.  With the
convention `n - 2 = 0` for `n ≤ 2` (ℕ-subtraction), `D r = 1` for `r ≤ 2`,
matching the paper's `D₂ = 1`.
-/

namespace Erdos320

/-- `E j u`: the `j`-fold exponential iterate `E_j(u)` of the manuscript
(eq. `D-J`); `E 0 u = u`, `E (j+1) u = exp (E j u)`. -/
noncomputable def E : ℕ → ℝ → ℝ
  | 0, u => u
  | j + 1, u => Real.exp (E j u)

@[simp] theorem E_zero (u : ℝ) : E 0 u = u := rfl

theorem E_succ (j : ℕ) (u : ℝ) : E (j + 1) u = Real.exp (E j u) := rfl

/-- Iterating exponentials composes additively: `E j (E k u) = E (j+k) u`. -/
theorem E_comp (j k : ℕ) (u : ℝ) : E j (E k u) = E (j + k) u := by
  induction j with
  | zero => simp
  | succ j ih => rw [E_succ, ih, ← E_succ, Nat.succ_add]

/-- The endpoint identity `E_j(e) = E_{j+1}(1)`: consecutive exponential
scales describe the same number at their common endpoint
(eq. `endpoint-matching`). -/
theorem E_exp_one (j : ℕ) : E j (Real.exp 1) = E (j + 1) 1 := by
  have h : Real.exp 1 = E 1 1 := by simp [E_succ]
  rw [h, E_comp]

theorem E_pos_of_pos {u : ℝ} (hu : 0 < u) (j : ℕ) : 0 < E j u := by
  cases j with
  | zero => simpa using hu
  | succ j => exact Real.exp_pos _

/-- For `j ≥ 1`, `E j u` is positive regardless of the sign of `u`. -/
theorem E_pos_of_one_le {j : ℕ} (hj : 1 ≤ j) (u : ℝ) : 0 < E j u := by
  cases j with
  | zero => omega
  | succ j => rw [E_succ]; exact Real.exp_pos _

/-- Each iterate is strictly below the next: `E j u < E (j+1) u`
(from `x < exp x`). -/
theorem E_lt_E_succ (j : ℕ) (u : ℝ) : E j u < E (j + 1) u := by
  rw [E_succ]
  linarith [Real.add_one_le_exp (E j u)]

theorem one_le_E_of_one_le {u : ℝ} (hu : 1 ≤ u) (j : ℕ) : 1 ≤ E j u := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
      rw [E_succ]
      calc (1 : ℝ) ≤ 1 + E j u := by linarith [ih]
      _ ≤ Real.exp (E j u) := by linarith [Real.add_one_le_exp (E j u)]

/-- `E j` is strictly monotone in `u`. -/
theorem E_strictMono (j : ℕ) : StrictMono (E j) := by
  induction j with
  | zero => exact fun _ _ h => h
  | succ j ih => exact fun x y h => Real.exp_lt_exp.mpr (ih h)

theorem E_mono (j : ℕ) : Monotone (E j) := (E_strictMono j).monotone

/-- `E j u` is monotone in the depth `j` when `u ≥ 1`.  (In fact
`E j u < E (j+1) u` always, by `E_lt_E_succ`.) -/
theorem E_mono_depth {u : ℝ} (_hu : 1 ≤ u) : Monotone fun j => E j u :=
  monotone_nat_of_le_succ fun j => (E_lt_E_succ j u).le

/-- `E` has derivative `∏_{j=1}^{k} E_j(u)` at every point: the chain-rule
product behind the manuscript's `a_r` (eq. `a-rho`). -/
theorem hasDerivAt_E (k : ℕ) (u : ℝ) :
    HasDerivAt (E k) (∏ j ∈ Finset.Icc 1 k, E j u) u := by
  induction k with
  | zero =>
      have hprod : (∏ j ∈ Finset.Icc 1 0, E j u) = 1 := by simp
      rw [hprod]
      exact hasDerivAt_id u
  | succ k ih =>
      have h : HasDerivAt (fun v => Real.exp (E k v))
          (Real.exp (E k u) * ∏ j ∈ Finset.Icc 1 k, E j u) u := ih.exp
      have hfun : (fun v => Real.exp (E k v)) = E (k + 1) := by
        funext v; rw [E_succ]
      have hprod : Real.exp (E k u) * ∏ j ∈ Finset.Icc 1 k, E j u
          = ∏ j ∈ Finset.Icc 1 (k + 1), E j u := by
        rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1), ← E_succ, mul_comm]
      rw [hfun, hprod] at h
      exact h

/-- `D r u = ∏_{j=0}^{r-3} E_j(u)`: the principal normalization `D_r`
(eq. `D-J`).  For `r ≤ 2` the range is empty and `D r = 1`, matching the
paper's `D₂ = 1`. -/
noncomputable def D (r : ℕ) (u : ℝ) : ℝ := ∏ j ∈ Finset.range (r - 2), E j u

theorem D_of_le_two {r : ℕ} (hr : r ≤ 2) (u : ℝ) : D r u = 1 := by
  unfold D
  rw [Nat.sub_eq_zero_of_le hr]
  simp

theorem D_succ {r : ℕ} (hr : 2 ≤ r) (u : ℝ) :
    D (r + 1) u = D r u * E (r - 2) u := by
  unfold D
  rw [show r + 1 - 2 = (r - 2) + 1 by omega, Finset.prod_range_succ]

theorem D_pos {u : ℝ} (hu : 0 < u) (r : ℕ) : 0 < D r u :=
  Finset.prod_pos fun j _ => E_pos_of_pos hu j

/-- The endpoint identity `D_r(e) = D_{r+1}(1)` (eq. `endpoint-matching`). -/
theorem D_exp_one {r : ℕ} (hr : 2 ≤ r) : D r (Real.exp 1) = D (r + 1) 1 := by
  have hidx : r + 1 - 2 = (r - 2) + 1 := by omega
  have hs : (∏ j ∈ Finset.range ((r - 2) + 1), E j 1)
      = (∏ j ∈ Finset.range (r - 2), E (j + 1) 1) * E 0 1 :=
    Finset.prod_range_succ' (fun j => E j 1) (r - 2)
  unfold D
  rw [hidx, hs, E_zero, mul_one]
  exact Finset.prod_congr rfl fun j _ => E_exp_one j

/-- `J r = D r + D (r-1)`: the endpoint-corrected normalization `J_r`
(eq. `D-J`), whose second summand records the endpoint-matching
contribution. -/
noncomputable def J (r : ℕ) (u : ℝ) : ℝ := D r u + D (r - 1) u

theorem J_pos {u : ℝ} (hu : 0 < u) (r : ℕ) : 0 < J r u :=
  add_pos (D_pos hu r) (D_pos hu (r - 1))

/-- The endpoint identity `J_r(e) = J_{r+1}(1)` (eq. `endpoint-matching`). -/
theorem J_exp_one {r : ℕ} (hr : 3 ≤ r) : J r (Real.exp 1) = J (r + 1) 1 := by
  unfold J
  rw [D_exp_one (by omega), show r + 1 - 1 = (r - 1) + 1 by omega,
    ← D_exp_one (by omega : 2 ≤ r - 1)]

/-- `a r u = ∏_{j=1}^{r-2} E_j(u)`: the chain-rule derivative factor `a_r`
of eq. `a-rho`; see `hasDerivAt_E_sub_two` for `a_r = E_{r-2}'`. -/
noncomputable def a (r : ℕ) (u : ℝ) : ℝ := ∏ j ∈ Finset.Icc 1 (r - 2), E j u

theorem a_pos (r : ℕ) (u : ℝ) : 0 < a r u :=
  Finset.prod_pos fun _ hj => E_pos_of_one_le (Finset.mem_Icc.mp hj).1 u

/-- `a_r` is the derivative of `E_{r-2}`, as in eq. `a-rho`. -/
theorem hasDerivAt_E_sub_two (r : ℕ) (u : ℝ) :
    HasDerivAt (E (r - 2)) (a r u) u :=
  hasDerivAt_E (r - 2) u

/-- On nonzero arguments, `a r u = D (r+1) u / u`: the identity
`a_{r-1} = D_r / u` used repeatedly in § `sec:exponential-iteration`
(shifted by one index). -/
theorem a_eq_D_succ_div {u : ℝ} (hu : u ≠ 0) {r : ℕ} (hr : 2 ≤ r) :
    a r u = D (r + 1) u / u := by
  have hidx : r + 1 - 2 = (r - 2) + 1 := by omega
  have hs : (∏ j ∈ Finset.range ((r - 2) + 1), E j u)
      = (∏ j ∈ Finset.range (r - 2), E (j + 1) u) * E 0 u :=
    Finset.prod_range_succ' (fun j => E j u) (r - 2)
  have hIcc : ∀ n : ℕ, (∏ j ∈ Finset.Icc 1 n, E j u)
      = ∏ j ∈ Finset.range n, E (1 + j) u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1), ih,
          Finset.prod_range_succ, Nat.add_comm 1 n]
  have hD : D (r + 1) u = a r u * u := by
    unfold D a
    rw [hidx, hs, hIcc (r - 2), E_zero]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by rw [Nat.add_comm]
  rw [hD, mul_div_assoc, div_self hu, mul_one]

/-- `A s u = 1 + ∑_{j=3}^s D_j(u)`: the cumulative normalization `A_s` of
eq. `D-identity` / `lem:backward-reference-convergence`. -/
noncomputable def A (s : ℕ) (u : ℝ) : ℝ := 1 + ∑ j ∈ Finset.Icc 3 s, D j u

theorem A_pos {u : ℝ} (hu : 0 < u) (s : ℕ) : 0 < A s u :=
  add_pos_of_pos_of_nonneg one_pos <|
    Finset.sum_nonneg fun j _ => (D_pos hu j).le

/-- `q r u = 1/(E_{r-3}(u)·E_{r-4}(u))`: the relative gap
`q_r = D_{r-2}/D_r` controlling the depth-`r` iteration errors of
§ `sec:exponential-iteration`. -/
noncomputable def q (r : ℕ) (u : ℝ) : ℝ := 1 / (E (r - 3) u * E (r - 4) u)

/-- For `r ≥ 5`, `q_r` is indeed the ratio `D_{r-2}/D_r`. -/
theorem q_eq_D_ratio {u : ℝ} (hu : 0 < u) {r : ℕ} (hr : 5 ≤ r) :
    q r u = D (r - 2) u / D r u := by
  have h1 : D r u = D (r - 1) u * E (r - 3) u := by
    have h := D_succ (r := r - 1) (by omega) u
    rw [show r - 1 + 1 = r by omega, show r - 1 - 2 = r - 3 by omega] at h
    exact h
  have h2 : D (r - 1) u = D (r - 2) u * E (r - 4) u := by
    have h := D_succ (r := r - 2) (by omega) u
    rw [show r - 2 + 1 = r - 1 by omega, show r - 2 - 2 = r - 4 by omega] at h
    exact h
  have hD2 : D (r - 2) u ≠ 0 := (D_pos hu _).ne'
  have hE3 : E (r - 3) u ≠ 0 := (E_pos_of_pos hu _).ne'
  have hE4 : E (r - 4) u ≠ 0 := (E_pos_of_pos hu _).ne'
  unfold q
  rw [h1, h2]
  field_simp

end Erdos320
