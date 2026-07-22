import Erdos320.Defs.IteratedExp
import Erdos320.Lemmas.IteratedExpBounds
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Backward reference functions (`sec:backward-reference`)

The manuscript's backward differentiation operator `𝓛_r f = f' / a_r`
(eq. `L-def`) and the finite backward reference functions
`Q_s^{[R]} = 𝓛_s 𝓛_{s+1} ⋯ 𝓛_{R-1} J_R` (eq. `finite-reference`), together
with the finite-depth *exact* identities of §5–6:

* the logarithmic-differentiation identities `𝓛_r D_{r+1} = A_r`
  (eq. `D-identity`), here in `HasDerivAt` form (`hasDerivAt_D_succ`,
  `hasDerivAt_A`);
* the defect identity `J_{r+1}' = a_r (J_r + R_r)` with
  `R_r = A_{r-2} + A_{r-1}/E_{r-2}` and the ratio bound `R_r ≤ 3 q_r J_r`
  (eq. `J-defect`; the paper asserts the ratio bound "for all sufficiently
  large `r`" — here it is proved explicitly for `r ≥ 6`);
* the `B_j = A_j'/a_j` recursion `B_j = (A_{j-1} + B_{j-1})/E_{j-2}`
  (eq. `Bj-recursion`) and the `B_j` value bounds (the unlabeled auxiliary
  estimate before eq. `Bj-derivative-bound`);
* the paper's explicit reference core `Q̃₄ = 𝓛₄(A₅ + A₅'/a₅)`,
  `Q̃₃ = 𝓛₃ Q̃₄` (eq. `reference-core`);
* the two exact terminal identities
  `Q_s^{[s+1]} = A_s + A_{s-1}/E_{s-2}` and
  `Q_s^{[s+2]} = A_s + B_s − (A_s − B_s)/E_{s-1}`
  (proof of `lem:backward-reference-convergence`).

The infinite-depth convergence statement (eq. `reference-increment`,
eq. `R7-tail`) is *not* proved here; it is built on top of this file.

Paper-vs-Lean notes:
* `hasDerivAt_J_succ` (eq. `J-defect`) requires `4 ≤ r`: at `r = 3` the
  identity `A_r = J_r + A_{r-2}` behind the cancellation fails
  (`A₃ = 1 + D₃` but `J₃ + A₁ = D₃ + 2`).  This is consistent with the
  paper, whose proof says "take `r ≥ 5`".
* The ratio bound `R_r/J_r ≤ 3 q_r` is proved for `r ≥ 6` and all `u ≥ 1`
  (the paper leaves the threshold implicit).
* The derivative bound `|B_j'| ≤ 4 A_{j-1} x_{j-3}' / x_{j-2}` of
  eq. `Bj-derivative-bound` is proved in the follow-up file
  (`BackwardReferenceLimit.lean`, `abs_deriv_Bref_le`), not here.
-/

namespace Erdos320

/-! ## Elementary exponential estimates

(`two_mul_le_exp` comes from `Erdos320.Lemmas.IteratedExpBounds`.) -/

/-- For `j ≥ 1` and `u ≥ 1`, the iterated exponential satisfies
`E_j(u) ≥ 2` (indeed `≥ e`). -/
theorem two_le_E {j : ℕ} (hj : 1 ≤ j) {u : ℝ} (hu : 1 ≤ u) : (2 : ℝ) ≤ E j u := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [E_succ]
  have h1 : (1 : ℝ) ≤ E k u := one_le_E_of_one_le hu k
  calc (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    _ ≤ Real.exp (E k u) := Real.exp_le_exp.mpr h1

/-! ## Small explicit values of `D`, `A`, `a`

These closed forms (in particular `A₅ = 1 + u + u·E₁ + u·E₁·E₂`) are what
the proved interval-certificate lemmas over the
reference core `Q̃₄`, `Q̃₃` (eq. `reference-core`; `CertLow*.lean`,
`CertHigh*.lean`) are stated against. -/

/-- `D₃(u) = u` (eq. `D-J`, smallest nontrivial normalization). -/
theorem D_three (u : ℝ) : D 3 u = u := by
  unfold D
  rw [show (3 : ℕ) - 2 = 1 from rfl, Finset.prod_range_one, E_zero]

/-- `D₄(u) = u · E₁(u)` (eq. `D-J`). -/
theorem D_four (u : ℝ) : D 4 u = u * E 1 u := by
  unfold D
  rw [show (4 : ℕ) - 2 = 2 from rfl, show (2 : ℕ) = 1 + 1 from rfl,
    Finset.prod_range_succ, Finset.prod_range_one, E_zero]

/-- `D₅(u) = u · E₁(u) · E₂(u)` (eq. `D-J`). -/
theorem D_five (u : ℝ) : D 5 u = u * E 1 u * E 2 u := by
  unfold D
  rw [show (5 : ℕ) - 2 = 3 from rfl, show (3 : ℕ) = 2 + 1 from rfl,
    Finset.prod_range_succ, show (2 : ℕ) = 1 + 1 from rfl,
    Finset.prod_range_succ, Finset.prod_range_one, E_zero]

/-- `A₂(u) = 1`: the cumulative normalization below its first summand
(empty sum in eq. `D-identity`'s `A_j = 1 + ∑_{k=3}^j D_k`). -/
theorem A_two (u : ℝ) : A 2 u = 1 := by
  unfold A
  rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, add_zero]

/-- `a₂(u) = 1` (empty chain-rule product in eq. `a-rho`). -/
theorem a_two (u : ℝ) : a 2 u = 1 := by
  unfold a
  rw [show (2 : ℕ) - 2 = 0 from rfl]
  simp

/-- `a₃(u) = E₁(u)` (eq. `a-rho`). -/
theorem a_three (u : ℝ) : a 3 u = E 1 u := by
  unfold a
  rw [show (3 : ℕ) - 2 = 1 from rfl, Finset.Icc_self, Finset.prod_singleton]

/-! ## Index-shift identities for `A` and `a` -/

/-- `A_{s+1} = A_s + D_{s+1}`: one-step unfolding of the cumulative sum
`A_j = 1 + ∑_{k=3}^j D_k` (used throughout §6). -/
theorem A_succ {s : ℕ} (hs : 2 ≤ s) (u : ℝ) : A (s + 1) u = A s u + D (s + 1) u := by
  unfold A
  rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ s + 1)]
  ring

/-- `a_{r+1} = a_r · E_{r-1}`: the chain-rule factor gains one scale per
depth (the identity `a_j = x_{j-2} a_{j-1}` of §6, shifted). -/
theorem a_succ {r : ℕ} (hr : 2 ≤ r) (u : ℝ) : a (r + 1) u = a r u * E (r - 1) u := by
  unfold a
  rw [show r + 1 - 2 = (r - 2) + 1 by omega,
    Finset.prod_Icc_succ_top (by omega : 1 ≤ (r - 2) + 1),
    show r - 2 + 1 = r - 1 by omega]

/-- `A₃(u) = 1 + u`. -/
theorem A_three_eq (u : ℝ) : A 3 u = 1 + u := by
  have h : A 3 u = A 2 u + D 3 u := A_succ (s := 2) le_rfl u
  rw [h, A_two, D_three]

/-- `A₄(u) = 1 + u + u·E₁(u)` (certificate-facing closed form). -/
theorem A_four_eq (u : ℝ) : A 4 u = 1 + u + u * E 1 u := by
  have h : A 4 u = A 3 u + D 4 u := A_succ (s := 3) (by omega) u
  rw [h, A_three_eq, D_four]

/-- `A₅(u) = 1 + u + u·E₁(u) + u·E₁(u)·E₂(u)` (the closed form of `A₅`
entering the reference core eq. `reference-core`; matches the certificate
program's `A5`). -/
theorem A_five_eq (u : ℝ) : A 5 u = 1 + u + u * E 1 u + u * E 1 u * E 2 u := by
  have h : A 5 u = A 4 u + D 5 u := A_succ (s := 4) (by omega) u
  rw [h, A_four_eq, D_five]

/-- For `u > 0`, the cumulative normalization `A_s(u)` is monotone in the
depth index `s`. -/
theorem A_mono_index {u : ℝ} (hu : 0 < u) : Monotone fun s => A s u := by
  intro s t hst
  show A s u ≤ A t u
  unfold A
  have h : ∑ j ∈ Finset.Icc 3 s, D j u ≤ ∑ j ∈ Finset.Icc 3 t, D j u :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right hst) (fun j _ _ => (D_pos hu j).le)
  linarith

/-- For `s ≥ 4` and `u ≥ 1`, `A_s ≤ 2 D_s`: the cumulative sum is dominated
by (twice) its top term.  This is the quantitative input behind the paper's
`0 ≤ R_r/J_r ≤ 3 q_r` (eq. `J-defect`). -/
theorem A_le_two_D {s : ℕ} (hs : 4 ≤ s) {u : ℝ} (hu : 1 ≤ u) : A s u ≤ 2 * D s u := by
  induction s, hs using Nat.le_induction with
  | base =>
      have hE1 : E 1 u = Real.exp u := by simpa using E_succ 0 u
      rw [A_four_eq, D_four, hE1]
      have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
      nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ u),
        mul_nonneg (by linarith : (0 : ℝ) ≤ u - 1) (by linarith : (0 : ℝ) ≤ u + 1)]
  | succ n hn ih =>
      have hA := A_succ (by omega : 2 ≤ n) u
      have hD := D_succ (by omega : 2 ≤ n) u
      have h2 : (2 : ℝ) ≤ E (n - 2) u := two_le_E (by omega) hu
      have hD0 : (0 : ℝ) < D n u := D_pos (by linarith) n
      rw [hA, hD]
      have hmul : D n u * 2 ≤ D n u * E (n - 2) u :=
        mul_le_mul_of_nonneg_left h2 hD0.le
      linarith

/-- For `r ≥ 4`, `A_r = J_r + A_{r-2}`: the top two summands of `A_r` are
exactly `J_r = D_r + D_{r-1}`.  This is "the cancellation behind the choice
`J_r = D_r + D_{r-1}`" (eq. `J-defect`); it *fails* at `r = 3`
(`A₃ = 1 + D₃` but `J₃ + A₁ = D₃ + 2`), which is why the defect identity
below carries the hypothesis `4 ≤ r`. -/
theorem A_eq_J_add {r : ℕ} (hr : 4 ≤ r) (u : ℝ) : A r u = J r u + A (r - 2) u := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  unfold A J
  rw [show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega,
    show m + 2 = m + 1 + 1 by omega,
    Finset.sum_Icc_succ_top (by omega : 3 ≤ m + 1 + 1),
    Finset.sum_Icc_succ_top (by omega : 3 ≤ m + 1)]
  ring

/-! ## The derivative identities of eq. `D-identity` -/

/-- `D_{r+1}' = a_r · A_r` for `r ≥ 2`: the first identity of
eq. `D-identity` (`𝓛_r D_{r+1} = A_r`), in `HasDerivAt` form. -/
theorem hasDerivAt_D_succ {r : ℕ} (hr : 2 ≤ r) (u : ℝ) :
    HasDerivAt (D (r + 1)) (a r u * A r u) u := by
  induction r, hr using Nat.le_induction with
  | base =>
      have hD3 : D 3 = fun v : ℝ => v := funext fun v => D_three v
      show HasDerivAt (D 3) (a 2 u * A 2 u) u
      rw [hD3, a_two, A_two, one_mul]
      exact hasDerivAt_id u
  | succ r hr ih =>
      have hDfun : D (r + 1 + 1) = fun v => D (r + 1) v * E (r - 1) v := by
        funext v
        show D (r + 1 + 1) v = D (r + 1) v * E (r - 1) v
        have h := D_succ (r := r + 1) (by omega) v
        rw [show r + 1 - 2 = r - 1 by omega] at h
        exact h
      have hmul := ih.mul (hasDerivAt_E (r - 1) u)
      have hprod : (∏ j ∈ Finset.Icc 1 (r - 1), E j u) = a (r + 1) u := by
        unfold a
        rw [show r + 1 - 2 = r - 1 by omega]
      have hval : a r u * A r u * E (r - 1) u + D (r + 1) u * a (r + 1) u
          = a (r + 1) u * A (r + 1) u := by
        rw [a_succ (by omega : 2 ≤ r) u, A_succ (by omega : 2 ≤ r) u]
        ring
      rw [hDfun, ← hval, ← hprod]
      exact hmul

/-- `A_s' = ∑_{j=3}^s a_{j-1} A_{j-1}`: term-by-term differentiation of the
cumulative normalization (each `D_j' = a_{j-1} A_{j-1}` by
eq. `D-identity`). -/
theorem hasDerivAt_A (s : ℕ) (u : ℝ) :
    HasDerivAt (A s) (∑ j ∈ Finset.Icc 3 s, a (j - 1) u * A (j - 1) u) u := by
  have hsum : HasDerivAt (fun v => ∑ j ∈ Finset.Icc 3 s, D j v)
      (∑ j ∈ Finset.Icc 3 s, a (j - 1) u * A (j - 1) u) u := by
    refine HasDerivAt.fun_sum fun j hj => ?_
    have hj3 : 3 ≤ j := (Finset.mem_Icc.mp hj).1
    have h := hasDerivAt_D_succ (r := j - 1) (by omega) u
    rw [show j - 1 + 1 = j by omega] at h
    exact h
  exact (hasDerivAt_const_add_iff (𝕜 := ℝ) (F := ℝ) (1 : ℝ)).mpr hsum

/-! ## The backward differentiation operator `𝓛_r` (eq. `L-def`) -/

/-- `Lop r f = f' / a_r`: the paper's backward differentiation operator
`𝓛_r` (eq. `L-def`), which inverts the main relation
`(H̄_{r+1})' ≈ a_r H̄_r`. -/
noncomputable def Lop (r : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := fun u => deriv f u / a r u

/-- Evaluate `𝓛_r f` at a point where a derivative of `f` is known. -/
theorem Lop_eq_of_hasDerivAt {r : ℕ} {u : ℝ} {f : ℝ → ℝ} {c : ℝ}
    (h : HasDerivAt f c u) : Lop r f u = c / a r u := by
  unfold Lop
  rw [h.deriv]

/-! ## The finite backward reference functions (eq. `finite-reference`) -/

/-- Auxiliary recursion for `Qref`: `QrefAux k R` applies the last `k`
backward operators `𝓛_{R-k} ⋯ 𝓛_{R-1}` to `J_R`. -/
noncomputable def QrefAux : ℕ → ℕ → (ℝ → ℝ)
  | 0, R => J R
  | k + 1, R => Lop (R - (k + 1)) (QrefAux k R)

theorem QrefAux_zero (R : ℕ) : QrefAux 0 R = J R := rfl

theorem QrefAux_succ (k R : ℕ) :
    QrefAux (k + 1) R = Lop (R - (k + 1)) (QrefAux k R) := rfl

/-- `Qref s R = Q_s^{[R]} = 𝓛_s 𝓛_{s+1} ⋯ 𝓛_{R-1} J_R`
(eq. `finite-reference`): the profile at depth `s` forced by principal term
`J_R` at terminal depth `R`.  For `s ≥ R` this degenerates to `J R`
(matching the paper's convention `Q_R^{[R]} = J_R`). -/
noncomputable def Qref (s R : ℕ) : ℝ → ℝ := QrefAux (R - s) R

/-- `Q_R^{[R]} = J_R` (the paper's convention when no operator is
applied). -/
theorem Qref_self (R : ℕ) : Qref R R = J R := by
  unfold Qref
  rw [Nat.sub_self, QrefAux_zero]

/-- One-step unfolding `Q_s^{[R]} = 𝓛_s Q_{s+1}^{[R]}` for `s < R`
(equivalently the paper's `(Q_{s+1}^{[R]})' = a_s Q_s^{[R]}`
read backwards). -/
theorem Qref_of_lt {s R : ℕ} (h : s < R) : Qref s R = Lop s (Qref (s + 1) R) := by
  unfold Qref
  rw [show R - s = (R - (s + 1)) + 1 by omega, QrefAux_succ,
    show R - ((R - (s + 1)) + 1) = s by omega]

/-! ## The defect identity `J_{r+1}' = a_r (J_r + R_r)` (eq. `J-defect`) -/

/-- `Rdefect r u = R_r(u) = A_{r-2}(u) + A_{r-1}(u)/E_{r-2}(u)`: the defect
left by `J_r` under backward differentiation (eq. `J-defect`). -/
noncomputable def Rdefect (r : ℕ) (u : ℝ) : ℝ := A (r - 2) u + A (r - 1) u / E (r - 2) u

/-- `J_{r+1}' = a_r (J_r + R_r)` for `r ≥ 4` (eq. `J-defect`).  The paper
states this for "sufficiently large `r`" (its proof takes `r ≥ 5`); the
identity genuinely fails at `r = 3` (see `A_eq_J_add`). -/
theorem hasDerivAt_J_succ {r : ℕ} (hr : 4 ≤ r) (u : ℝ) :
    HasDerivAt (J (r + 1)) (a r u * (J r u + Rdefect r u)) u := by
  have hd1 : HasDerivAt (D (r + 1)) (a r u * A r u) u := hasDerivAt_D_succ (by omega) u
  have hd2 : HasDerivAt (D r) (a (r - 1) u * A (r - 1) u) u := by
    have h := hasDerivAt_D_succ (r := r - 1) (by omega) u
    rw [show r - 1 + 1 = r by omega] at h
    exact h
  have hfun : J (r + 1) = fun v => D (r + 1) v + D r v := by
    funext v
    show J (r + 1) v = D (r + 1) v + D r v
    unfold J
    rw [show r + 1 - 1 = r by omega]
  have hval : a r u * (J r u + Rdefect r u)
      = a r u * A r u + a (r - 1) u * A (r - 1) u := by
    have hA : A r u = J r u + A (r - 2) u := A_eq_J_add hr u
    have ha : a r u = a (r - 1) u * E (r - 2) u := by
      have h := a_succ (r := r - 1) (by omega) u
      rw [show r - 1 + 1 = r by omega, show r - 1 - 1 = r - 2 by omega] at h
      exact h
    have hE : E (r - 2) u ≠ 0 := (E_pos_of_one_le (by omega) u).ne'
    unfold Rdefect
    rw [hA, ha]
    field_simp
    ring
  rw [hfun, hval]
  exact hd1.add hd2

/-- The defect is nonnegative on positive arguments (first half of
eq. `J-defect`'s `0 ≤ R_r/J_r ≤ 3q_r`). -/
theorem Rdefect_nonneg {u : ℝ} (hu : 0 < u) (r : ℕ) : 0 ≤ Rdefect r u := by
  unfold Rdefect
  exact add_nonneg (A_pos hu _).le
    (div_nonneg (A_pos hu _).le (E_pos_of_pos hu _).le)

/-- `R_r ≤ 3 q_r J_r` for `r ≥ 6` and `u ≥ 1` (second half of
eq. `J-defect`'s ratio bound; the paper's "for all sufficiently large `r`"
made explicit). -/
theorem Rdefect_le_three_q_mul_J {r : ℕ} (hr : 6 ≤ r) {u : ℝ} (hu : 1 ≤ u) :
    Rdefect r u ≤ 3 * q r u * J r u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hA2 : A (r - 2) u ≤ 2 * D (r - 2) u := A_le_two_D (by omega) hu
  have hA1 : A (r - 1) u ≤ 2 * D (r - 1) u := A_le_two_D (by omega) hu
  have hDrm1 : D (r - 1) u = D (r - 2) u * E (r - 4) u := by
    have h := D_succ (r := r - 2) (by omega) u
    rw [show r - 2 + 1 = r - 1 by omega, show r - 2 - 2 = r - 4 by omega] at h
    exact h
  have hEE : 2 * E (r - 4) u ≤ E (r - 2) u := by
    have h2 : E (r - 4) u ≤ E (r - 3) u := by
      have h := E_lt_E_succ (r - 4) u
      rw [show r - 4 + 1 = r - 3 by omega] at h
      exact h.le
    have h3 : E (r - 2) u = Real.exp (E (r - 3) u) := by
      rw [show r - 2 = (r - 3) + 1 by omega, E_succ]
    rw [h3]
    calc 2 * E (r - 4) u ≤ Real.exp (E (r - 4) u) :=
          two_mul_le_exp (E_pos_of_pos hu0 _).le
      _ ≤ Real.exp (E (r - 3) u) := Real.exp_le_exp.mpr h2
  have hEpos : (0 : ℝ) < E (r - 2) u := E_pos_of_one_le (by omega) u
  have hD2pos : (0 : ℝ) < D (r - 2) u := D_pos hu0 (r - 2)
  have hmid : A (r - 1) u / E (r - 2) u ≤ D (r - 2) u := by
    rw [div_le_iff₀ hEpos]
    have hint := mul_le_mul_of_nonneg_left hEE hD2pos.le
    linarith
  have hqD : q r u * D r u = D (r - 2) u := by
    rw [q_eq_D_ratio hu0 (by omega), div_mul_cancel₀ _ (D_pos hu0 r).ne']
  have hqpos : (0 : ℝ) < q r u := by
    unfold q
    exact one_div_pos.mpr (mul_pos (E_pos_of_pos hu0 _) (E_pos_of_pos hu0 _))
  have hDJ : D r u ≤ J r u := by
    unfold J
    linarith [D_pos hu0 (r - 1)]
  have hq3 : 3 * D (r - 2) u ≤ 3 * q r u * J r u := by
    have h := mul_le_mul_of_nonneg_left hDJ hqpos.le
    calc 3 * D (r - 2) u = 3 * (q r u * D r u) := by rw [hqD]
      _ ≤ 3 * (q r u * J r u) := by linarith
      _ = 3 * q r u * J r u := by ring
  unfold Rdefect
  linarith

/-! ## The `B_j` machinery (eq. `Bj-recursion`, eq. `Bj-derivative-bound`
and its auxiliary value estimate) -/

/-- `Bref j u = B_j(u) = A_j'(u) / a_j(u)`: the normalized derivative of
the cumulative sum (§6, proof of `lem:backward-reference-convergence`). -/
noncomputable def Bref (j : ℕ) : ℝ → ℝ := fun u => deriv (A j) u / a j u

/-- `a_j · B_j = A_j'` (the defining relation of `B_j`, cleared of the
division; `a_j ≠ 0` always). -/
theorem a_mul_Bref (j : ℕ) (u : ℝ) : a j u * Bref j u = deriv (A j) u := by
  unfold Bref
  rw [mul_comm, div_mul_cancel₀ _ (a_pos j u).ne']

/-- `A_j' = a_j B_j` in `HasDerivAt` form. -/
theorem hasDerivAt_A_Bref (j : ℕ) (u : ℝ) :
    HasDerivAt (A j) (a j u * Bref j u) u := by
  rw [a_mul_Bref, (hasDerivAt_A j u).deriv]
  exact hasDerivAt_A j u

/-- `B_j = (A_{j-1} + B_{j-1}) / E_{j-2}` for `j ≥ 3`
(eq. `Bj-recursion`; from `A_j = A_{j-1} + D_j`, `𝓛_{j-1} D_j = A_{j-1}`,
and `a_j = E_{j-2} a_{j-1}`). -/
theorem Bref_recursion {j : ℕ} (hj : 3 ≤ j) (u : ℝ) :
    Bref j u = (A (j - 1) u + Bref (j - 1) u) / E (j - 2) u := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  rw [show m + 1 - 1 = m by omega, show m + 1 - 2 = m - 1 by omega]
  have hsum : deriv (A (m + 1)) u = deriv (A m) u + a m u * A m u := by
    rw [(hasDerivAt_A (m + 1) u).deriv, (hasDerivAt_A m u).deriv,
      Finset.sum_Icc_succ_top (by omega : 3 ≤ m + 1), show m + 1 - 1 = m by omega]
  unfold Bref
  rw [hsum, a_succ hm]
  have ha : a m u ≠ 0 := (a_pos m u).ne'
  have hE : E (m - 1) u ≠ 0 := (E_pos_of_one_le (by omega) u).ne'
  field_simp
  ring

/-- `0 ≤ B_j` on positive arguments (the `0 ≤ B_j` half of the unlabeled
auxiliary value estimate before eq. `Bj-derivative-bound`; in fact it needs
no upper restriction on `u`). -/
theorem Bref_nonneg {u : ℝ} (hu : 0 < u) (j : ℕ) : 0 ≤ Bref j u := by
  unfold Bref
  apply div_nonneg _ (a_pos j u).le
  rw [(hasDerivAt_A j u).deriv]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (a_pos _ u).le (A_pos hu _).le

/-- `B_j ≤ A_{j-1}` for `j ≥ 3`, `u ≥ 1`: the induction engine behind
the auxiliary value estimate ("A direct check at `j = 4` and induction
first give the auxiliary estimate", before eq. `Bj-derivative-bound`; here
the direct check already succeeds at `j = 3`). -/
theorem Bref_le_A_pred {j : ℕ} (hj : 3 ≤ j) {u : ℝ} (hu : 1 ≤ u) :
    Bref j u ≤ A (j - 1) u := by
  induction j, hj using Nat.le_induction with
  | base =>
      have hd : deriv (A 3) u = 1 := by
        rw [(hasDerivAt_A 3 u).deriv, Finset.Icc_self, Finset.sum_singleton,
          show (3 : ℕ) - 1 = 2 from rfl, a_two, A_two, mul_one]
      show Bref 3 u ≤ A 2 u
      unfold Bref
      rw [hd, a_three, A_two]
      have h1 : (1 : ℝ) ≤ E 1 u := one_le_E_of_one_le hu 1
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < E 1 u), one_mul]
      exact h1
  | succ j hj ih =>
      have hu0 : (0 : ℝ) < u := by linarith
      have hrec := Bref_recursion (j := j + 1) (by omega) u
      rw [show j + 1 - 1 = j by omega, show j + 1 - 2 = j - 1 by omega] at hrec
      rw [show j + 1 - 1 = j by omega, hrec]
      have h2 : (2 : ℝ) ≤ E (j - 1) u := two_le_E (by omega) hu
      have hA0 : (0 : ℝ) < A j u := A_pos hu0 j
      have hAmono : A (j - 1) u ≤ A j u := A_mono_index hu0 (by omega : j - 1 ≤ j)
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < E (j - 1) u)]
      have hmul : A j u * 2 ≤ A j u * E (j - 1) u :=
        mul_le_mul_of_nonneg_left h2 hA0.le
      linarith

/-! ## The reference core `Q̃₄`, `Q̃₃` (eq. `reference-core`) -/

/-- `Q̃₄ = 𝓛₄ (A₅ + A₅'/a₅) = 𝓛₄ (A₅ + B₅)` (eq. `reference-core`): the
finite, explicitly computable core of the limiting reference function at
depth 4.  Closed forms for the ingredients: `A_five_eq`, `D_three`–`D_five`,
`a_mul_Bref`. -/
noncomputable def QrefCore4 : ℝ → ℝ := Lop 4 (fun u => A 5 u + Bref 5 u)

/-- `Q̃₃ = 𝓛₃ Q̃₄` (eq. `reference-core`). -/
noncomputable def QrefCore3 : ℝ → ℝ := Lop 3 QrefCore4

/-! ## The two exact terminal identities

Proof of `lem:backward-reference-convergence`: "The first two terminal
depths satisfy the exact identities `Q_s^{[s+1]} = A_s + b_s` and
`Q_s^{[s+2]} = A_s + B_s − (A_s − B_s)/x_{s-1}`", with `b_s = A_{s-1}/x_{s-2}`
and `x_j = E_j(u)`.  Both hold for every real `u` (all denominators are the
always-positive `a_r`, `E_j` with `j ≥ 1`). -/

/-- `Q_s^{[s+1]} = A_s + A_{s-1}/E_{s-2}` for `s ≥ 4` (first exact terminal
identity, i.e. `𝓛_s J_{s+1} = A_s + b_s`). -/
theorem Qref_succ_eq {s : ℕ} (hs : 4 ≤ s) (u : ℝ) :
    Qref s (s + 1) u = A s u + A (s - 1) u / E (s - 2) u := by
  have h1 : Qref s (s + 1) = Lop s (Qref (s + 1) (s + 1)) := Qref_of_lt (by omega)
  rw [h1, Qref_self, Lop_eq_of_hasDerivAt (hasDerivAt_J_succ hs u),
    mul_div_cancel_left₀ _ (a_pos s u).ne']
  unfold Rdefect
  rw [A_eq_J_add hs u]
  ring

/-- `Q_s^{[s+2]} = A_s + B_s − (A_s − B_s)/E_{s-1}` for `s ≥ 3` (second
exact terminal identity; the paper uses it from `s = 4` up). -/
theorem Qref_succ_succ_eq {s : ℕ} (hs : 3 ≤ s) (u : ℝ) :
    Qref s (s + 2) u = A s u + Bref s u - (A s u - Bref s u) / E (s - 1) u := by
  have hg : Qref (s + 1) (s + 2) = A (s + 1) + A s / E (s - 1) := by
    funext v
    show Qref (s + 1) (s + 2) v = A (s + 1) v + A s v / E (s - 1) v
    have h := Qref_succ_eq (s := s + 1) (by omega) v
    rw [show s + 1 + 1 = s + 2 by omega, show s + 1 - 1 = s by omega,
      show s + 1 - 2 = s - 1 by omega] at h
    exact h
  have hXpos : (0 : ℝ) < E (s - 1) u := E_pos_of_one_le (by omega) u
  have hE : HasDerivAt (E (s - 1)) (a (s + 1) u) u := by
    have h := hasDerivAt_E_sub_two (s + 1) u
    rw [show s + 1 - 2 = s - 1 by omega] at h
    exact h
  have hA1 : HasDerivAt (A (s + 1)) (a (s + 1) u * Bref (s + 1) u) u :=
    hasDerivAt_A_Bref (s + 1) u
  have hA0 : HasDerivAt (A s) (a s u * Bref s u) u := hasDerivAt_A_Bref s u
  have hsum := hA1.add (hA0.div hE hXpos.ne')
  have hBrec : Bref (s + 1) u = (A s u + Bref s u) / E (s - 1) u := by
    have h := Bref_recursion (j := s + 1) (by omega) u
    rw [show s + 1 - 1 = s by omega, show s + 1 - 2 = s - 1 by omega] at h
    exact h
  have haE : a (s + 1) u = a s u * E (s - 1) u := a_succ (by omega : 2 ≤ s) u
  rw [Qref_of_lt (by omega : s < s + 2), hg, Lop_eq_of_hasDerivAt hsum, hBrec, haE]
  have ha : a s u ≠ 0 := (a_pos s u).ne'
  have hX : E (s - 1) u ≠ 0 := hXpos.ne'
  field_simp
  ring

end Erdos320
