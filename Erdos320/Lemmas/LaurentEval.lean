import Erdos320.Lemmas.BackwardReference
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Laurent-monomial bookkeeping for the backward operators (§6, eq. `laurent-derivative`)

The convergence proof of `lem:backward-reference-convergence` tracks every
function through the variables `x_j = E_j(u)`: each object in sight is an
integer combination of Laurent monomials `x^ν = ∏_j x_j^{ν_j}` (finitely many
`j`, integer exponents), and both `d/du` and the backward operators `𝓛_r` act
combinatorially on exponent vectors:
```
(x^ν)' = ν₀ x^{ν−e₀} + ∑_{j≥1} ν_j x^{ν+e₁+⋯+e_{j−1}},   𝓛_r x^ν = (x^ν)'/(x₁⋯x_{r−2})
```
(eq. `laurent-derivative`; the `j`-th summand arises from `x_j' = x₁⋯x_j`,
so `x_j^{-1}·x_j' = x₁⋯x_{j−1}`).

This file provides the *infrastructure* for that bookkeeping — the paper's
all-depth induction itself is built on top of it elsewhere:

* `ExpVec` / `LaurentComb` — formal exponent vectors (`ℕ →₀ ℤ`) and formal
  ℤ-combinations of monomials (`ExpVec →₀ ℤ`), with evaluation maps
  `evalMon`, `evalComb` into `ℝ → ℝ` (`x_j := E j u`).
* `derivMon` / `derivComb` — the formal derivative implementing
  eq. `laurent-derivative`, with the analytic bridge `hasDerivAt_evalComb`.
* `shiftComb` — division by a monomial as an exponent shift, giving the
  backward-operator bridge `Lop_evalComb`:
  `𝓛_r (evalComb P) = evalComb (shiftComb (aVec r) (derivComb P))`.
* `DComb`, `JComb`, `AComb`, `RdefectComb` — the starter combinations whose
  evaluations are the paper's `D_r`, `J_R`, `A_s`, `R_R` (eq. `D-J`,
  eq. `reference-defect`).
* Size functionals `l1Norm` (coefficient ℓ¹-norm `‖·‖₁`), `height` /
  `combHeight` (exponent height `ht`), `posDeg` / `combPosDeg` (positive
  degree `d₊`), `maxIdx` (largest occurring variable index), with the
  evaluation estimates `abs_evalComb_le` / `abs_evalComb_le_div` and the
  operation bookkeeping (`l1Norm_derivComb_le`, `combHeight_derivComb_le`,
  `l1Norm_shiftComb`, `combHeight_shiftComb_le`, `maxIdx_derivComb_le`,
  `maxIdx_shiftComb_le`) matching the paper's "differentiation multiplies the
  coefficient ℓ¹-norm by at most the old height, whereas the division shift
  leaves coefficients unchanged".
* The persistence lemmas `derivComb_apply_le_neg_one` /
  `shiftComb_apply_le_neg_one`: a terminal inverse factor `x_t^{-1}` survives
  differentiation and shifts as long as no variable of index above `t`
  occurs — the paper's "these terminal inverse factors persist under every
  later operator".

All evaluation identities that involve negative exponents of `x₀ = u` carry
the hypothesis `0 < u`; the consumers work on `u ∈ [1, e]`, so this is free.

Paper vs. Lean: the paper's height bookkeeping — "one differentiation raises
the height by at most the largest variable index plus one, hence by at most
`R` here; this includes the possible `x₀` term" — is
`combHeight_derivComb_le`:
`combHeight (derivComb P) ≤ combHeight P + maxIdx P + 1`, whose `+1` is that
`x₀`-term `ν₀ x^{ν−e₀}` (it can *raise* the height by `1` when `ν₀ < 0`);
with `maxIdx P + 1 ≤ R` this gives the paper's `+R`.
-/

namespace Erdos320

/-! ## Exponent vectors, combinations, and their evaluation -/

/-- Exponent vectors: finitely supported ℤ-valued exponents on the variables
`x_j = E_j(u)` of eq. `laurent-derivative`.  Coordinate `0` is the phase
variable `x₀ = u` itself. -/
abbrev ExpVec : Type := ℕ →₀ ℤ

/-- Formal ℤ-linear combinations of Laurent monomials in the `x_j`
(a "Laurent polynomial" in the paper's terminology, with integer exponents
allowed). -/
abbrev LaurentComb : Type := ExpVec →₀ ℤ

/-- Evaluation of the Laurent monomial `x^ν = ∏_j E_j(u)^{ν_j}` at phase `u`.
The product ranges over the (finite) support of `ν`; factors with exponent `0`
are `1`, so any superset of the support gives the same value
(`evalMon_eq_prod_superset`). -/
noncomputable def evalMon (ν : ExpVec) (u : ℝ) : ℝ :=
  ∏ j ∈ ν.support, E j u ^ ν j

/-- Evaluation of a formal combination: `evalComb P u = ∑_ν P(ν)·x^ν`. -/
noncomputable def evalComb (P : LaurentComb) (u : ℝ) : ℝ :=
  ∑ ν ∈ P.support, (P ν : ℝ) * evalMon ν u

/-- The support product defining `evalMon` may be extended over any superset:
the extra factors are `E j u ^ (0 : ℤ) = 1`. -/
theorem evalMon_eq_prod_superset {ν : ExpVec} {s : Finset ℕ}
    (hs : ν.support ⊆ s) (u : ℝ) :
    evalMon ν u = ∏ j ∈ s, E j u ^ ν j :=
  Finset.prod_subset hs fun j _ hj => by
    rw [Finsupp.notMem_support_iff.mp hj, zpow_zero]

/-- The empty monomial evaluates to `1`. -/
@[simp] theorem evalMon_zero_vec (u : ℝ) : evalMon (0 : ExpVec) u = 1 := by
  simp [evalMon]

/-- Monomials evaluate positively on positive phase. -/
theorem evalMon_pos {u : ℝ} (hu : 0 < u) (ν : ExpVec) : 0 < evalMon ν u :=
  Finset.prod_pos fun j _ => zpow_pos (E_pos_of_pos hu j) _

/-- Multiplicativity of monomial evaluation: adding exponent vectors
multiplies the values.  Positivity of `u` keeps the `zpow` arithmetic honest
at the variable `x₀ = u`. -/
theorem evalMon_add {u : ℝ} (hu : 0 < u) (ν μ : ExpVec) :
    evalMon (ν + μ) u = evalMon ν u * evalMon μ u := by
  rw [evalMon_eq_prod_superset
      (Finsupp.support_add : (ν + μ).support ⊆ ν.support ∪ μ.support) u,
    evalMon_eq_prod_superset
      (Finset.subset_union_left : ν.support ⊆ ν.support ∪ μ.support) u,
    evalMon_eq_prod_superset
      (Finset.subset_union_right : μ.support ⊆ ν.support ∪ μ.support) u,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finsupp.add_apply, zpow_add₀ (E_pos_of_pos hu j).ne']

/-- Negating an exponent vector inverts the monomial value (no positivity
needed: `zpow_neg` holds in the group-with-zero `ℝ`). -/
theorem evalMon_neg (ν : ExpVec) (u : ℝ) :
    evalMon (-ν) u = (evalMon ν u)⁻¹ := by
  unfold evalMon
  rw [Finsupp.support_neg]
  simp only [Finsupp.neg_apply, zpow_neg]
  exact Finset.prod_inv_distrib fun j => E j u ^ ν j

/-- Subtracting exponent vectors divides the monomial values. -/
theorem evalMon_sub {u : ℝ} (hu : 0 < u) (ν μ : ExpVec) :
    evalMon (ν - μ) u = evalMon ν u / evalMon μ u := by
  rw [sub_eq_add_neg, evalMon_add hu, evalMon_neg, div_eq_mul_inv]

/-- A single-variable monomial evaluates to the corresponding power. -/
theorem evalMon_single (j : ℕ) (n : ℤ) (u : ℝ) :
    evalMon (Finsupp.single j n) u = E j u ^ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [evalMon]
  · unfold evalMon
    rw [Finsupp.support_single j hn, Finset.prod_singleton,
      Finsupp.single_eq_same]

/-! ## Evaluation of combinations: linearity -/

/-- The support sum defining `evalComb` may be extended over any superset:
the extra terms have coefficient `0`. -/
theorem evalComb_eq_sum_superset {P : LaurentComb} {s : Finset ExpVec}
    (hs : P.support ⊆ s) (u : ℝ) :
    evalComb P u = ∑ ν ∈ s, (P ν : ℝ) * evalMon ν u :=
  Finset.sum_subset hs fun ν _ hν => by
    rw [Finsupp.notMem_support_iff.mp hν, Int.cast_zero, zero_mul]

@[simp] theorem evalComb_zero (u : ℝ) : evalComb (0 : LaurentComb) u = 0 := by
  simp [evalComb]

theorem evalComb_add (P Q : LaurentComb) (u : ℝ) :
    evalComb (P + Q) u = evalComb P u + evalComb Q u := by
  rw [evalComb_eq_sum_superset
      (Finsupp.support_add : (P + Q).support ⊆ P.support ∪ Q.support) u,
    evalComb_eq_sum_superset
      (Finset.subset_union_left : P.support ⊆ P.support ∪ Q.support) u,
    evalComb_eq_sum_superset
      (Finset.subset_union_right : Q.support ⊆ P.support ∪ Q.support) u,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finsupp.add_apply, Int.cast_add, add_mul]

theorem evalComb_smul (c : ℤ) (P : LaurentComb) (u : ℝ) :
    evalComb (c • P) u = (c : ℝ) * evalComb P u := by
  rw [evalComb_eq_sum_superset
    (Finsupp.support_smul : (c • P).support ⊆ P.support) u]
  unfold evalComb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, Int.cast_mul, mul_assoc]

theorem evalComb_single (ν : ExpVec) (c : ℤ) (u : ℝ) :
    evalComb (Finsupp.single ν c) u = (c : ℝ) * evalMon ν u := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [evalComb]
  · unfold evalComb
    rw [Finsupp.support_single ν hc, Finset.sum_singleton,
      Finsupp.single_eq_same]

theorem evalComb_finsetSum {ι : Type*} (s : Finset ι) (f : ι → LaurentComb)
    (u : ℝ) :
    evalComb (∑ i ∈ s, f i) u = ∑ i ∈ s, evalComb (f i) u := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s _his ih => rw [Finset.sum_cons, Finset.sum_cons, evalComb_add, ih]

/-! ## Structured exponent vectors: stairs, ranges, and `aVec` -/

/-- `stairVec k = e₁ + ⋯ + e_k`: the exponent vector of the "stair" monomial
`x₁⋯x_k` that eq. `laurent-derivative` adds when differentiating `x_{k+1}`. -/
noncomputable def stairVec (k : ℕ) : ExpVec :=
  ∑ i ∈ Finset.Icc 1 k, Finsupp.single i 1

theorem stairVec_apply (k j : ℕ) :
    stairVec k j = if j ∈ Finset.Icc 1 k then 1 else 0 := by
  unfold stairVec
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  exact Finset.sum_ite_eq' (Finset.Icc 1 k) j fun _ => (1 : ℤ)

theorem stairVec_support_subset (k : ℕ) :
    (stairVec k).support ⊆ Finset.Icc 1 k := by
  intro j hj
  by_contra hjk
  have h := Finsupp.mem_support_iff.mp hj
  rw [stairVec_apply, if_neg hjk] at h
  exact h rfl

theorem evalMon_stairVec (k : ℕ) (u : ℝ) :
    evalMon (stairVec k) u = ∏ i ∈ Finset.Icc 1 k, E i u := by
  rw [evalMon_eq_prod_superset (stairVec_support_subset k)]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [stairVec_apply, if_pos hj, zpow_one]

/-- `rangeVec k = e₀ + e₁ + ⋯ + e_{k−1}`: the exponent vector of the
principal monomial `x₀x₁⋯x_{k−1}`, so that `D_r = x^{rangeVec (r−2)}`
(eq. `D-J`). -/
noncomputable def rangeVec (k : ℕ) : ExpVec :=
  ∑ i ∈ Finset.range k, Finsupp.single i 1

theorem rangeVec_apply (k j : ℕ) :
    rangeVec k j = if j ∈ Finset.range k then 1 else 0 := by
  unfold rangeVec
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  exact Finset.sum_ite_eq' (Finset.range k) j fun _ => (1 : ℤ)

theorem rangeVec_support_subset (k : ℕ) :
    (rangeVec k).support ⊆ Finset.range k := by
  intro j hj
  by_contra hjk
  have h := Finsupp.mem_support_iff.mp hj
  rw [rangeVec_apply, if_neg hjk] at h
  exact h rfl

theorem evalMon_rangeVec (k : ℕ) (u : ℝ) :
    evalMon (rangeVec k) u = ∏ j ∈ Finset.range k, E j u := by
  rw [evalMon_eq_prod_superset (rangeVec_support_subset k)]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [rangeVec_apply, if_pos hj, zpow_one]

/-- `D_r` is the evaluation of the range monomial (eq. `D-J`). -/
theorem evalMon_rangeVec_eq_D (r : ℕ) (u : ℝ) :
    evalMon (rangeVec (r - 2)) u = D r u :=
  evalMon_rangeVec (r - 2) u

/-- `aVec r = e₁ + ⋯ + e_{r−2}`: the exponent vector of the denominator
monomial `x₁⋯x_{r−2} = a_r` of the backward operator `𝓛_r` (eq. `L-def`). -/
noncomputable def aVec (r : ℕ) : ExpVec := stairVec (r - 2)

/-- The `aVec` monomial evaluates to the paper's `a_r` (eq. `a-rho`). -/
theorem evalMon_aVec (r : ℕ) (u : ℝ) : evalMon (aVec r) u = a r u := by
  unfold aVec
  exact evalMon_stairVec (r - 2) u

/-- All coordinates of `aVec` are nonnegative (input for
`shiftComb_apply_le_neg_one` at `μ = aVec r`). -/
theorem aVec_apply_nonneg (r t : ℕ) : 0 ≤ aVec r t := by
  unfold aVec
  rw [stairVec_apply]
  split <;> omega

/-! ## The formal derivative (eq. `laurent-derivative`) -/

/-- `derivShift j`: the exponent shift produced by differentiating the
variable `x_j` inside a monomial — `−e₀` for the phase variable `x₀ = u`,
and the stair `e₁ + ⋯ + e_{j−1}` for `j ≥ 1` (from
`x_j'/x_j = x₁⋯x_{j−1}`, eq. `laurent-derivative`). -/
noncomputable def derivShift : ℕ → ExpVec
  | 0 => -Finsupp.single 0 1
  | j + 1 => stairVec j

/-- `derivMon ν`: the formal derivative of the monomial `x^ν`, i.e.
`ν₀ x^{ν−e₀} + ∑_{j≥1} ν_j x^{ν+e₁+⋯+e_{j−1}}` (eq. `laurent-derivative`). -/
noncomputable def derivMon (ν : ExpVec) : LaurentComb :=
  ∑ j ∈ ν.support, Finsupp.single (ν + derivShift j) (ν j)

/-- `derivComb P`: the formal derivative of a combination, extended
ℤ-linearly from `derivMon`. -/
noncomputable def derivComb (P : LaurentComb) : LaurentComb :=
  ∑ ν ∈ P.support, P ν • derivMon ν

/-- The evaluation of a `derivShift`-ed monomial: uniformly in `j`,
`x^{ν + derivShift j} = x^ν · (x₁⋯x_j) / x_j` (empty product and `x₀ = u`
for `j = 0`). -/
theorem evalMon_add_derivShift {u : ℝ} (hu : 0 < u) (ν : ExpVec) (j : ℕ) :
    evalMon (ν + derivShift j) u
      = evalMon ν u * (∏ i ∈ Finset.Icc 1 j, E i u) / E j u := by
  cases j with
  | zero =>
      show evalMon (ν + -Finsupp.single 0 1) u = _
      rw [evalMon_add hu, evalMon_neg, evalMon_single, zpow_one, E_zero,
        Finset.Icc_eq_empty (by omega : ¬(1 : ℕ) ≤ 0), Finset.prod_empty,
        mul_one, div_eq_mul_inv]
  | succ k =>
      show evalMon (ν + stairVec k) u = _
      rw [evalMon_add hu, evalMon_stairVec,
        Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1), ← mul_assoc,
        mul_div_cancel_right₀ _ (E_pos_of_one_le (by omega) u).ne']

/-- **Bridge 1 (monomials).**  The analytic derivative of `evalMon ν` is the
evaluation of the formal derivative `derivMon ν`
(eq. `laurent-derivative`). -/
theorem hasDerivAt_evalMon {u : ℝ} (hu : 0 < u) (ν : ExpVec) :
    HasDerivAt (evalMon ν) (evalComb (derivMon ν) u) u := by
  have hfac : ∀ j ∈ ν.support, HasDerivAt (fun v => E j v ^ ν j)
      ((ν j : ℝ) * E j u ^ (ν j - 1) * ∏ i ∈ Finset.Icc 1 j, E i u) u :=
    fun j _ =>
      (hasDerivAt_zpow (ν j) (E j u) (Or.inl (E_pos_of_pos hu j).ne')).comp u
        (hasDerivAt_E j u)
  have hterm : ∀ j ∈ ν.support,
      (∏ i ∈ ν.support.erase j, E i u ^ ν i)
          • ((ν j : ℝ) * E j u ^ (ν j - 1) * ∏ i ∈ Finset.Icc 1 j, E i u)
        = (ν j : ℝ) * evalMon (ν + derivShift j) u := by
    intro j hj
    rw [smul_eq_mul, evalMon_add_derivShift hu ν j,
      show evalMon ν u = (∏ i ∈ ν.support.erase j, E i u ^ ν i) * E j u ^ ν j
        from (Finset.prod_erase_mul _ _ hj).symm,
      zpow_sub_one₀ (E_pos_of_pos hu j).ne', div_eq_mul_inv]
    ring
  have hsum : evalComb (derivMon ν) u
      = ∑ j ∈ ν.support, (ν j : ℝ) * evalMon (ν + derivShift j) u := by
    unfold derivMon
    rw [evalComb_finsetSum]
    exact Finset.sum_congr rfl fun j _ => evalComb_single _ _ u
  have hval : (∑ j ∈ ν.support, (∏ i ∈ ν.support.erase j, E i u ^ ν i)
          • ((ν j : ℝ) * E j u ^ (ν j - 1) * ∏ i ∈ Finset.Icc 1 j, E i u))
      = evalComb (derivMon ν) u := by
    rw [hsum]
    exact Finset.sum_congr rfl hterm
  have hfun : evalMon ν = fun v => ∏ j ∈ ν.support, E j v ^ ν j := rfl
  rw [hfun, ← hval]
  exact HasDerivAt.fun_finsetProd hfac

/-- **Bridge 1 (combinations).**  The analytic derivative of `evalComb P` is
the evaluation of the formal derivative `derivComb P`. -/
theorem hasDerivAt_evalComb {u : ℝ} (hu : 0 < u) (P : LaurentComb) :
    HasDerivAt (evalComb P) (evalComb (derivComb P) u) u := by
  have hterms : ∀ ν ∈ P.support, HasDerivAt (fun v => (P ν : ℝ) * evalMon ν v)
      ((P ν : ℝ) * evalComb (derivMon ν) u) u :=
    fun ν _ => (hasDerivAt_evalMon hu ν).const_mul _
  have hval : (∑ ν ∈ P.support, (P ν : ℝ) * evalComb (derivMon ν) u)
      = evalComb (derivComb P) u := by
    unfold derivComb
    rw [evalComb_finsetSum]
    exact Finset.sum_congr rfl fun ν _ => (evalComb_smul _ _ u).symm
  have hfun : evalComb P = fun v => ∑ ν ∈ P.support, (P ν : ℝ) * evalMon ν v :=
    rfl
  rw [hfun, ← hval]
  exact HasDerivAt.fun_sum hterms

/-! ## Division by a monomial: the exponent shift -/

/-- Subtracting a fixed exponent vector is injective (used to control the
support of `shiftComb`). -/
theorem sub_const_injective (μ : ExpVec) :
    Function.Injective fun ν : ExpVec => ν - μ := fun ν₁ ν₂ h => by
  have h' := congrArg (· + μ) h
  simpa using h'

/-- `shiftComb μ P`: division of the combination `P` by the monomial `x^μ`,
implemented as the exponent shift `ν ↦ ν − μ` (eq. `laurent-derivative`,
right half: the division in `𝓛_r` "is" a monomial shift). -/
noncomputable def shiftComb (μ : ExpVec) (P : LaurentComb) : LaurentComb :=
  Finsupp.mapDomain (fun ν => ν - μ) P

/-- Evaluation of a shifted combination: division by the monomial value. -/
theorem evalComb_shiftComb {u : ℝ} (hu : 0 < u) (μ : ExpVec)
    (P : LaurentComb) :
    evalComb (shiftComb μ P) u = evalComb P u / evalMon μ u := by
  unfold evalComb shiftComb
  rw [Finsupp.mapDomain_support_of_injective (sub_const_injective μ) P,
    Finset.sum_image fun ν₁ _ ν₂ _ h => sub_const_injective μ h,
    div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [Finsupp.mapDomain_apply (sub_const_injective μ)]
  rw [evalMon_sub hu, div_eq_mul_inv]
  ring

/-- **Bridge 2.**  The backward operator `𝓛_r` (eq. `L-def`) acts on
evaluated combinations as formal differentiation followed by the `aVec r`
exponent shift: `𝓛_r x^ν = (x^ν)'/(x₁⋯x_{r−2})` (eq. `laurent-derivative`). -/
theorem Lop_evalComb (r : ℕ) (P : LaurentComb) {u : ℝ} (hu : 0 < u) :
    Lop r (evalComb P) u
      = evalComb (shiftComb (aVec r) (derivComb P)) u := by
  rw [Lop_eq_of_hasDerivAt (hasDerivAt_evalComb hu P),
    evalComb_shiftComb hu, evalMon_aVec]

/-! ## Starter combinations: `D_r`, `J_R`, `A_s`, `R_R` as formal objects -/

/-- `DComb r`: the principal normalization `D_r = x₀x₁⋯x_{r−3}` as a formal
combination (eq. `D-J`). -/
noncomputable def DComb (r : ℕ) : LaurentComb :=
  Finsupp.single (rangeVec (r - 2)) 1

theorem evalComb_DComb (r : ℕ) (u : ℝ) : evalComb (DComb r) u = D r u := by
  unfold DComb
  rw [evalComb_single, evalMon_rangeVec_eq_D, Int.cast_one, one_mul]

/-- `JComb R`: the endpoint-corrected normalization `J_R = D_R + D_{R−1}` as
a formal combination (eq. `D-J`).  This is the seed of the finite reference
functions `Q_s^{[R]} = 𝓛_s⋯𝓛_{R−1} J_R` (eq. `finite-reference`). -/
noncomputable def JComb (R : ℕ) : LaurentComb := DComb R + DComb (R - 1)

theorem evalComb_JComb (R : ℕ) (u : ℝ) : evalComb (JComb R) u = J R u := by
  unfold JComb
  rw [evalComb_add, evalComb_DComb, evalComb_DComb]
  rfl

/-- `AComb s`: the cumulative normalization `A_s = 1 + ∑_{j=3}^s D_j` as a
formal combination (eq. `D-identity`). -/
noncomputable def AComb (s : ℕ) : LaurentComb :=
  Finsupp.single 0 1 + ∑ j ∈ Finset.Icc 3 s, DComb j

theorem evalComb_AComb (s : ℕ) (u : ℝ) : evalComb (AComb s) u = A s u := by
  unfold AComb
  rw [evalComb_add, evalComb_single, evalMon_zero_vec, evalComb_finsetSum,
    Int.cast_one, mul_one]
  unfold A
  congr 1
  exact Finset.sum_congr rfl fun j _ => evalComb_DComb j u

/-- `RdefectComb R`: the defect `R_R = A_{R−2} + A_{R−1}/x_{R−2}` of
eq. `reference-defect` as a formal combination. -/
noncomputable def RdefectComb (R : ℕ) : LaurentComb :=
  AComb (R - 2) + shiftComb (Finsupp.single (R - 2) 1) (AComb (R - 1))

theorem evalComb_RdefectComb {u : ℝ} (hu : 0 < u) (R : ℕ) :
    evalComb (RdefectComb R) u = Rdefect R u := by
  unfold RdefectComb Rdefect
  rw [evalComb_add, evalComb_AComb, evalComb_shiftComb hu, evalComb_AComb,
    evalMon_single, zpow_one]

/-! ## Size functionals: `‖·‖₁`, height, positive degree, largest index

These are the quantities the paper's induction runs on ("For a Laurent
polynomial let `d₊` be the largest sum of its positive exponents, let `ht` be
the largest sum of the absolute values of all its exponents, and let `‖·‖₁`
be the sum of the absolute values of its coefficients"). -/

/-- Coefficient ℓ¹-norm `‖P‖₁ = ∑_ν |P(ν)|`. -/
def l1Norm (P : LaurentComb) : ℕ := ∑ ν ∈ P.support, (P ν).natAbs

/-- Exponent height of a single monomial: `ht(ν) = ∑_j |ν_j|`. -/
def height (ν : ExpVec) : ℕ := ∑ j ∈ ν.support, (ν j).natAbs

/-- Positive degree of a single monomial: `d₊(ν) = ∑_j max(ν_j, 0)`. -/
def posDeg (ν : ExpVec) : ℕ := ∑ j ∈ ν.support, (ν j).toNat

/-- Largest exponent height over the monomials of a combination. -/
def combHeight (P : LaurentComb) : ℕ := P.support.sup height

/-- Largest positive degree over the monomials of a combination. -/
def combPosDeg (P : LaurentComb) : ℕ := P.support.sup posDeg

/-- Largest variable index occurring in a single exponent vector. -/
def vecMaxIdx (ν : ExpVec) : ℕ := ν.support.sup id

/-- Largest variable index occurring anywhere in a combination. -/
def maxIdx (P : LaurentComb) : ℕ := P.support.sup vecMaxIdx

theorem height_eq_sum_superset {ν : ExpVec} {s : Finset ℕ}
    (hs : ν.support ⊆ s) : height ν = ∑ j ∈ s, (ν j).natAbs :=
  Finset.sum_subset hs fun j _ hj => by
    rw [Finsupp.notMem_support_iff.mp hj, Int.natAbs_zero]

theorem l1Norm_eq_sum_superset {P : LaurentComb} {s : Finset ExpVec}
    (hs : P.support ⊆ s) : l1Norm P = ∑ ν ∈ s, (P ν).natAbs :=
  Finset.sum_subset hs fun ν _ hν => by
    rw [Finsupp.notMem_support_iff.mp hν, Int.natAbs_zero]

theorem posDeg_le_height (ν : ExpVec) : posDeg ν ≤ height ν :=
  Finset.sum_le_sum fun j _ => by omega

/-- Each monomial's height is bounded by the combination's height. -/
theorem height_le_combHeight {P : LaurentComb} {ν : ExpVec}
    (hν : ν ∈ P.support) : height ν ≤ combHeight P :=
  Finset.le_sup (f := height) hν

/-- Each monomial's positive degree is bounded by the combination's. -/
theorem posDeg_le_combPosDeg {P : LaurentComb} {ν : ExpVec}
    (hν : ν ∈ P.support) : posDeg ν ≤ combPosDeg P :=
  Finset.le_sup (f := posDeg) hν

/-- Each variable index occurring in a combination is at most `maxIdx`. -/
theorem le_maxIdx {P : LaurentComb} {ν : ExpVec} {j : ℕ}
    (hν : ν ∈ P.support) (hj : j ∈ ν.support) : j ≤ maxIdx P :=
  le_trans (Finset.le_sup (f := id) hj) (Finset.le_sup (f := vecMaxIdx) hν)

theorem combPosDeg_le_combHeight (P : LaurentComb) :
    combPosDeg P ≤ combHeight P := by
  unfold combPosDeg combHeight
  refine Finset.sup_le fun ν hν => ?_
  exact le_trans (posDeg_le_height ν) (Finset.le_sup hν)

/-! ### Height and norm under the algebraic operations

The paper's bookkeeping (proof of `lem:backward-reference-convergence`):
heights are subadditive, the division shift preserves coefficients, and
differentiation multiplies `‖·‖₁` by at most the old height. -/

theorem height_add_le (ν μ : ExpVec) : height (ν + μ) ≤ height ν + height μ := by
  rw [height_eq_sum_superset
      (Finsupp.support_add : (ν + μ).support ⊆ ν.support ∪ μ.support),
    height_eq_sum_superset
      (Finset.subset_union_left : ν.support ⊆ ν.support ∪ μ.support),
    height_eq_sum_superset
      (Finset.subset_union_right : μ.support ⊆ ν.support ∪ μ.support),
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finsupp.add_apply]
  exact Int.natAbs_add_le _ _

theorem height_neg (ν : ExpVec) : height (-ν) = height ν := by
  unfold height
  rw [Finsupp.support_neg]
  exact Finset.sum_congr rfl fun j _ => by rw [Finsupp.neg_apply, Int.natAbs_neg]

theorem height_sub_le (ν μ : ExpVec) : height (ν - μ) ≤ height ν + height μ := by
  calc height (ν - μ) = height (ν + -μ) := by rw [sub_eq_add_neg]
    _ ≤ height ν + height (-μ) := height_add_le ν (-μ)
    _ = height ν + height μ := by rw [height_neg]

theorem height_single (j : ℕ) (n : ℤ) :
    height (Finsupp.single j n) = n.natAbs := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [height]
  · unfold height
    rw [Finsupp.support_single j hn, Finset.sum_singleton,
      Finsupp.single_eq_same]

theorem height_stairVec_le (k : ℕ) : height (stairVec k) ≤ k :=
  calc height (stairVec k)
      = ∑ j ∈ Finset.Icc 1 k, ((stairVec k) j).natAbs :=
        height_eq_sum_superset (stairVec_support_subset k)
    _ ≤ ∑ _j ∈ Finset.Icc 1 k, 1 :=
        Finset.sum_le_sum fun j hj => by rw [stairVec_apply, if_pos hj]; omega
    _ = k := by rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]; omega

theorem height_aVec_le (r : ℕ) : height (aVec r) ≤ r - 2 :=
  height_stairVec_le (r - 2)

/-- Height cost of one differentiation shift: `1` for the `x₀`-term
(`ν − e₀`), at most `j − 1` for the stair of the variable `x_j`. -/
theorem height_derivShift_le (j : ℕ) : height (derivShift j) ≤ max j 1 := by
  cases j with
  | zero =>
      show height (-Finsupp.single 0 1) ≤ max 0 1
      rw [height_neg, height_single]
      omega
  | succ k =>
      show height (stairVec k) ≤ max (k + 1) 1
      exact le_trans (height_stairVec_le k) (le_max_of_le_left (by omega))

theorem l1Norm_add_le (P Q : LaurentComb) :
    l1Norm (P + Q) ≤ l1Norm P + l1Norm Q := by
  rw [l1Norm_eq_sum_superset
      (Finsupp.support_add : (P + Q).support ⊆ P.support ∪ Q.support),
    l1Norm_eq_sum_superset
      (Finset.subset_union_left : P.support ⊆ P.support ∪ Q.support),
    l1Norm_eq_sum_superset
      (Finset.subset_union_right : Q.support ⊆ P.support ∪ Q.support),
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ν _ => ?_
  rw [Finsupp.add_apply]
  exact Int.natAbs_add_le _ _

theorem l1Norm_smul (c : ℤ) (P : LaurentComb) :
    l1Norm (c • P) = c.natAbs * l1Norm P := by
  rw [l1Norm_eq_sum_superset
    (Finsupp.support_smul : (c • P).support ⊆ P.support)]
  unfold l1Norm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, Int.natAbs_mul]

theorem l1Norm_single (ν : ExpVec) (c : ℤ) :
    l1Norm (Finsupp.single ν c) = c.natAbs := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [l1Norm]
  · unfold l1Norm
    rw [Finsupp.support_single ν hc, Finset.sum_singleton,
      Finsupp.single_eq_same]

theorem l1Norm_finsetSum_le {ι : Type*} (s : Finset ι) (f : ι → LaurentComb) :
    l1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1Norm (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [l1Norm]
  | cons i s _his ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact le_trans (l1Norm_add_le _ _) (Nat.add_le_add_left ih _)

/-- The division shift leaves the coefficient ℓ¹-norm unchanged (the shift
`ν ↦ ν − μ` is a bijection onto its image). -/
theorem l1Norm_shiftComb (μ : ExpVec) (P : LaurentComb) :
    l1Norm (shiftComb μ P) = l1Norm P := by
  unfold l1Norm shiftComb
  rw [Finsupp.mapDomain_support_of_injective (sub_const_injective μ) P,
    Finset.sum_image fun ν₁ _ ν₂ _ h => sub_const_injective μ h]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [Finsupp.mapDomain_apply (sub_const_injective μ)]

/-- The division shift raises every height by at most `height μ`. -/
theorem combHeight_shiftComb_le (μ : ExpVec) (P : LaurentComb) :
    combHeight (shiftComb μ P) ≤ combHeight P + height μ := by
  have hsup : ∀ ν' ∈ (shiftComb μ P).support,
      height ν' ≤ combHeight P + height μ := by
    intro ν' hν'
    have hν'' : ν' ∈ (Finsupp.mapDomain (fun ν => ν - μ) P).support := hν'
    rw [Finsupp.mapDomain_support_of_injective (sub_const_injective μ) P]
      at hν''
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hν''
    exact le_trans (height_sub_le ν μ)
      (Nat.add_le_add_right (height_le_combHeight hν) _)
  exact Finset.sup_le hsup

/-! ### Support structure of the formal derivative -/

/-- Every variable index in `derivShift j` is at most `j`. -/
theorem mem_derivShift_support_le {j i : ℕ}
    (hi : i ∈ (derivShift j).support) : i ≤ j := by
  cases j with
  | zero =>
      have h0 : i ∈ (Finsupp.single (0 : ℕ) (1 : ℤ)).support := by
        have hsupp : (derivShift 0).support
            = (Finsupp.single (0 : ℕ) (1 : ℤ)).support :=
          Finsupp.support_neg _
        rwa [hsupp] at hi
      have hi0 : i = 0 := Finset.mem_singleton.mp (Finsupp.support_single_subset h0)
      omega
  | succ k =>
      have h := stairVec_support_subset k hi
      exact le_trans (Finset.mem_Icc.mp h).2 (by omega)

/-- Coordinates `t ≥ j` are never *increased* by the shift of the variable
`x_j`: the `x₀`-term only lowers coordinate `0`, and the stair of `x_j` only
touches coordinates `1, …, j−1`. -/
theorem derivShift_apply_nonpos {j t : ℕ} (hjt : j ≤ t) :
    derivShift j t ≤ 0 := by
  cases j with
  | zero =>
      show (-Finsupp.single (0 : ℕ) (1 : ℤ)) t ≤ 0
      rw [Finsupp.neg_apply, Finsupp.single_apply]
      split <;> omega
  | succ k =>
      show stairVec k t ≤ 0
      rw [stairVec_apply,
        if_neg fun hmem => absurd (Finset.mem_Icc.mp hmem).2 (by omega)]

/-- The support of `derivMon ν` consists of shifted copies of `ν`. -/
theorem derivMon_support_subset (ν : ExpVec) :
    (derivMon ν).support ⊆ ν.support.image fun j => ν + derivShift j := by
  unfold derivMon
  refine Finsupp.support_finsetSum.trans ?_
  intro μ hμ
  rw [Finset.mem_biUnion] at hμ
  obtain ⟨j, hj, hμj⟩ := hμ
  have hμ' := Finsupp.support_single_subset hμj
  rw [Finset.mem_singleton] at hμ'
  exact Finset.mem_image.mpr ⟨j, hj, hμ'.symm⟩

/-- Every monomial of `derivComb P` is `ν + derivShift j` for some monomial
`ν` of `P` and some variable `j` occurring in `ν` — the structural fact
behind all the derivative bookkeeping below. -/
theorem exists_of_mem_derivComb_support {P : LaurentComb} {μ : ExpVec}
    (hμ : μ ∈ (derivComb P).support) :
    ∃ ν ∈ P.support, ∃ j ∈ ν.support, μ = ν + derivShift j := by
  have h1 : μ ∈ P.support.biUnion fun ν => (P ν • derivMon ν).support := by
    have hsub : (derivComb P).support
        ⊆ P.support.biUnion fun ν => (P ν • derivMon ν).support := by
      unfold derivComb
      exact Finsupp.support_finsetSum
    exact hsub hμ
  rw [Finset.mem_biUnion] at h1
  obtain ⟨ν, hν, hμν⟩ := h1
  have h2 := derivMon_support_subset ν (Finsupp.support_smul hμν)
  rw [Finset.mem_image] at h2
  obtain ⟨j, hj, hμj⟩ := h2
  exact ⟨ν, hν, j, hj, hμj.symm⟩

/-! ### Bookkeeping of the formal derivative -/

/-- A monomial spawns at most `height ν` worth of coefficients under formal
differentiation (`∑_j |ν_j| = ht(ν)`). -/
theorem l1Norm_derivMon_le (ν : ExpVec) : l1Norm (derivMon ν) ≤ height ν := by
  unfold derivMon
  calc l1Norm (∑ j ∈ ν.support, Finsupp.single (ν + derivShift j) (ν j))
      ≤ ∑ j ∈ ν.support, l1Norm (Finsupp.single (ν + derivShift j) (ν j)) :=
        l1Norm_finsetSum_le _ _
    _ = ∑ j ∈ ν.support, (ν j).natAbs :=
        Finset.sum_congr rfl fun j _ => l1Norm_single _ _
    _ = height ν := rfl

/-- "Differentiation multiplies the coefficient ℓ¹-norm by at most the old
height" (proof of `lem:backward-reference-convergence`). -/
theorem l1Norm_derivComb_le (P : LaurentComb) :
    l1Norm (derivComb P) ≤ combHeight P * l1Norm P := by
  unfold derivComb
  calc l1Norm (∑ ν ∈ P.support, P ν • derivMon ν)
      ≤ ∑ ν ∈ P.support, l1Norm (P ν • derivMon ν) := l1Norm_finsetSum_le _ _
    _ = ∑ ν ∈ P.support, (P ν).natAbs * l1Norm (derivMon ν) :=
        Finset.sum_congr rfl fun ν _ => l1Norm_smul _ _
    _ ≤ ∑ ν ∈ P.support, (P ν).natAbs * combHeight P :=
        Finset.sum_le_sum fun ν hν => Nat.mul_le_mul le_rfl
          (le_trans (l1Norm_derivMon_le ν) (Finset.le_sup hν))
    _ = combHeight P * l1Norm P := by rw [← Finset.sum_mul, mul_comm]; rfl

/-- The paper's "one differentiation raises the height by at most the largest
variable index plus one" (proof of `lem:backward-reference-convergence`):
here by at most `maxIdx P + 1`, the `+1` covering the possible `x₀`-term
`ν₀ x^{ν−e₀}`, which raises the height by `1` when `ν₀ < 0`. -/
theorem combHeight_derivComb_le (P : LaurentComb) :
    combHeight (derivComb P) ≤ combHeight P + maxIdx P + 1 := by
  have hsup : ∀ μ ∈ (derivComb P).support,
      height μ ≤ combHeight P + maxIdx P + 1 := by
    intro μ hμ
    obtain ⟨ν, hν, j, hj, rfl⟩ := exists_of_mem_derivComb_support hμ
    have h1 : height (ν + derivShift j) ≤ height ν + height (derivShift j) :=
      height_add_le _ _
    have h2 : height ν ≤ combHeight P := height_le_combHeight hν
    have h3 : height (derivShift j) ≤ max j 1 := height_derivShift_le j
    have h4 : j ≤ maxIdx P := le_maxIdx hν hj
    omega
  exact Finset.sup_le hsup

/-- Formal differentiation never introduces variables of index above the
existing maximum (the `x₀`-term lowers coordinate `0`; the stair of `x_j`
adds only indices `< j`). -/
theorem maxIdx_derivComb_le (P : LaurentComb) :
    maxIdx (derivComb P) ≤ maxIdx P := by
  have hsup : ∀ μ ∈ (derivComb P).support, vecMaxIdx μ ≤ maxIdx P := by
    intro μ hμ
    obtain ⟨ν, hν, j, hj, rfl⟩ := exists_of_mem_derivComb_support hμ
    have hidx : ∀ i ∈ (ν + derivShift j).support, i ≤ maxIdx P := by
      intro i hi
      have hi' : i ∈ ν.support ∪ (derivShift j).support :=
        Finsupp.support_add hi
      rcases Finset.mem_union.mp hi' with h | h
      · exact le_maxIdx hν h
      · exact le_trans (mem_derivShift_support_le h) (le_maxIdx hν hj)
    exact Finset.sup_le hidx
  exact Finset.sup_le hsup

/-- The division shift introduces at most the variables of the divisor. -/
theorem maxIdx_shiftComb_le (μ : ExpVec) (P : LaurentComb) :
    maxIdx (shiftComb μ P) ≤ max (maxIdx P) (vecMaxIdx μ) := by
  have hsup : ∀ ν' ∈ (shiftComb μ P).support,
      vecMaxIdx ν' ≤ max (maxIdx P) (vecMaxIdx μ) := by
    intro ν' hν'
    have hν'' : ν' ∈ (Finsupp.mapDomain (fun ν => ν - μ) P).support := hν'
    rw [Finsupp.mapDomain_support_of_injective (sub_const_injective μ) P]
      at hν''
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hν''
    have hidx : ∀ i ∈ (ν - μ).support, i ≤ max (maxIdx P) (vecMaxIdx μ) := by
      intro i hi
      have hi' : i ∈ ν.support ∪ μ.support := by
        have hsub : (ν - μ).support ⊆ ν.support ∪ (-μ).support := by
          rw [sub_eq_add_neg]
          exact Finsupp.support_add
        rw [Finsupp.support_neg] at hsub
        exact hsub hi
      rcases Finset.mem_union.mp hi' with h | h
      · refine le_max_of_le_left ?_
        exact le_trans (Finset.le_sup (f := id) h)
          (Finset.le_sup (f := vecMaxIdx) hν)
      · exact le_max_of_le_right (Finset.le_sup (f := id) h)
    exact Finset.sup_le hidx
  exact Finset.sup_le hsup

/-! ### Persistence of a terminal inverse factor

The paper: "These terminal inverse factors persist under every later operator
and under ordinary differentiation: differentiating `x_j` changes only
variables of index below `j`, and the denominator in every later `𝓛_r` also
involves only lower-index variables." -/

/-- If every monomial of `P` carries `x_t^{-1}` (coordinate `≤ −1` at `t`)
and no variable of index above `t` occurs, then every monomial of the formal
derivative still carries `x_t^{-1}`. -/
theorem derivComb_apply_le_neg_one {P : LaurentComb} {t : ℕ}
    (hmax : maxIdx P ≤ t) (hP : ∀ ν ∈ P.support, ν t ≤ -1) :
    ∀ μ ∈ (derivComb P).support, μ t ≤ -1 := by
  intro μ hμ
  obtain ⟨ν, hν, j, hj, rfl⟩ := exists_of_mem_derivComb_support hμ
  have hjt : j ≤ t := le_trans (le_maxIdx hν hj) hmax
  have hshift : derivShift j t ≤ 0 := derivShift_apply_nonpos hjt
  have hνt := hP ν hν
  show ν t + derivShift j t ≤ -1
  omega

/-- If every monomial of `P` carries `x_t^{-1}` and the divisor's coordinate
at `t` is nonnegative (e.g. `μ = aVec r`, `aVec_apply_nonneg`), then every
monomial of the shifted combination still carries `x_t^{-1}`. -/
theorem shiftComb_apply_le_neg_one {P : LaurentComb} {μ : ExpVec} {t : ℕ}
    (hμ : 0 ≤ μ t) (hP : ∀ ν ∈ P.support, ν t ≤ -1) :
    ∀ ν' ∈ (shiftComb μ P).support, ν' t ≤ -1 := by
  intro ν' hν'
  have hν'' : ν' ∈ (Finsupp.mapDomain (fun ν => ν - μ) P).support := hν'
  rw [Finsupp.mapDomain_support_of_injective (sub_const_injective μ) P] at hν''
  obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hν''
  have hνt := hP ν hν
  show ν t - μ t ≤ -1
  omega

/-! ## Evaluation estimates

The paper's step from bookkeeping to bounds: on `u ∈ [1, e]`, each monomial
is at most `xmax^{d₊}` when every variable with positive exponent is `≤ xmax`
(negative-exponent factors are `≤ 1` since `E_j ≥ 1`), and a designated
terminal inverse variable `x_t^{-1}` contributes an extra factor `1/x_t`. -/

/-- Product form of the monomial estimate, over an arbitrary index set. -/
theorem prod_zpow_le_pow_sum_toNat {u xmax : ℝ} (hu : 1 ≤ u) {ν : ExpVec}
    {s : Finset ℕ} (hbound : ∀ j ∈ s, 0 < ν j → E j u ≤ xmax) :
    ∏ j ∈ s, E j u ^ ν j ≤ xmax ^ ∑ j ∈ s, (ν j).toNat := by
  have hu0 : (0 : ℝ) < u := by linarith
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod
    (fun j _ => (zpow_pos (E_pos_of_pos hu0 j) _).le) fun j hj => ?_
  rcases le_or_gt (ν j) 0 with hle | hgt
  · have h1 : E j u ^ ν j ≤ 1 :=
      zpow_le_one_of_nonpos₀ (one_le_E_of_one_le hu j) hle
    have h2 : (ν j).toNat = 0 := by omega
    rw [h2, pow_zero]
    exact h1
  · have hcast : E j u ^ ν j = E j u ^ (ν j).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hgt.le]
    rw [hcast]
    exact pow_le_pow_left₀ (le_trans zero_le_one (one_le_E_of_one_le hu j))
      (hbound j hj hgt) _

/-- Monomial estimate: `|x^ν| ≤ xmax^{d₊(ν)}` on `u ≥ 1` when every variable
with positive exponent is bounded by `xmax`. -/
theorem abs_evalMon_le {u xmax : ℝ} (hu : 1 ≤ u) {ν : ExpVec}
    (hbound : ∀ j ∈ ν.support, 0 < ν j → E j u ≤ xmax) :
    |evalMon ν u| ≤ xmax ^ posDeg ν := by
  rw [abs_of_pos (evalMon_pos (by linarith) ν)]
  exact prod_zpow_le_pow_sum_toNat hu hbound

/-- Terminal-inverse refinement (the paper's crux): a designated variable `t`
with exponent `≤ −1` contributes an extra factor `1/x_t` beyond the
`xmax^{d₊}` bound. -/
theorem abs_evalMon_le_div {u xmax : ℝ} (hu : 1 ≤ u) {ν : ExpVec}
    (hbound : ∀ j ∈ ν.support, 0 < ν j → E j u ≤ xmax) {t : ℕ}
    (ht : ν t ≤ -1) :
    |evalMon ν u| ≤ xmax ^ posDeg ν / E t u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have htmem : t ∈ ν.support := Finsupp.mem_support_iff.mpr (by omega)
  rw [abs_of_pos (evalMon_pos hu0 ν)]
  have hsplit : evalMon ν u
      = (∏ j ∈ ν.support.erase t, E j u ^ ν j) * E t u ^ ν t :=
    (Finset.prod_erase_mul _ _ htmem).symm
  have hprod : (∏ j ∈ ν.support.erase t, E j u ^ ν j) ≤ xmax ^ posDeg ν := by
    have h1 : (∏ j ∈ ν.support.erase t, E j u ^ ν j)
        ≤ xmax ^ ∑ j ∈ ν.support.erase t, (ν j).toNat :=
      prod_zpow_le_pow_sum_toNat hu fun j hj hpos =>
        hbound j (Finset.mem_of_mem_erase hj) hpos
    have h2 : (∑ j ∈ ν.support.erase t, (ν j).toNat) = posDeg ν :=
      Finset.sum_erase _ (by omega)
    rwa [h2] at h1
  have hb : (0 : ℝ) ≤ xmax ^ posDeg ν :=
    le_trans (Finset.prod_pos fun j _ =>
      zpow_pos (E_pos_of_pos hu0 j) _ : (0 : ℝ)
        < ∏ j ∈ ν.support.erase t, E j u ^ ν j).le hprod
  have hEfac : E t u ^ ν t ≤ (E t u)⁻¹ := by
    have h := zpow_le_zpow_right₀ (one_le_E_of_one_le hu t) ht
    rwa [zpow_neg, zpow_one] at h
  calc evalMon ν u
      = (∏ j ∈ ν.support.erase t, E j u ^ ν j) * E t u ^ ν t := hsplit
    _ ≤ xmax ^ posDeg ν * (E t u)⁻¹ :=
        mul_le_mul hprod hEfac (zpow_pos (E_pos_of_pos hu0 t) _).le hb
    _ = xmax ^ posDeg ν / E t u := by rw [div_eq_mul_inv]

/-- Combination estimate: `|evalComb P u| ≤ ‖P‖₁ · xmax^{d₊(P)}` on `u ≥ 1`
(needs `1 ≤ xmax` to compare the per-monomial degrees to `combPosDeg`). -/
theorem abs_evalComb_le {u xmax : ℝ} (hu : 1 ≤ u) (hxmax : 1 ≤ xmax)
    {P : LaurentComb}
    (hbound : ∀ ν ∈ P.support, ∀ j ∈ ν.support, 0 < ν j → E j u ≤ xmax) :
    |evalComb P u| ≤ (l1Norm P : ℝ) * xmax ^ combPosDeg P := by
  calc |evalComb P u| ≤ ∑ ν ∈ P.support, |(P ν : ℝ) * evalMon ν u| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ν ∈ P.support, ((P ν).natAbs : ℝ) * xmax ^ combPosDeg P := by
        refine Finset.sum_le_sum fun ν hν => ?_
        rw [abs_mul, Nat.cast_natAbs, Int.cast_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ((P ν : ℝ)))
        calc |evalMon ν u| ≤ xmax ^ posDeg ν := abs_evalMon_le hu (hbound ν hν)
          _ ≤ xmax ^ combPosDeg P :=
              pow_le_pow_right₀ hxmax (posDeg_le_combPosDeg hν)
    _ = (l1Norm P : ℝ) * xmax ^ combPosDeg P := by
        rw [← Finset.sum_mul]
        congr 1
        unfold l1Norm
        push_cast
        rfl

/-- Combination estimate with a persistent terminal inverse factor: if every
monomial of `P` carries `x_t^{-1}`, the whole combination gains `1/x_t`. -/
theorem abs_evalComb_le_div {u xmax : ℝ} (hu : 1 ≤ u) (hxmax : 1 ≤ xmax)
    {P : LaurentComb}
    (hbound : ∀ ν ∈ P.support, ∀ j ∈ ν.support, 0 < ν j → E j u ≤ xmax)
    {t : ℕ} (ht : ∀ ν ∈ P.support, ν t ≤ -1) :
    |evalComb P u| ≤ (l1Norm P : ℝ) * xmax ^ combPosDeg P / E t u := by
  have hu0 : (0 : ℝ) < u := by linarith
  calc |evalComb P u| ≤ ∑ ν ∈ P.support, |(P ν : ℝ) * evalMon ν u| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ν ∈ P.support,
          ((P ν).natAbs : ℝ) * (xmax ^ combPosDeg P / E t u) := by
        refine Finset.sum_le_sum fun ν hν => ?_
        rw [abs_mul, Nat.cast_natAbs, Int.cast_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ((P ν : ℝ)))
        calc |evalMon ν u|
            ≤ xmax ^ posDeg ν / E t u :=
              abs_evalMon_le_div hu (hbound ν hν) (ht ν hν)
          _ ≤ xmax ^ combPosDeg P / E t u :=
              div_le_div_of_nonneg_right
                (pow_le_pow_right₀ hxmax (posDeg_le_combPosDeg hν))
                (E_pos_of_pos hu0 t).le
    _ = (l1Norm P : ℝ) * xmax ^ combPosDeg P / E t u := by
        rw [← Finset.sum_mul, mul_div_assoc]
        congr 1
        unfold l1Norm
        push_cast
        rfl

end Erdos320
