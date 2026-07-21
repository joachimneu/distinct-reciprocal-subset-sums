import Erdos320.Lemmas.BackwardReference
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Explicit closed forms for the reference core `Q̃₄`, `Q̃₃` (eq. `reference-core`)

The reference core of §6, `Q̃₄ = 𝓛₄(A₅ + B₅)` and `Q̃₃ = 𝓛₃ Q̃₄`
(`Erdos320.QrefCore4`, `Erdos320.QrefCore3`), is a finite, explicitly
computable rational function of the iterated exponentials `E₁(u) = eᵘ`,
`E₂(u) = e^{E₁}`, `E₃(u) = e^{E₂}`.  This file records the exact closed forms
of `Q̃₄`, its first and second derivatives, and `Q̃₃`, as consumed by the
interval certificates of `sec:certificates`.

Every object is a Laurent polynomial in `E₁, E₂, E₃, u` with common denominator
`E₁²E₂²E₃`; the derivations `E₁' = E₁`, `E₂' = E₁E₂`, `E₃' = E₁E₂E₃` are the
manuscript's eq. `laurent-derivative`.  The closed forms match the certificate
program's `finite_reference_values` (`directed_interval_certificate.py`); they
are proved here directly from Mathlib's `HasDerivAt` calculus (not via the
`LaurentComb` symbolic layer), so the numerator polynomials appear literally.
-/

namespace Erdos320

/-! ## Derivatives of the iterated exponentials (eq. `laurent-derivative`) -/

/-- `E₁' = E₁` (chain-rule product `∏_{Icc 1 1} = E₁`). -/
theorem hasDerivAt_E1 (v : ℝ) : HasDerivAt (E 1) (E 1 v) v := by
  have h := hasDerivAt_E 1 v
  rwa [Finset.Icc_self, Finset.prod_singleton] at h

/-- `E₂' = E₁E₂` (chain-rule product `∏_{Icc 1 2} = E₁E₂`). -/
theorem hasDerivAt_E2 (v : ℝ) : HasDerivAt (E 2) (E 1 v * E 2 v) v := by
  have hp : (∏ j ∈ Finset.Icc 1 2, E j v) = E 1 v * E 2 v := by
    rw [show Finset.Icc (1 : ℕ) 2 = {1, 2} from by decide, Finset.prod_pair (by decide)]
  have h := hasDerivAt_E 2 v
  rwa [hp] at h

/-- `E₃' = E₁E₂E₃` (chain-rule product `∏_{Icc 1 3} = E₁E₂E₃`). -/
theorem hasDerivAt_E3 (v : ℝ) : HasDerivAt (E 3) (E 1 v * E 2 v * E 3 v) v := by
  have hp : (∏ j ∈ Finset.Icc 1 3, E j v) = E 1 v * E 2 v * E 3 v := by
    rw [show Finset.Icc (1 : ℕ) 3 = {1, 2, 3} from by decide, Finset.prod_insert (by decide),
      Finset.prod_pair (by decide), ← mul_assoc]
  have h := hasDerivAt_E 3 v
  rwa [hp] at h

/-! ## Small closed forms for the chain-rule factors `a₄`, `a₅` -/

/-- `a₄(u) = E₁E₂` (eq. `a-rho`). -/
theorem a4_val (v : ℝ) : a 4 v = E 1 v * E 2 v := by
  have h := a_succ (r := 3) (by norm_num) v
  rw [show (3 : ℕ) + 1 = 4 from rfl, show (3 : ℕ) - 1 = 2 from rfl, a_three] at h
  exact h

/-- `a₅(u) = E₁E₂E₃` (eq. `a-rho`). -/
theorem a5_val (v : ℝ) : a 5 v = E 1 v * E 2 v * E 3 v := by
  have h := a_succ (r := 4) (by norm_num) v
  rw [show (4 : ℕ) + 1 = 5 from rfl, show (4 : ℕ) - 1 = 3 from rfl, a4_val] at h
  exact h

/-! ## `A₅` and its derivative -/

/-- `A₅` in closed form (`A_five_eq`). -/
noncomputable def A5f (v : ℝ) : ℝ := 1 + v + v * E 1 v + v * E 1 v * E 2 v

/-- `A₅'` in closed form. -/
noncomputable def dA5f (v : ℝ) : ℝ :=
  1 + E 1 v + v * E 1 v + E 1 v * E 2 v + v * E 1 v * E 2 v + v * E 1 v ^ 2 * E 2 v

/-- `HasDerivAt (A₅) (dA5f)` (differentiating the closed form `A_five_eq`). -/
theorem hasDerivAt_A5 (v : ℝ) : HasDerivAt (A 5) (dA5f v) v := by
  have hA5eq : A 5 = A5f := by funext w; exact A_five_eq w
  rw [hA5eq]
  have h : HasDerivAt A5f _ v :=
    ((((hasDerivAt_const v (1 : ℝ)).fun_add (hasDerivAt_id' v)).fun_add
        ((hasDerivAt_id' v).fun_mul (hasDerivAt_E1 v))).fun_add
      (((hasDerivAt_id' v).fun_mul (hasDerivAt_E1 v)).fun_mul (hasDerivAt_E2 v)))
  convert h using 1
  simp only [dA5f]
  ring

/-- `A₅'(u) = dA5f u`. -/
theorem deriv_A5 (v : ℝ) : deriv (A 5) v = dA5f v := (hasDerivAt_A5 v).deriv

/-! ## The reference core `Q̃₄`, its derivatives, and `Q̃₃` -/

/-- Common denominator `E₁²E₂²E₃`. -/
noncomputable def QC4den (v : ℝ) : ℝ := E 1 v ^ 2 * E 2 v ^ 2 * E 3 v

theorem QC4den_ne (v : ℝ) : QC4den v ≠ 0 := by
  unfold QC4den
  exact (mul_pos (mul_pos (pow_pos (E_pos_of_one_le (j := 1) (by norm_num) v) 2)
      (pow_pos (E_pos_of_one_le (j := 2) (by norm_num) v) 2))
    (E_pos_of_one_le (j := 3) (by norm_num) v)).ne'

/-- Numerator of `Q̃₄` over `E₁²E₂²E₃`. -/
noncomputable def numQC4f (v : ℝ) : ℝ :=
  (0 : ℝ) - (1 : ℝ) + (E 1 v * E 2 v * E 3 v) - (E 1 v ^ 2) + (E 1 v ^ 2 * E 2 v * E 3 v) - (E 1 v ^ 2 * E 2 v ^ 2) + (E 1 v ^ 2 * E 2 v ^ 2 * E 3 v) - (v * E 1 v ^ 2) + (v * E 1 v ^ 2 * E 2 v * E 3 v) - (v * E 1 v ^ 2 * E 2 v ^ 2) + (v * E 1 v ^ 2 * E 2 v ^ 2 * E 3 v) - (v * E 1 v ^ 3 * E 2 v ^ 2) + (v * E 1 v ^ 3 * E 2 v ^ 2 * E 3 v)

/-- Numerator of `Q̃₄'` over `E₁²E₂²E₃`. -/
noncomputable def numdQC4f (v : ℝ) : ℝ :=
  (0 : ℝ) + (2 : ℝ) + ((2 : ℝ) * (E 1 v)) + (E 1 v * E 2 v) - (E 1 v * E 2 v * E 3 v) - (E 1 v ^ 2) - (E 1 v ^ 2 * E 2 v ^ 2) + (E 1 v ^ 2 * E 2 v ^ 2 * E 3 v) + ((2 : ℝ) * (E 1 v ^ 3)) + (E 1 v ^ 3 * E 2 v) - (E 1 v ^ 3 * E 2 v * E 3 v) - (E 1 v ^ 3 * E 2 v ^ 2) + (E 1 v ^ 3 * E 2 v ^ 2 * E 3 v) + (E 1 v ^ 3 * E 2 v ^ 3) + ((2 : ℝ) * (v * E 1 v ^ 3)) + (v * E 1 v ^ 3 * E 2 v) - (v * E 1 v ^ 3 * E 2 v * E 3 v) - (v * E 1 v ^ 3 * E 2 v ^ 2) + (v * E 1 v ^ 3 * E 2 v ^ 2 * E 3 v) + (v * E 1 v ^ 3 * E 2 v ^ 3) + (v * E 1 v ^ 4 * E 2 v ^ 3)

/-- Numerator of `Q̃₄''` over `E₁²E₂²E₃`. -/
noncomputable def numd2QC4f (v : ℝ) : ℝ :=
  (0 : ℝ) - (4 : ℝ) - ((6 : ℝ) * (E 1 v)) - ((3 : ℝ) * (E 1 v * E 2 v)) + (E 1 v * E 2 v * E 3 v) - ((4 : ℝ) * (E 1 v ^ 2)) - ((3 : ℝ) * (E 1 v ^ 2 * E 2 v)) + (E 1 v ^ 2 * E 2 v * E 3 v) - (E 1 v ^ 2 * E 2 v ^ 2) + ((6 : ℝ) * (E 1 v ^ 3)) + ((3 : ℝ) * (E 1 v ^ 3 * E 2 v)) - ((2 : ℝ) * (E 1 v ^ 3 * E 2 v * E 3 v)) - ((2 : ℝ) * (E 1 v ^ 3 * E 2 v ^ 2)) + ((2 : ℝ) * (E 1 v ^ 3 * E 2 v ^ 2 * E 3 v)) + ((3 : ℝ) * (E 1 v ^ 3 * E 2 v ^ 3)) - ((4 : ℝ) * (E 1 v ^ 4)) - ((3 : ℝ) * (E 1 v ^ 4 * E 2 v)) + (E 1 v ^ 4 * E 2 v * E 3 v) - (E 1 v ^ 4 * E 2 v ^ 2) + ((3 : ℝ) * (E 1 v ^ 4 * E 2 v ^ 3)) - (E 1 v ^ 4 * E 2 v ^ 4) + ((2 : ℝ) * (v * E 1 v ^ 3)) + (v * E 1 v ^ 3 * E 2 v) - (v * E 1 v ^ 3 * E 2 v * E 3 v) - (v * E 1 v ^ 3 * E 2 v ^ 2) + (v * E 1 v ^ 3 * E 2 v ^ 2 * E 3 v) + (v * E 1 v ^ 3 * E 2 v ^ 3) - ((4 : ℝ) * (v * E 1 v ^ 4)) - ((3 : ℝ) * (v * E 1 v ^ 4 * E 2 v)) + (v * E 1 v ^ 4 * E 2 v * E 3 v) - (v * E 1 v ^ 4 * E 2 v ^ 2) + ((4 : ℝ) * (v * E 1 v ^ 4 * E 2 v ^ 3)) - (v * E 1 v ^ 4 * E 2 v ^ 4) + (v * E 1 v ^ 5 * E 2 v ^ 3) - (v * E 1 v ^ 5 * E 2 v ^ 4)

/-- `Q̃₄` as `numQC4f / (E₁²E₂²E₃)`. -/
noncomputable def QC4f (v : ℝ) : ℝ := numQC4f v / QC4den v

/-- `Q̃₄'` as `numdQC4f / (E₁²E₂²E₃)`. -/
noncomputable def dQC4f (v : ℝ) : ℝ := numdQC4f v / QC4den v

/-! ## Value identities (all `u`) -/

set_option maxHeartbeats 1600000 in
/-- `Q̃₄ = QC4f`. -/
theorem QrefCore4_val (v : ℝ) : QrefCore4 v = QC4f v := by
  have e1ne : E 1 v ≠ 0 := (E_pos_of_one_le (j := 1) (by norm_num) v).ne'
  have e2ne : E 2 v ≠ 0 := (E_pos_of_one_le (j := 2) (by norm_num) v).ne'
  have e3ne : E 3 v ≠ 0 := (E_pos_of_one_le (j := 3) (by norm_num) v).ne'
  have hBrefeq : Bref 5 = fun w => dA5f w / (E 1 w * E 2 w * E 3 w) := by
    funext w; unfold Bref; rw [deriv_A5 w, a5_val w]
  have hden3ne : E 1 v * E 2 v * E 3 v ≠ 0 := mul_ne_zero (mul_ne_zero e1ne e2ne) e3ne
  have hA5 : HasDerivAt (A 5) (dA5f v) v := hasDerivAt_A5 v
  have hdA5 : HasDerivAt dA5f _ v :=
    ((((((hasDerivAt_const v (1 : ℝ)).fun_add (hasDerivAt_E1 v)).fun_add
          ((hasDerivAt_id' v).fun_mul (hasDerivAt_E1 v))).fun_add
        ((hasDerivAt_E1 v).fun_mul (hasDerivAt_E2 v))).fun_add
      (((hasDerivAt_id' v).fun_mul (hasDerivAt_E1 v)).fun_mul (hasDerivAt_E2 v))).fun_add
      (((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 2)).fun_mul (hasDerivAt_E2 v)))
  have hden3 : HasDerivAt (fun w => E 1 w * E 2 w * E 3 w) _ v :=
    ((hasDerivAt_E1 v).fun_mul (hasDerivAt_E2 v)).fun_mul (hasDerivAt_E3 v)
  have hBref5 := hBrefeq.symm ▸ hdA5.fun_div hden3 hden3ne
  have hsum : HasDerivAt (fun w => A 5 w + Bref 5 w) _ v := hA5.fun_add hBref5
  have hQ : QrefCore4 v = _ / a 4 v := Lop_eq_of_hasDerivAt (r := 4) hsum
  rw [hQ, a4_val v]
  simp only [QC4f, numQC4f, QC4den, dA5f]
  field_simp
  ring

set_option maxHeartbeats 3200000 in
/-- `Q̃₄' = dQC4f`. -/
theorem deriv_QrefCore4_val (v : ℝ) : deriv QrefCore4 v = dQC4f v := by
  have e1ne : E 1 v ≠ 0 := (E_pos_of_one_le (j := 1) (by norm_num) v).ne'
  have e2ne : E 2 v ≠ 0 := (E_pos_of_one_le (j := 2) (by norm_num) v).ne'
  have e3ne : E 3 v ≠ 0 := (E_pos_of_one_le (j := 3) (by norm_num) v).ne'
  rw [show QrefCore4 = QC4f from funext QrefCore4_val]
  have hden : HasDerivAt QC4den _ v :=
    (((hasDerivAt_E1 v).fun_pow 2).fun_mul ((hasDerivAt_E2 v).fun_pow 2)).fun_mul (hasDerivAt_E3 v)
  have hnum : HasDerivAt numQC4f _ v :=
    (((((((((((((hasDerivAt_const v (0 : ℝ)).fun_sub (hasDerivAt_const v (1 : ℝ))).fun_add (((hasDerivAt_E1 v).fun_mul (hasDerivAt_E2 v)).fun_mul (hasDerivAt_E3 v))).fun_sub ((hasDerivAt_E1 v).fun_pow 2)).fun_add ((((hasDerivAt_E1 v).fun_pow 2).fun_mul (hasDerivAt_E2 v)).fun_mul (hasDerivAt_E3 v))).fun_sub (((hasDerivAt_E1 v).fun_pow 2).fun_mul ((hasDerivAt_E2 v).fun_pow 2))).fun_add ((((hasDerivAt_E1 v).fun_pow 2).fun_mul ((hasDerivAt_E2 v).fun_pow 2)).fun_mul (hasDerivAt_E3 v))).fun_sub ((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 2))).fun_add ((((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 2)).fun_mul (hasDerivAt_E2 v)).fun_mul (hasDerivAt_E3 v))).fun_sub (((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 2)).fun_mul ((hasDerivAt_E2 v).fun_pow 2))).fun_add ((((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 2)).fun_mul ((hasDerivAt_E2 v).fun_pow 2)).fun_mul (hasDerivAt_E3 v))).fun_sub (((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 3)).fun_mul ((hasDerivAt_E2 v).fun_pow 2))).fun_add ((((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 3)).fun_mul ((hasDerivAt_E2 v).fun_pow 2)).fun_mul (hasDerivAt_E3 v)))
  have h' : HasDerivAt QC4f _ v := hnum.fun_div hden (QC4den_ne v)
  rw [h'.deriv]
  simp only [dQC4f, numdQC4f, numQC4f, QC4den]
  field_simp
  ring

set_option maxHeartbeats 6400000 in
/-- `Q̃₄'' = numd2QC4f / (E₁²E₂²E₃)`. -/
theorem deriv2_QrefCore4_val (v : ℝ) :
    deriv (deriv QrefCore4) v = numd2QC4f v / QC4den v := by
  have e1ne : E 1 v ≠ 0 := (E_pos_of_one_le (j := 1) (by norm_num) v).ne'
  have e2ne : E 2 v ≠ 0 := (E_pos_of_one_le (j := 2) (by norm_num) v).ne'
  have e3ne : E 3 v ≠ 0 := (E_pos_of_one_le (j := 3) (by norm_num) v).ne'
  rw [show deriv QrefCore4 = dQC4f from funext deriv_QrefCore4_val]
  have hden : HasDerivAt QC4den _ v :=
    (((hasDerivAt_E1 v).fun_pow 2).fun_mul ((hasDerivAt_E2 v).fun_pow 2)).fun_mul (hasDerivAt_E3 v)
  have hnum : HasDerivAt numdQC4f _ v :=
    (((((((((((((((((((((hasDerivAt_const v (0 : ℝ)).fun_add (hasDerivAt_const v (2 : ℝ))).fun_add ((hasDerivAt_E1 v).const_mul (2 : ℝ))).fun_add ((hasDerivAt_E1 v).fun_mul (hasDerivAt_E2 v))).fun_sub (((hasDerivAt_E1 v).fun_mul (hasDerivAt_E2 v)).fun_mul (hasDerivAt_E3 v))).fun_sub ((hasDerivAt_E1 v).fun_pow 2)).fun_sub (((hasDerivAt_E1 v).fun_pow 2).fun_mul ((hasDerivAt_E2 v).fun_pow 2))).fun_add ((((hasDerivAt_E1 v).fun_pow 2).fun_mul ((hasDerivAt_E2 v).fun_pow 2)).fun_mul (hasDerivAt_E3 v))).fun_add (((hasDerivAt_E1 v).fun_pow 3).const_mul (2 : ℝ))).fun_add (((hasDerivAt_E1 v).fun_pow 3).fun_mul (hasDerivAt_E2 v))).fun_sub ((((hasDerivAt_E1 v).fun_pow 3).fun_mul (hasDerivAt_E2 v)).fun_mul (hasDerivAt_E3 v))).fun_sub (((hasDerivAt_E1 v).fun_pow 3).fun_mul ((hasDerivAt_E2 v).fun_pow 2))).fun_add ((((hasDerivAt_E1 v).fun_pow 3).fun_mul ((hasDerivAt_E2 v).fun_pow 2)).fun_mul (hasDerivAt_E3 v))).fun_add (((hasDerivAt_E1 v).fun_pow 3).fun_mul ((hasDerivAt_E2 v).fun_pow 3))).fun_add (((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 3)).const_mul (2 : ℝ))).fun_add (((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 3)).fun_mul (hasDerivAt_E2 v))).fun_sub ((((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 3)).fun_mul (hasDerivAt_E2 v)).fun_mul (hasDerivAt_E3 v))).fun_sub (((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 3)).fun_mul ((hasDerivAt_E2 v).fun_pow 2))).fun_add ((((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 3)).fun_mul ((hasDerivAt_E2 v).fun_pow 2)).fun_mul (hasDerivAt_E3 v))).fun_add (((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 3)).fun_mul ((hasDerivAt_E2 v).fun_pow 3))).fun_add (((hasDerivAt_id' v).fun_mul ((hasDerivAt_E1 v).fun_pow 4)).fun_mul ((hasDerivAt_E2 v).fun_pow 3)))
  have h' : HasDerivAt dQC4f _ v := hnum.fun_div hden (QC4den_ne v)
  rw [h'.deriv]
  simp only [numd2QC4f, numdQC4f, QC4den]
  field_simp
  ring

/-- `Q̃₃ = numdQC4f / (E₁³E₂²E₃)`  (`Q̃₃ = 𝓛₃ Q̃₄ = Q̃₄'/E₁`). -/
theorem QrefCore3_val (v : ℝ) :
    QrefCore3 v = numdQC4f v / (E 1 v ^ 3 * E 2 v ^ 2 * E 3 v) := by
  have h1 : QrefCore3 v = deriv QrefCore4 v / a 3 v := rfl
  rw [h1, deriv_QrefCore4_val v, a_three]
  unfold dQC4f QC4den
  rw [div_div]
  congr 1
  ring

/-! ## Public closed-form API (for the interval certificates)

Each RHS is the explicit Laurent polynomial numerator over its monomial
denominator; the `_hu : 0 < u` hypothesis is kept for the certificate callers
(the identities in fact hold for every real `u`). -/

/-- **Closed form of `Q̃₄`** (12 monomials over `E₁²E₂²E₃`). -/
theorem QrefCore4_closedForm {u : ℝ} (_hu : 0 < u) :
    QrefCore4 u =
      ((0 : ℝ) - (1 : ℝ) + (E 1 u * E 2 u * E 3 u) - (E 1 u ^ 2) + (E 1 u ^ 2 * E 2 u * E 3 u) - (E 1 u ^ 2 * E 2 u ^ 2) + (E 1 u ^ 2 * E 2 u ^ 2 * E 3 u) - (u * E 1 u ^ 2) + (u * E 1 u ^ 2 * E 2 u * E 3 u) - (u * E 1 u ^ 2 * E 2 u ^ 2) + (u * E 1 u ^ 2 * E 2 u ^ 2 * E 3 u) - (u * E 1 u ^ 3 * E 2 u ^ 2) + (u * E 1 u ^ 3 * E 2 u ^ 2 * E 3 u)) / (E 1 u ^ 2 * E 2 u ^ 2 * E 3 u) :=
  QrefCore4_val u

/-- **Closed form of `Q̃₄'`** (20 monomials over `E₁²E₂²E₃`). -/
theorem deriv_QrefCore4_closedForm {u : ℝ} (_hu : 0 < u) :
    deriv QrefCore4 u =
      ((0 : ℝ) + (2 : ℝ) + ((2 : ℝ) * (E 1 u)) + (E 1 u * E 2 u) - (E 1 u * E 2 u * E 3 u) - (E 1 u ^ 2) - (E 1 u ^ 2 * E 2 u ^ 2) + (E 1 u ^ 2 * E 2 u ^ 2 * E 3 u) + ((2 : ℝ) * (E 1 u ^ 3)) + (E 1 u ^ 3 * E 2 u) - (E 1 u ^ 3 * E 2 u * E 3 u) - (E 1 u ^ 3 * E 2 u ^ 2) + (E 1 u ^ 3 * E 2 u ^ 2 * E 3 u) + (E 1 u ^ 3 * E 2 u ^ 3) + ((2 : ℝ) * (u * E 1 u ^ 3)) + (u * E 1 u ^ 3 * E 2 u) - (u * E 1 u ^ 3 * E 2 u * E 3 u) - (u * E 1 u ^ 3 * E 2 u ^ 2) + (u * E 1 u ^ 3 * E 2 u ^ 2 * E 3 u) + (u * E 1 u ^ 3 * E 2 u ^ 3) + (u * E 1 u ^ 4 * E 2 u ^ 3)) / (E 1 u ^ 2 * E 2 u ^ 2 * E 3 u) :=
  deriv_QrefCore4_val u

/-- **Closed form of `Q̃₄''`** (34 monomials over `E₁²E₂²E₃`). -/
theorem deriv2_QrefCore4_closedForm {u : ℝ} (_hu : 0 < u) :
    deriv (deriv QrefCore4) u =
      ((0 : ℝ) - (4 : ℝ) - ((6 : ℝ) * (E 1 u)) - ((3 : ℝ) * (E 1 u * E 2 u)) + (E 1 u * E 2 u * E 3 u) - ((4 : ℝ) * (E 1 u ^ 2)) - ((3 : ℝ) * (E 1 u ^ 2 * E 2 u)) + (E 1 u ^ 2 * E 2 u * E 3 u) - (E 1 u ^ 2 * E 2 u ^ 2) + ((6 : ℝ) * (E 1 u ^ 3)) + ((3 : ℝ) * (E 1 u ^ 3 * E 2 u)) - ((2 : ℝ) * (E 1 u ^ 3 * E 2 u * E 3 u)) - ((2 : ℝ) * (E 1 u ^ 3 * E 2 u ^ 2)) + ((2 : ℝ) * (E 1 u ^ 3 * E 2 u ^ 2 * E 3 u)) + ((3 : ℝ) * (E 1 u ^ 3 * E 2 u ^ 3)) - ((4 : ℝ) * (E 1 u ^ 4)) - ((3 : ℝ) * (E 1 u ^ 4 * E 2 u)) + (E 1 u ^ 4 * E 2 u * E 3 u) - (E 1 u ^ 4 * E 2 u ^ 2) + ((3 : ℝ) * (E 1 u ^ 4 * E 2 u ^ 3)) - (E 1 u ^ 4 * E 2 u ^ 4) + ((2 : ℝ) * (u * E 1 u ^ 3)) + (u * E 1 u ^ 3 * E 2 u) - (u * E 1 u ^ 3 * E 2 u * E 3 u) - (u * E 1 u ^ 3 * E 2 u ^ 2) + (u * E 1 u ^ 3 * E 2 u ^ 2 * E 3 u) + (u * E 1 u ^ 3 * E 2 u ^ 3) - ((4 : ℝ) * (u * E 1 u ^ 4)) - ((3 : ℝ) * (u * E 1 u ^ 4 * E 2 u)) + (u * E 1 u ^ 4 * E 2 u * E 3 u) - (u * E 1 u ^ 4 * E 2 u ^ 2) + ((4 : ℝ) * (u * E 1 u ^ 4 * E 2 u ^ 3)) - (u * E 1 u ^ 4 * E 2 u ^ 4) + (u * E 1 u ^ 5 * E 2 u ^ 3) - (u * E 1 u ^ 5 * E 2 u ^ 4)) / (E 1 u ^ 2 * E 2 u ^ 2 * E 3 u) :=
  deriv2_QrefCore4_val u

/-- **Closed form of `Q̃₃`** (20 monomials over `E₁³E₂²E₃`). -/
theorem QrefCore3_closedForm {u : ℝ} (_hu : 0 < u) :
    QrefCore3 u =
      ((0 : ℝ) + (2 : ℝ) + ((2 : ℝ) * (E 1 u)) + (E 1 u * E 2 u) - (E 1 u * E 2 u * E 3 u) - (E 1 u ^ 2) - (E 1 u ^ 2 * E 2 u ^ 2) + (E 1 u ^ 2 * E 2 u ^ 2 * E 3 u) + ((2 : ℝ) * (E 1 u ^ 3)) + (E 1 u ^ 3 * E 2 u) - (E 1 u ^ 3 * E 2 u * E 3 u) - (E 1 u ^ 3 * E 2 u ^ 2) + (E 1 u ^ 3 * E 2 u ^ 2 * E 3 u) + (E 1 u ^ 3 * E 2 u ^ 3) + ((2 : ℝ) * (u * E 1 u ^ 3)) + (u * E 1 u ^ 3 * E 2 u) - (u * E 1 u ^ 3 * E 2 u * E 3 u) - (u * E 1 u ^ 3 * E 2 u ^ 2) + (u * E 1 u ^ 3 * E 2 u ^ 2 * E 3 u) + (u * E 1 u ^ 3 * E 2 u ^ 3) + (u * E 1 u ^ 4 * E 2 u ^ 3)) / (E 1 u ^ 3 * E 2 u ^ 2 * E 3 u) :=
  QrefCore3_val u

/-! ## Grouped closed forms (for the curvature / slope-matching certificates)

The `Q̃₄'` / `Q̃₄''` closed forms rewritten as a decoupled leading part plus a
remainder over `E₁²E₂²E₃`.  Both are pure algebraic identities (valid for all
`u` with `E_k ≠ 0`), factored out here so their heavy `field_simp; ring` is
elaborated once — every high/low curvature and slope-matching lemma reuses them
instead of re-running the `rw [..._closedForm]; field_simp; ring` derivation. -/

set_option maxHeartbeats 1200000 in
/-- **Grouped closed form of `Q̃₄'`**: a decoupled leading part plus a remainder
over `E₁²E₂²E₃`. -/
theorem cert_grouped_deriv_QrefCore4 {u : ℝ} (hu0 : 0 < u) :
    deriv QrefCore4 u
      = (1 + E 1 u + u * E 1 u - E 1 u / E 2 u - u * E 1 u / E 2 u - 1 / (E 1 u * E 2 u))
        + (2 + 2 * E 1 u + E 1 u * E 2 u - E 1 u ^ 2 - E 1 u ^ 2 * E 2 u ^ 2
            + 2 * E 1 u ^ 3 + E 1 u ^ 3 * E 2 u - E 1 u ^ 3 * E 2 u ^ 2 + E 1 u ^ 3 * E 2 u ^ 3
            + 2 * u * E 1 u ^ 3 + u * E 1 u ^ 3 * E 2 u - u * E 1 u ^ 3 * E 2 u ^ 2
            + u * E 1 u ^ 3 * E 2 u ^ 3 + u * E 1 u ^ 4 * E 2 u ^ 3)
          / (E 1 u ^ 2 * E 2 u ^ 2 * E 3 u) := by
  have h1 : E 1 u ≠ 0 := (E_pos_of_one_le (j := 1) (by norm_num) u).ne'
  have h2 : E 2 u ≠ 0 := (E_pos_of_one_le (j := 2) (by norm_num) u).ne'
  have h3 : E 3 u ≠ 0 := (E_pos_of_one_le (j := 3) (by norm_num) u).ne'
  rw [deriv_QrefCore4_closedForm hu0]
  field_simp
  ring

set_option maxHeartbeats 1200000 in
/-- **Grouped closed form of `Q̃₄''`**: leading part plus remainder over
`E₁²E₂²E₃`. -/
theorem cert_grouped_deriv2_QrefCore4 {u : ℝ} (hu0 : 0 < u) :
    deriv (deriv QrefCore4) u
      = (1 / (E 1 u * E 2 u) + 1 / E 2 u - 2 * (E 1 u / E 2 u) + 2 * E 1 u + E 1 u ^ 2 / E 2 u
          - u * E 1 u / E 2 u + u * E 1 u + u * E 1 u ^ 2 / E 2 u)
        + ((6 * E 1 u ^ 3 + 3 * E 1 u ^ 3 * E 2 u + 3 * E 1 u ^ 3 * E 2 u ^ 3
            + 3 * E 1 u ^ 4 * E 2 u ^ 3 + 2 * u * E 1 u ^ 3 + u * E 1 u ^ 3 * E 2 u
            + u * E 1 u ^ 3 * E 2 u ^ 3 + 4 * u * E 1 u ^ 4 * E 2 u ^ 3 + u * E 1 u ^ 5 * E 2 u ^ 3)
          - (4 + 6 * E 1 u + 3 * E 1 u * E 2 u + 4 * E 1 u ^ 2 + 3 * E 1 u ^ 2 * E 2 u
            + E 1 u ^ 2 * E 2 u ^ 2 + 2 * E 1 u ^ 3 * E 2 u ^ 2 + 4 * E 1 u ^ 4 + 3 * E 1 u ^ 4 * E 2 u
            + E 1 u ^ 4 * E 2 u ^ 2 + E 1 u ^ 4 * E 2 u ^ 4 + u * E 1 u ^ 3 * E 2 u ^ 2
            + 4 * u * E 1 u ^ 4 + 3 * u * E 1 u ^ 4 * E 2 u + u * E 1 u ^ 4 * E 2 u ^ 2
            + u * E 1 u ^ 4 * E 2 u ^ 4 + u * E 1 u ^ 5 * E 2 u ^ 4))
          / (E 1 u ^ 2 * E 2 u ^ 2 * E 3 u) := by
  have h1 : E 1 u ≠ 0 := (E_pos_of_one_le (j := 1) (by norm_num) u).ne'
  have h2 : E 2 u ≠ 0 := (E_pos_of_one_le (j := 2) (by norm_num) u).ne'
  have h3 : E 3 u ≠ 0 := (E_pos_of_one_le (j := 3) (by norm_num) u).ne'
  rw [deriv2_QrefCore4_closedForm hu0]
  field_simp
  ring

end Erdos320
