import Erdos320.Defs.LogCount
import Erdos320.Lemmas.SBasic

/-!
# Bookkeeping for `N = ⌊e^X⌋`

The averaging relation (`prop:averaging-relation`) works with `N = ⌊e^X⌋` and
freely interchanges `e^X` with `N` and `X` with `log N`; the paper notes in
`prop:averaging-relation` that "In the proof we write `N = ⌊e^X⌋` and
temporarily normalize by `X/N` rather than `X/e^X`; their difference is
exponentially smaller than the stated error".  This file makes those
interchanges exact:

* two-sided floor bounds `e^X/2 ≤ N ≤ e^X` and `1 ≤ N` (for `X ≥ 1`),
* `X − 1/N ≤ log N ≤ X`,
* the normalization bridge `F(e^X) = (X/e^X)·g(N)` and its comparison with
  the §4 proof's preferred normalization `(X/N)·g(N)`.
-/

namespace Erdos320

/-- For `X ≥ 1`, the floor of `e^X` is at least `1`. -/
theorem one_le_expFloor {X : ℝ} (hX : 1 ≤ X) : 1 ≤ ⌊Real.exp X⌋₊ := by
  have h : (1 : ℝ) ≤ Real.exp X := by
    calc (1 : ℝ) ≤ X := hX
    _ ≤ Real.exp X := by linarith [Real.add_one_le_exp X]
  exact (Nat.le_floor_iff (Real.exp_pos X).le).mpr (by exact_mod_cast h)

theorem expFloor_le_exp (X : ℝ) : (⌊Real.exp X⌋₊ : ℝ) ≤ Real.exp X :=
  Nat.floor_le (Real.exp_pos X).le

/-- For `X ≥ 1`, `e^X/2 ≤ ⌊e^X⌋` (the floor loses at most a factor two,
generously). -/
theorem exp_div_two_le_expFloor {X : ℝ} (hX : 1 ≤ X) :
    Real.exp X / 2 ≤ (⌊Real.exp X⌋₊ : ℝ) := by
  have h2 : (2 : ℝ) ≤ Real.exp X := by linarith [Real.add_one_le_exp X]
  have hfloor : Real.exp X - 1 ≤ (⌊Real.exp X⌋₊ : ℝ) := by
    linarith [Nat.sub_one_lt_floor (Real.exp X)]
  linarith

/-- `log ⌊e^X⌋ ≤ X` for `X ≥ 1`. -/
theorem log_expFloor_le {X : ℝ} (hX : 1 ≤ X) : Real.log ⌊Real.exp X⌋₊ ≤ X := by
  have hN1 : (1 : ℝ) ≤ (⌊Real.exp X⌋₊ : ℝ) := by exact_mod_cast one_le_expFloor hX
  calc Real.log ⌊Real.exp X⌋₊ ≤ Real.log (Real.exp X) :=
        Real.log_le_log (by linarith) (expFloor_le_exp X)
  _ = X := Real.log_exp X

/-- `X − 1/N ≤ log N` for `N = ⌊e^X⌋`, `X ≥ 1`: the floor costs at most
`log(1 + 1/N) ≤ 1/N` of the exponent. -/
theorem log_expFloor_ge {X : ℝ} (hX : 1 ≤ X) :
    X - 1 / (⌊Real.exp X⌋₊ : ℝ) ≤ Real.log ⌊Real.exp X⌋₊ := by
  set N := ⌊Real.exp X⌋₊ with hN
  have hN1 : 1 ≤ N := one_le_expFloor hX
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hlt : Real.exp X < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlog : X < Real.log ((N : ℝ) + 1) := by
    rw [← Real.log_exp X]
    exact Real.log_lt_log (Real.exp_pos X) hlt
  have hsplit : Real.log ((N : ℝ) + 1) = Real.log N + Real.log (1 + 1 / N) := by
    rw [← Real.log_mul hNpos.ne' (by positivity)]
    congr 1
    field_simp
  have hbound : Real.log (1 + 1 / (N : ℝ)) ≤ 1 / N := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / N by positivity)
    linarith
  linarith

/-- The exact normalization at `e^X`: `F(e^X) = (X/e^X)·g(⌊e^X⌋)`. -/
theorem FReal_exp_eq (X : ℝ) :
    FReal (Real.exp X) = X / Real.exp X * g ⌊Real.exp X⌋₊ := by
  rw [FReal, Real.log_exp]

/-- Switching the §4 proof's normalization `(X/N)·g(N)` for the exact
`F(e^X) = (X/e^X)·g(N)` costs at most `X·log 2/e^X` (exponentially
negligible). -/
theorem abs_FReal_exp_sub_div_floor {X : ℝ} (hX : 1 ≤ X) :
    |FReal (Real.exp X) - X / (⌊Real.exp X⌋₊ : ℝ) * g ⌊Real.exp X⌋₊|
      ≤ X * Real.log 2 / Real.exp X := by
  set N := ⌊Real.exp X⌋₊ with hN
  have hN1 : 1 ≤ N := one_le_expFloor hX
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hEpos : (0 : ℝ) < Real.exp X := Real.exp_pos X
  have hNE : (N : ℝ) ≤ Real.exp X := expFloor_le_exp X
  have hgap : Real.exp X - (N : ℝ) ≤ 1 := by
    linarith [Nat.sub_one_lt_floor (Real.exp X)]
  have hg0 : 0 ≤ g N := g_nonneg N
  have hgN : g N ≤ (N : ℝ) * Real.log 2 := g_le_mul_log_two N
  have hX0 : 0 < X := by linarith
  rw [FReal_exp_eq]
  have hkey : X / Real.exp X * g N - X / (N : ℝ) * g N
      = -(X * g N * ((Real.exp X - N) / ((N : ℝ) * Real.exp X))) := by
    field_simp
    ring
  have hquot0 : 0 ≤ (Real.exp X - (N : ℝ)) / ((N : ℝ) * Real.exp X) :=
    div_nonneg (by linarith) (by positivity)
  rw [hkey, abs_neg,
    abs_of_nonneg (mul_nonneg (mul_nonneg hX0.le hg0) hquot0)]
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hab : X * g N ≤ X * ((N : ℝ) * Real.log 2) :=
    mul_le_mul_of_nonneg_left hgN hX0.le
  have hcd : (Real.exp X - (N : ℝ)) / ((N : ℝ) * Real.exp X)
      ≤ 1 / ((N : ℝ) * Real.exp X) :=
    div_le_div_of_nonneg_right hgap (by positivity)
  calc X * g N * ((Real.exp X - (N : ℝ)) / ((N : ℝ) * Real.exp X))
      ≤ X * ((N : ℝ) * Real.log 2) * (1 / ((N : ℝ) * Real.exp X)) :=
        mul_le_mul hab hcd hquot0
          (mul_nonneg hX0.le (mul_nonneg hNpos.le hlog2))
  _ = X * Real.log 2 / Real.exp X := by field_simp

end Erdos320
