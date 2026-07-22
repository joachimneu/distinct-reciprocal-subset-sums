import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Elementary series estimates for `log t / t` and `log t / t²`

Sum-vs-integral comparisons for the concrete decreasing integrands
`log t / t` and `log t / t²`, consumed by the paper's
`prop:averaging-relation` and by the explicit averaging-error bounds
`lem:explicit-low-averaging` / `cor:explicit-high-averaging` (matching the
formula `∑_{k=2}^{A} log k / k ≤ ½ log²A + O(1)`).

Contents:

* **Antitonicity** of `log t / t` and `log t / (t·t)` on `[e, ∞)`
  (`log_div_antitoneOn`, `log_div_sq_antitoneOn`), thin wrappers over Mathlib's
  `Real.log_div_self_antitoneOn` and `Real.log_div_self_rpow_antitoneOn`.
* **Closed-form integrals** `∫ log t/t = log²t/2` and
  `∫ log t/t² = −(log t + 1)/t` on positive intervals
  (`integral_log_div_self`, `integral_log_div_sq`).
* **Partial-sum bound** `∑_{m=1}^{A} log(m+1)/(m+1) ≤ log²(A+1)/2 + 1`
  (`sum_log_succ_div_succ_le`).
* **Tail bound** `∑_{m=A+1}^{B} log(m+1)/(m+1)² ≤ (log(A+1)+1)/(A+1)` for
  `A ≥ 3` (`sum_log_div_sq_tail_le`).
* **Harmonic-type bounds** `∑_{m=1}^{A} 1/m ≤ 1 + log A`
  (`sum_one_div_le_log`, from Mathlib's `harmonic_le_one_add_log`) and
  `∑_{m=A+1}^{B} 1/m² ≤ 1/A` (`sum_one_div_Ioc_le`, from Mathlib's
  `sum_Ioc_inv_sq_le_sub`).
* **Consumer combination** `∑_{m=1}^{M} (log 2 · log(m+1))/(m+1)
  ≤ log 2 · (log²(M+1)/2 + 1)` (`sum_min_cap_error_le`).
-/

namespace Erdos320

/-! ## Antitonicity of `log t / t` and `log t / t²` on `[e, ∞)` -/

/-- `t ↦ log t / t` is antitone on `[e, ∞)`.  This is Mathlib's
`Real.log_div_self_antitoneOn`. -/
theorem log_div_antitoneOn :
    AntitoneOn (fun t : ℝ => Real.log t / t) (Set.Ici (Real.exp 1)) :=
  Real.log_div_self_antitoneOn

/-- `t ↦ log t / (t·t)` is antitone on `[e, ∞)`.  This is Mathlib's
`Real.log_div_self_rpow_antitoneOn` at `a = 2` (whose domain `[e^(1/2), ∞)` is
wider than `[e, ∞)`), with `t^(2:ℝ)` rewritten to `t·t`. -/
theorem log_div_sq_antitoneOn :
    AntitoneOn (fun t : ℝ => Real.log t / (t * t)) (Set.Ici (Real.exp 1)) := by
  have h := (Real.log_div_self_rpow_antitoneOn (a := 2) (by norm_num)).mono
    (Set.Ici_subset_Ici.mpr (Real.exp_le_exp.mpr (by norm_num : (2 : ℝ)⁻¹ ≤ 1)))
  refine h.congr fun t _ => ?_
  simp only [Real.rpow_two, pow_two]

/-! ## Closed-form integrals -/

/-- `log t / t` is interval-integrable on any interval with positive left
endpoint. -/
theorem intervalIntegrable_log_div_self {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => Real.log t / t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  have hne : ∀ t ∈ Set.Icc a b, t ≠ 0 := fun t ht => (ha.trans_le ht.1).ne'
  exact (Real.continuousOn_log.mono fun t ht =>
    Set.mem_compl_singleton_iff.mpr (hne t ht)).div continuousOn_id hne

/-- `log t / (t·t)` is interval-integrable on any interval with positive left
endpoint. -/
theorem intervalIntegrable_log_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => Real.log t / (t * t))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  have hne : ∀ t ∈ Set.Icc a b, t * t ≠ 0 := fun t ht =>
    mul_ne_zero (ha.trans_le ht.1).ne' (ha.trans_le ht.1).ne'
  exact (Real.continuousOn_log.mono fun t ht =>
    Set.mem_compl_singleton_iff.mpr (ha.trans_le ht.1).ne').div
    (continuousOn_id.mul continuousOn_id) hne

/-- `∫_a^b log t / t dt = log²b/2 − log²a/2` for `0 < a ≤ b`. -/
theorem integral_log_div_self {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, Real.log t / t
      = Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun u => Real.log u * Real.log u / 2) (Real.log t / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have htne : t ≠ 0 := (ha.trans_le ht.1).ne'
    have h : HasDerivAt (fun u => Real.log u * Real.log u / 2)
        ((t⁻¹ * Real.log t + Real.log t * t⁻¹) / 2) t :=
      ((Real.hasDerivAt_log htne).fun_mul
        (Real.hasDerivAt_log htne)).div_const 2
    have hval : (t⁻¹ * Real.log t + Real.log t * t⁻¹) / 2
        = Real.log t / t := by ring
    rw [← hval]
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_log_div_self ha hab)]
  ring

/-- `∫_a^b log t / t² dt = (log a + 1)/a − (log b + 1)/b` for `0 < a ≤ b`
(antiderivative `−(log t + 1)/t`). -/
theorem integral_log_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, Real.log t / (t * t)
      = (Real.log a + 1) / a - (Real.log b + 1) / b := by
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun u => -((Real.log u + 1) / u))
        (Real.log t / (t * t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have htne : t ≠ 0 := ht0.ne'
    have hnum : HasDerivAt (fun u => Real.log u + 1) t⁻¹ t :=
      (Real.hasDerivAt_log htne).add_const 1
    have h : HasDerivAt (fun u => -((Real.log u + 1) / u))
        (-((t⁻¹ * t - (Real.log t + 1) * 1) / t ^ 2)) t :=
      (hnum.fun_div (hasDerivAt_id' t) htne).fun_neg
    have hval : -((t⁻¹ * t - (Real.log t + 1) * 1) / t ^ 2)
        = Real.log t / (t * t) := by
      rw [inv_mul_cancel₀ htne, pow_two]
      ring
    rw [← hval]
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_log_div_sq ha hab)]
  ring

/-! ## The main partial-sum bound for `log(m+1)/(m+1)` -/

/-- **Main partial-sum bound** (the manuscript's
`∑_{k=2}^{A+1} log k / k ≤ ½ log²(A+1) + 1`, the `½ log²(T+1) + 1` term in the
upper estimate of `lem:explicit-low-averaging`): the sum of `log(m+1)/(m+1)`
over `1 ≤ m ≤ A` is at most `log²(A+1)/2 + 1`.  The terms `m = 1, 2`
contribute `log 2/2 + log 3/3 < 1` (the additive constant); the rest is
dominated by `∫_3^{A+1} log t / t dt ≤ log²(A+1)/2` by antitonicity of
`log t / t` on `[e, ∞)`. -/
theorem sum_log_succ_div_succ_le (A : ℕ) :
    ∑ m ∈ Finset.Icc 1 A, Real.log (m + 1) / (m + 1)
      ≤ Real.log (A + 1) ^ 2 / 2 + 1 := by
  rcases lt_or_ge A 2 with hA | hA
  · interval_cases A
    · rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty
        (by omega), Finset.sum_empty]
      norm_num [Real.log_one]
    · rw [Finset.Icc_self, Finset.sum_singleton]
      have h1 : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
        linarith
      have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      push_cast
      norm_num
      nlinarith [sq_nonneg (Real.log 2)]
  · have hsplit : Finset.Icc 1 A = Finset.Ioc 0 A := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hsplit, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le 2) hA]
    have hhead : ∑ m ∈ Finset.Ioc (0 : ℕ) 2, Real.log (m + 1) / (m + 1) ≤ 1 := by
      rw [show Finset.Ioc (0 : ℕ) 2 = ({1, 2} : Finset ℕ) by decide,
        Finset.sum_pair (by norm_num : (1:ℕ) ≠ 2)]
      have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
        have h34 : Real.log 3 ≤ Real.log 4 :=
          Real.log_le_log (by norm_num) (by norm_num)
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        linarith
      push_cast
      norm_num
      linarith
    have htail : ∑ m ∈ Finset.Ioc 2 A, Real.log (m + 1) / (m + 1)
        ≤ Real.log (A + 1) ^ 2 / 2 := by
      have hIoc : Finset.Ioc 2 A = Finset.Ico 3 (A + 1) := by
        ext x
        simp only [Finset.mem_Ioc, Finset.mem_Ico]
        omega
      have hmono : AntitoneOn (fun t : ℝ => Real.log t / t)
          (Set.Icc ((3 : ℕ) : ℝ) ((A + 1 : ℕ) : ℝ)) := by
        apply log_div_antitoneOn.mono
        intro t ht
        show Real.exp 1 ≤ t
        have h3t : ((3 : ℕ) : ℝ) ≤ t := ht.1
        have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
        linarith [Real.exp_one_lt_d9]
      have hA3 : (3 : ℕ) ≤ A + 1 := by omega
      calc ∑ m ∈ Finset.Ioc 2 A, Real.log (m + 1) / (m + 1)
          = ∑ m ∈ Finset.Ico 3 (A + 1),
              (fun t : ℝ => Real.log t / t) ((m + 1 : ℕ) : ℝ) := by
            rw [hIoc]
            exact Finset.sum_congr rfl fun m _ => by push_cast; ring
        _ ≤ ∫ x in ((3 : ℕ) : ℝ)..((A + 1 : ℕ) : ℝ), Real.log x / x :=
            hmono.sum_le_integral_Ico hA3
        _ = Real.log ((A + 1 : ℕ) : ℝ) ^ 2 / 2
              - Real.log ((3 : ℕ) : ℝ) ^ 2 / 2 :=
            integral_log_div_self (by positivity) (Nat.cast_le.mpr hA3)
        _ ≤ Real.log ((A : ℝ) + 1) ^ 2 / 2 := by
            have hcast : ((A + 1 : ℕ) : ℝ) = (A : ℝ) + 1 := by push_cast; ring
            rw [hcast]
            nlinarith [sq_nonneg (Real.log ((3 : ℕ) : ℝ))]
    linarith

/-! ## Tail bound for `log(m+1)/(m+1)²` -/

/-- **Tail bound** for the series `∑ log(m+1)/(m+1)²`: for `A ≥ 3`,
`∑_{m=A+1}^{B} log(m+1)/((m+1)(m+1)) ≤ (log(A+1) + 1)/(A+1)`, uniformly in
`B` — the finite-`B` form of `∫_{A+1}^∞ log t / t² dt = (log(A+1)+1)/(A+1)`,
via antitonicity of `log t / t²` on `[e, ∞)` (here `A + 1 ≥ 4 > e`). -/
theorem sum_log_div_sq_tail_le (A B : ℕ) (hA : 3 ≤ A) :
    ∑ m ∈ Finset.Ioc A B, Real.log (m + 1) / ((m + 1) * (m + 1))
      ≤ (Real.log (A + 1) + 1) / (A + 1) := by
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  have hlogA : 0 ≤ Real.log ((A : ℝ) + 1) := Real.log_nonneg (by linarith)
  rcases le_or_gt B A with hBA | hAB
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    apply div_nonneg (by linarith) (by linarith)
  · have hIoc : Finset.Ioc A B = Finset.Ico (A + 1) (B + 1) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    have hmono : AntitoneOn (fun t : ℝ => Real.log t / (t * t))
        (Set.Icc ((A + 1 : ℕ) : ℝ) ((B + 1 : ℕ) : ℝ)) := by
      apply log_div_sq_antitoneOn.mono
      intro t ht
      show Real.exp 1 ≤ t
      have h4t : ((4 : ℕ) : ℝ) ≤ ((A + 1 : ℕ) : ℝ) :=
        Nat.cast_le.mpr (by omega)
      have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
      linarith [Real.exp_one_lt_d9, ht.1]
    have hstep : A + 1 ≤ B + 1 := by omega
    calc ∑ m ∈ Finset.Ioc A B, Real.log (m + 1) / ((m + 1) * (m + 1))
        = ∑ m ∈ Finset.Ico (A + 1) (B + 1),
            (fun t : ℝ => Real.log t / (t * t)) ((m + 1 : ℕ) : ℝ) := by
          rw [hIoc]
          exact Finset.sum_congr rfl fun m _ => by push_cast; ring
      _ ≤ ∫ x in ((A + 1 : ℕ) : ℝ)..((B + 1 : ℕ) : ℝ),
            Real.log x / (x * x) :=
          hmono.sum_le_integral_Ico hstep
      _ = (Real.log ((A + 1 : ℕ) : ℝ) + 1) / ((A + 1 : ℕ) : ℝ)
            - (Real.log ((B + 1 : ℕ) : ℝ) + 1) / ((B + 1 : ℕ) : ℝ) :=
          integral_log_div_sq (by positivity) (Nat.cast_le.mpr hstep)
      _ ≤ (Real.log ((A : ℝ) + 1) + 1) / ((A : ℝ) + 1) := by
          have hcastA : ((A + 1 : ℕ) : ℝ) = (A : ℝ) + 1 := by push_cast; ring
          have hcastB : ((B + 1 : ℕ) : ℝ) = (B : ℝ) + 1 := by push_cast; ring
          rw [hcastA, hcastB]
          have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
          have hlogB : 0 ≤ Real.log ((B : ℝ) + 1) :=
            Real.log_nonneg (by linarith)
          have hBterm : 0 ≤ (Real.log ((B : ℝ) + 1) + 1) / ((B : ℝ) + 1) :=
            div_nonneg (by linarith) (by linarith)
          linarith

/-! ## Harmonic-type bounds -/

/-- `∑_{m=1}^{A} 1/m ≤ 1 + log A`, the real-valued form of Mathlib's
`harmonic_le_one_add_log`. -/
theorem sum_one_div_le_log (A : ℕ) :
    ∑ m ∈ Finset.Icc 1 A, (1 : ℝ) / m ≤ 1 + Real.log A := by
  have h := harmonic_le_one_add_log A
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- `∑_{m=A+1}^{B} 1/m² ≤ 1/A` for `A ≥ 1`, uniformly in `B` (telescoping
`1/m² ≤ 1/(m−1) − 1/m`; via Mathlib's `sum_Ioc_inv_sq_le_sub`). -/
theorem sum_one_div_Ioc_le (A B : ℕ) (hA : 1 ≤ A) :
    ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / (m * m) ≤ 1 / A := by
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  rcases le_or_gt B A with hBA | hAB
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : A ≠ 0) hAB.le
    have hBpos : (0 : ℝ) < (B : ℝ) := by
      have hB : 0 < B := by omega
      exact_mod_cast hB
    have hsum : ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / (m * m)
        = ∑ i ∈ Finset.Ioc A B, (((i : ℝ)) ^ 2)⁻¹ :=
      Finset.sum_congr rfl fun m _ => by rw [one_div, sq]
    rw [hsum, one_div]
    have hBinv : (0 : ℝ) < ((B : ℝ))⁻¹ := by positivity
    linarith

/-! ## Combination form for the consumer -/

/-- Combination form for the `min`-cap error of `lem:explicit-low-averaging`:
`∑_{m=1}^{M} (log 2 · log(m+1))/(m+1) ≤ log 2 · (log²(M+1)/2 + 1)`. -/
theorem sum_min_cap_error_le (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, Real.log 2 * Real.log (m + 1) / (m + 1)
      ≤ Real.log 2 * (Real.log (M + 1) ^ 2 / 2 + 1) := by
  have h := sum_log_succ_div_succ_le M
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc ∑ m ∈ Finset.Icc 1 M, Real.log 2 * Real.log (m + 1) / (m + 1)
      = Real.log 2 * ∑ m ∈ Finset.Icc 1 M, Real.log (m + 1) / (m + 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ Real.log 2 * (Real.log (M + 1) ^ 2 / 2 + 1) :=
        mul_le_mul_of_nonneg_left h hlog2

end Erdos320
