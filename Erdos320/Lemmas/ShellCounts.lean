import Erdos320.Assumptions
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt

/-!
# Prime-interval counting toolkit for the shell estimates

Generic two-sided estimates for the number of primes in a real interval
`(a, b]` with `2 ≤ a ≤ b`, derived from the Fiori–Kadiri–Swidinsky input
`fioriKadiriSwidinsky_pi_approx` (eq. `FKS-pi` in the manuscript), plus the
decay estimates for the FKS error term that the manuscript's shell-count
arguments consume:

* eq. `prime-shell-sum` (inside the proof of `prop:averaging-relation`):
  the shell count `P_m = π(N/m) − π(N/(m+1))` is `∫_{y_m}^{x_m} dt/log t`
  up to `O(Err_π(x_m) + Err_π(y_m))` — here `abs_primeInterval_sub_Li` and
  `Li_gap_bounds`;
* eq. `explicit-shell-count` (inside `lem:explicit-low-averaging`): the same
  count with a fully explicit, astronomically small error once
  `log t ≥ 9·10⁶` — here `fksError_le_tiny`.

The shell-specific normalization (shells `⌊N/p⌋ = m`, the `X/N` scaling)
happens in later consumer files; this file only counts primes on intervals.
-/

namespace Erdos320

/-- The Fiori–Kadiri–Swidinsky error majorant
`Err_π(t) = 9.2211 · t · √(log t) · exp(−0.8476·√(log t))`, the right-hand
side of eq. `FKS-pi` (`fioriKadiriSwidinsky_pi_approx`).  The manuscript
writes this `Err_π(t)` there and consumes it in the proof of
`prop:averaging-relation` (eq. `prime-shell-sum`). -/
noncomputable def fksError (t : ℝ) : ℝ :=
  9.2211 * t * Real.sqrt (Real.log t) * Real.exp (-0.8476 * Real.sqrt (Real.log t))

/-- The FKS error majorant is nonnegative for `t ≥ 0` (for `t < 1` the
`√(log t)` factor is `0` by the junk-value convention, so no lower bound on
`t` beyond `0 ≤ t` is needed). -/
theorem fksError_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ fksError t := by
  unfold fksError
  have h1 : (0 : ℝ) ≤ 9.2211 * t := by linarith
  exact mul_nonneg (mul_nonneg h1 (Real.sqrt_nonneg _)) (Real.exp_pos _).le

/-- `π` (on real arguments) is monotone: more room, at least as many primes. -/
theorem primePi_mono : Monotone primePi := fun _ _ h =>
  Nat.monotone_primeCounting (Nat.floor_mono h)

/-- `t ↦ 1/log t` is interval-integrable on any interval with both endpoints
`≥ 2` (there `log` is continuous and bounded away from `0`). -/
theorem intervalIntegrable_one_div_log {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b := by
  have hmem : ∀ t ∈ Set.uIcc a b, 2 ≤ t := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with h | h
    · linarith [h.1]
    · linarith [h.1]
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · apply Real.continuousOn_log.mono
    intro t ht
    have h2t := hmem t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h0
    rw [h0] at h2t
    norm_num at h2t
  · intro t ht
    exact (Real.log_pos (by linarith [hmem t ht])).ne'

/-- Difference identity for the logarithmic integral: for `2 ≤ a ≤ b`,
`Li(b) − Li(a) = ∫_a^b dt/log t`.  This is the form in which `Li` enters the
shell counts of eq. `prime-shell-sum`. -/
theorem Li_sub_Li {a b : ℝ} (h2 : 2 ≤ a) (hab : a ≤ b) :
    Li b - Li a = ∫ t in a..b, 1 / Real.log t := by
  have hb : (2 : ℝ) ≤ b := h2.trans hab
  have h1 : IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume 2 a :=
    intervalIntegrable_one_div_log le_rfl h2
  have h2' : IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b :=
    intervalIntegrable_one_div_log h2 hb
  have h3 := intervalIntegral.integral_add_adjacent_intervals h1 h2'
  unfold Li
  linarith [h3]

/-- Two-sided bound on a gap of the logarithmic integral by the endpoint
values of the integrand: `(b−a)/log b ≤ Li(b) − Li(a) ≤ (b−a)/log a` for
`2 ≤ a ≤ b`.  This is the "bounding the integrand `1/log t` at the shell
endpoints" step of eq. `explicit-shell-count`, and the
`log t = X + O(log(m+1))` step of eq. `prime-shell-sum`. -/
theorem Li_gap_bounds {a b : ℝ} (h2 : 2 ≤ a) (hab : a ≤ b) :
    (b - a) / Real.log b ≤ Li b - Li a ∧ Li b - Li a ≤ (b - a) / Real.log a := by
  have hb : (2 : ℝ) ≤ b := h2.trans hab
  have hloga : 0 < Real.log a := Real.log_pos (by linarith)
  have hint : IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b :=
    intervalIntegrable_one_div_log h2 hb
  rw [Li_sub_Li h2 hab]
  constructor
  · calc (b - a) / Real.log b
        = ∫ _ in a..b, 1 / Real.log b := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
      _ ≤ ∫ t in a..b, 1 / Real.log t := by
          apply intervalIntegral.integral_mono_on hab intervalIntegrable_const hint
          intro y hy
          have hy1 : a ≤ y := hy.1
          have hy2 : y ≤ b := hy.2
          have hly : 0 < Real.log y := Real.log_pos (by linarith)
          exact one_div_le_one_div_of_le hly (Real.log_le_log (by linarith) hy2)
  · calc (∫ t in a..b, 1 / Real.log t)
        ≤ ∫ _ in a..b, 1 / Real.log a := by
          apply intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
          intro y hy
          have hy1 : a ≤ y := hy.1
          exact one_div_le_one_div_of_le hloga (Real.log_le_log (by linarith) hy1)
      _ = (b - a) / Real.log a := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring

/-- **FKS interval count.**  For `2 ≤ a ≤ b`, the number of primes in `(a, b]`
differs from `Li(b) − Li(a)` by at most `Err_π(a) + Err_π(b)`.  This is exactly the
`P_m = ∫_{y_m}^{x_m} dt/log t + O(Err_π(x_m) + Err_π(y_m))` step of
eq. `prime-shell-sum` (and of eq. `explicit-shell-count`), obtained by
triangle inequality from eq. `FKS-pi` at both endpoints. -/
theorem abs_primeInterval_sub_Li {a b : ℝ} (h2 : 2 ≤ a) (hab : a ≤ b) :
    |((primePi b : ℝ) - (primePi a : ℝ)) - (Li b - Li a)| ≤ fksError a + fksError b := by
  have hb : (2 : ℝ) ≤ b := h2.trans hab
  have Ha := fioriKadiriSwidinsky_pi_approx a h2
  have Hb := fioriKadiriSwidinsky_pi_approx b hb
  have hkey : ((primePi b : ℝ) - (primePi a : ℝ)) - (Li b - Li a)
      = ((primePi b : ℝ) - Li b) - ((primePi a : ℝ) - Li a) := by ring
  rw [hkey]
  calc |((primePi b : ℝ) - Li b) - ((primePi a : ℝ) - Li a)|
      = |((primePi b : ℝ) - Li b) + -((primePi a : ℝ) - Li a)| := by
        rw [sub_eq_add_neg]
    _ ≤ |(primePi b : ℝ) - Li b| + |-((primePi a : ℝ) - Li a)| := abs_add_le _ _
    _ = |(primePi b : ℝ) - Li b| + |(primePi a : ℝ) - Li a| := by rw [abs_neg]
    _ ≤ fksError a + fksError b := by
        unfold fksError
        linarith

/-- Lower prime-interval count: for `2 ≤ a ≤ b`,
`π(b) − π(a) ≥ (b−a)/log b − Err_π(a) − Err_π(b)`.  Lower half of
eq. `explicit-shell-count` (`c_m − ε_m ≤ (X/N)·P_m` after normalization). -/
theorem primeInterval_lower {a b : ℝ} (h2 : 2 ≤ a) (hab : a ≤ b) :
    (b - a) / Real.log b - fksError a - fksError b ≤ (primePi b : ℝ) - (primePi a : ℝ) := by
  have h1 := abs_le.mp (abs_primeInterval_sub_Li h2 hab)
  have h2' := (Li_gap_bounds h2 hab).1
  linarith [h1.1]

/-- Upper prime-interval count: for `2 ≤ a ≤ b`,
`π(b) − π(a) ≤ (b−a)/log a + Err_π(a) + Err_π(b)`.  Upper half of
eq. `explicit-shell-count` (`(X/N)·P_m ≤ c_m·X/(X−log(m+1)) + ε_m` after
normalization). -/
theorem primeInterval_upper {a b : ℝ} (h2 : 2 ≤ a) (hab : a ≤ b) :
    (primePi b : ℝ) - (primePi a : ℝ) ≤ (b - a) / Real.log a + fksError a + fksError b := by
  have h1 := abs_le.mp (abs_primeInterval_sub_Li h2 hab)
  have h2' := (Li_gap_bounds h2 hab).2
  linarith [h1.2]

/-- Elementary exponential domination: `x ≤ exp(c·x)` once `x ≥ 2/c²`
(from `exp y ≥ 1 + y + y²/2` for `y ≥ 0`).  Helper for absorbing polynomial
factors into the exponential in the FKS error decay lemmas below. -/
theorem le_exp_mul_of_pos {c x : ℝ} (hc : 0 < c) (hx : 2 / c ^ 2 ≤ x) :
    x ≤ Real.exp (c * x) := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h2 : 2 ≤ x * c ^ 2 := by
    rw [div_le_iff₀ hc2] at hx
    linarith
  have hcx : (0 : ℝ) ≤ c * x := by positivity
  have h1 := Real.quadratic_le_exp_of_nonneg hcx
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) hx0.le, hcx, h1]

/-- Absorbing the `√(log t)` factor of the FKS error: once `log t ≥ 4·10⁶`,
`Err_π(t) ≤ 10·t·exp(−0.8·√(log t))`.  This is the manuscript's
`≪ X^{3/2}·exp(−0.8476·√(⋯)) ≪ ⋯ e^{−0.8√X}` absorption step in the
`Σ|ε_m|` estimate of eq. `prime-shell-sum` (and the analogous step in
`lem:explicit-low-averaging`), with an explicit threshold: `√(log t) ≥ 2000 ≥
2/0.0476²` makes `√(log t) ≤ exp(0.0476·√(log t))`. -/
theorem fksError_le_of_log_ge {t : ℝ} (ht : 0 ≤ t)
    (hlog : (4 * 10 ^ 6 : ℝ) ≤ Real.log t) :
    fksError t ≤ 10 * t * Real.exp (-0.8 * Real.sqrt (Real.log t)) := by
  set s := Real.sqrt (Real.log t) with hs_def
  have hs2000 : (2000 : ℝ) ≤ s := by
    rw [hs_def]
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hsexp : s ≤ Real.exp (0.0476 * s) := by
    apply le_exp_mul_of_pos (by norm_num : (0 : ℝ) < 0.0476)
    calc (2 : ℝ) / 0.0476 ^ 2 ≤ 2000 := by norm_num
      _ ≤ s := hs2000
  have hE1 : (0 : ℝ) < Real.exp (-0.8476 * s) := Real.exp_pos _
  have hsplit : Real.exp (0.0476 * s) * Real.exp (-0.8476 * s) = Real.exp (-0.8 * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h9t : (0 : ℝ) ≤ 9.2211 * t := by linarith
  have hfk : fksError t = 9.2211 * t * s * Real.exp (-0.8476 * s) := by
    rw [hs_def]
    rfl
  rw [hfk]
  calc 9.2211 * t * s * Real.exp (-0.8476 * s)
      ≤ 9.2211 * t * Real.exp (0.0476 * s) * Real.exp (-0.8476 * s) := by
        apply mul_le_mul_of_nonneg_right _ hE1.le
        exact mul_le_mul_of_nonneg_left hsexp h9t
    _ = 9.2211 * t * Real.exp (-0.8 * s) := by
        rw [mul_assoc, hsplit]
    _ ≤ 10 * t * Real.exp (-0.8 * s) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith

/-- **Explicit huge-range decay of the FKS error.**  Once `log t ≥ 9·10⁶`
(the certificate lemmas have `log Q > X − 34 ≥ 9 699 966`, see
`lem:explicit-low-averaging`), the FKS error is utterly negligible:
`Err_π(t) ≤ t/10¹⁰⁰`.  This backs the manuscript's remark for
eq. `explicit-shell-count` that "`Err_π(t)/t` is decreasing throughout this
range, and at every relevant shell endpoint `Err_π(t)/t ≤ 9.871·10⁻¹¹⁴³ <
10⁻¹¹⁴⁰`" (we certify the weaker but amply sufficient `10⁻¹⁰⁰` threshold
bound at every `t` in range, so we need neither the monotonicity claim nor
the endpoint values). -/
theorem fksError_le_tiny {t : ℝ} (ht : 0 ≤ t)
    (hlog : (9 * 10 ^ 6 : ℝ) ≤ Real.log t) :
    fksError t ≤ t / 10 ^ 100 := by
  have h4 : (4 * 10 ^ 6 : ℝ) ≤ Real.log t := by linarith
  have h1 := fksError_le_of_log_ge ht h4
  have hs3000 : (3000 : ℝ) ≤ Real.sqrt (Real.log t) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hmono : Real.exp (-0.8 * Real.sqrt (Real.log t)) ≤ Real.exp (-2400 : ℝ) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hexp2400 : (10 : ℝ) ^ 101 ≤ Real.exp 2400 := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (10 : ℝ) ^ 101 ≤ (10 : ℝ) ^ 102 := by gcongr <;> norm_num
      _ = ((10 : ℝ) ^ 3) ^ 34 := by rw [← pow_mul]
      _ ≤ ((2 : ℝ) ^ 10) ^ 34 := by gcongr; norm_num
      _ = (2 : ℝ) ^ 340 := by rw [← pow_mul]
      _ ≤ (2 : ℝ) ^ 2400 := by gcongr <;> norm_num
      _ ≤ Real.exp 1 ^ 2400 := by gcongr
      _ = Real.exp 2400 := by
          rw [← Real.exp_nat_mul]
          norm_num
  have hE0 : Real.exp (-2400 : ℝ) ≤ 1 / 10 ^ 101 := by
    have hmul : Real.exp (-2400 : ℝ) * Real.exp 2400 = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [mul_nonneg (Real.exp_pos (-2400 : ℝ)).le (sub_nonneg.mpr hexp2400), hmul]
  have h10t : (0 : ℝ) ≤ 10 * t := by linarith
  calc fksError t
      ≤ 10 * t * Real.exp (-0.8 * Real.sqrt (Real.log t)) := h1
    _ ≤ 10 * t * Real.exp (-2400 : ℝ) := mul_le_mul_of_nonneg_left hmono h10t
    _ ≤ 10 * t * (1 / 10 ^ 101) := mul_le_mul_of_nonneg_left hE0 h10t
    _ = t / 10 ^ 100 := by ring

/-- Chebyshev bound: `ϑ(x) ≤ (log 4)·x` for `x ≥ 0`, via Mathlib's
`Chebyshev.theta_le_log4_mul_x` (through the `chebyshevTheta_eq_theta`
bridge).  Used by the shell decomposition to bound the first prime-power
layer `ϑ(Q)` in eq. `shell-sum` / `prop:averaging-relation`. -/
theorem chebyshevTheta_le_log_four_mul {x : ℝ} (hx : 0 ≤ x) :
    chebyshevTheta x ≤ Real.log 4 * x := by
  rw [chebyshevTheta_eq_theta]
  exact Chebyshev.theta_le_log4_mul_x hx
