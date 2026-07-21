import Erdos320.Lemmas.SBasic
import Erdos320.Lemmas.ShellCounts
import Erdos320.Defs.RatToZMod
import Erdos320.Defs.PrimeCounting
import Erdos320.Assumptions
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The elementary threshold bracket (`lem:elementary-threshold`)

The manuscript's Lemma "Elementary threshold bracket", eq. `elementary-threshold`:
```
t / log 2  <  m_*(t)  <  4 t log (2t).
```

* The **lower bound** follows from the trivial `g(m) ≤ m log 2`
  (`g_le_mul_log_two`).  The paper states it for every `t > 0`; the proof in
  fact needs no positivity, so `mStar_lower` below is stated for every real `t`
  (a strictly stronger, still faithful statement).
* The **upper bound** rests on the paper's observation that "reductions modulo
  the primes `p ∈ (m/2, m]` show that their reciprocal subsets are all
  distinct, so `g(m) ≥ (π(m) − π(m/2)) log 2`", combined with the explicit
  Fiori–Kadiri–Swidinsky prime-counting estimate (eq. `FKS-pi`, the declared
  external input `fioriKadiriSwidinsky_pi_approx` of `Erdos320/Assumptions.lean`)
  and the elementary integral bound
  `Li(m) − Li(m/2) ≥ m / (2 log m)`.  Following the paper, the upper bound is
  proved in the explicit range `t ≥ exp(9·10⁶)`, "which covers every numerical
  use of that upper bound".
-/

namespace Erdos320

open Finset

/-! ## Lower bound: `t / log 2 < m_*(t)` -/

/-- **Lower half of eq. `elementary-threshold`** (`lem:elementary-threshold`):
`t / log 2 < m_*(t)`.  From `t < g(m_*(t)) ≤ m_*(t) · log 2`
(`lt_g_mStar` and `g_le_mul_log_two`).  The paper asserts this for every
`t > 0`; the argument never uses positivity of `t`, so it is stated here for
every real `t` — for `t ≤ 0` both sides degrade gracefully and the inequality
still holds. -/
theorem mStar_lower (t : ℝ) : t / Real.log 2 < (mStar t : ℝ) := by
  have h1 : t < g (mStar t) := lt_g_mStar t
  have h2 : g (mStar t) ≤ (mStar t : ℝ) * Real.log 2 := g_le_mul_log_two (mStar t)
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  rw [div_lt_iff₀ hlog]
  linarith

/-! ## Distinctness of reciprocal sums over sets of primes

The engine behind the paper's "reductions modulo the primes `p ∈ (m/2, m]`
show that their reciprocal subsets are all distinct": if two finite sets of
primes have the same reciprocal sum, they are equal, because a prime `p` in
one set but not the other survives reduction modulo `p` (after clearing the
`1/p` term by multiplying through by `p`). -/

/-- If `A` and `B` are finite sets of primes with the same reciprocal sum
`∑ 1/q`, no prime `p` can lie in `A` but not in `B`: multiplying the equal
sums by `p` and reducing modulo `p` (via `ratToZMod`) gives `1` on the `A`
side and `0` on the `B` side.  This is the reduction step in the proof of
`lem:elementary-threshold`. -/
theorem reciprocal_prime_sums_distinct {A B : Finset ℕ}
    (hA : ∀ q ∈ A, Nat.Prime q) (hB : ∀ q ∈ B, Nat.Prime q) {p : ℕ}
    (hpA : p ∈ A) (hpB : p ∉ B)
    (hsum : ∑ q ∈ A, (1 : ℚ) / q = ∑ q ∈ B, (1 : ℚ) / q) : False := by
  have hp : Nat.Prime p := hA p hpA
  haveI := Fact.mk hp
  -- `p` does not divide any prime `q ≠ p` (as integers)
  have hbint : ∀ q : ℕ, Nat.Prime q → q ≠ p → ¬ (p : ℤ) ∣ (q : ℤ) := by
    intro q hq hqp hd
    rw [Int.natCast_dvd_natCast] at hd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd).symm
  -- the fraction representation `(p/q) · q = p`
  have hab : ∀ q : ℕ, Nat.Prime q →
      ((p : ℚ) / (q : ℚ)) * (((q : ℕ) : ℤ) : ℚ) = (((p : ℕ) : ℤ) : ℚ) := by
    intro q hq
    have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.pos.ne'
    push_cast
    field_simp
  -- denominators of `p/q` are `p`-free for primes `q ≠ p`
  have hden : ∀ q : ℕ, Nat.Prime q → q ≠ p → ¬ p ∣ ((p : ℚ) / (q : ℚ)).den :=
    fun q hq hqp => not_dvd_den_of_mul_intCast_eq hp (hbint q hq hqp) (hab q hq)
  -- and their reductions vanish, since the numerator `p` is `0` mod `p`
  have hval : ∀ q : ℕ, Nat.Prime q → q ≠ p → ratToZMod p ((p : ℚ) / (q : ℚ)) = 0 := by
    intro q hq hqp
    rw [ratToZMod_unique hp (hbint q hq hqp) (hab q hq)]
    simp
  -- multiply the equal sums by `p`
  have hmul : ∑ q ∈ A, (p : ℚ) / q = ∑ q ∈ B, (p : ℚ) / q := by
    have h := congrArg (fun x : ℚ => (p : ℚ) * x) hsum
    simp only [Finset.mul_sum, mul_one_div] at h
    exact h
  -- the `B` side reduces to `0`
  have hBaux : ∀ q ∈ B, Nat.Prime q ∧ q ≠ p := fun q hq =>
    ⟨hB q hq, fun h => hpB (h ▸ hq)⟩
  have hBden : ∀ q ∈ B, ¬ p ∣ ((p : ℚ) / (q : ℚ)).den := fun q hq =>
    hden q (hBaux q hq).1 (hBaux q hq).2
  have hBval : ratToZMod p (∑ q ∈ B, (p : ℚ) / q) = 0 := by
    rw [ratToZMod_sum hp hBden]
    exact Finset.sum_eq_zero fun q hq => hval q (hBaux q hq).1 (hBaux q hq).2
  -- the `A` side reduces to `1` (split off the term `p/p = 1`)
  have hAden : ∀ q ∈ A.erase p, ¬ p ∣ ((p : ℚ) / (q : ℚ)).den := fun q hq =>
    hden q (hA q (Finset.mem_of_mem_erase hq)) (Finset.ne_of_mem_erase hq)
  have hone : ¬ p ∣ (1 : ℚ).den := by simpa using hp.ne_one
  have hAval : ratToZMod p (∑ q ∈ A, (p : ℚ) / q) = 1 := by
    rw [← Finset.sum_erase_add A _ hpA,
      show (p : ℚ) / (p : ℚ) = 1 from div_self (Nat.cast_ne_zero.mpr hp.pos.ne'),
      ratToZMod_add hp (not_dvd_den_sum hp hAden) hone, ratToZMod_one,
      ratToZMod_sum hp hAden,
      Finset.sum_eq_zero fun q hq =>
        hval q (hA q (Finset.mem_of_mem_erase hq)) (Finset.ne_of_mem_erase hq),
      zero_add]
  -- contradiction: `1 = 0` in the field `ZMod p`
  have h10 : (1 : ZMod p) = 0 := by
    rw [← hAval, ← hBval]
    exact congrArg (ratToZMod p) hmul
  exact one_ne_zero h10

/-- Reciprocal sums over subsets of a finite set `P` of primes `≤ m` are
pairwise distinct elements of `𝓔_m`, so `2^{|P|} ≤ S(m)`.  This is the
counting form of the paper's "their reciprocal subsets are all distinct"
(proof of `lem:elementary-threshold`). -/
theorem two_pow_card_le_S_of_primes {m : ℕ} {P : Finset ℕ}
    (hprime : ∀ q ∈ P, Nat.Prime q) (hle : ∀ q ∈ P, q ≤ m) :
    2 ^ P.card ≤ S m := by
  rw [← Finset.card_powerset]
  show P.powerset.card ≤ (reciprocalSubsetSumSet m).card
  refine Finset.card_le_card_of_injOn (fun A => ∑ n ∈ A, (1 : ℚ) / n) ?_ ?_
  · -- each subset sum lands in `𝓔_m`
    intro A hA
    rw [Finset.mem_coe, Finset.mem_powerset] at hA
    simp only [Finset.mem_coe, reciprocalSubsetSumSet, Finset.mem_image]
    refine ⟨A, Finset.mem_powerset.mpr fun q hq => ?_, rfl⟩
    rw [Finset.mem_Icc]
    exact ⟨(hprime q (hA hq)).one_lt.le, hle q (hA hq)⟩
  · -- distinct subsets give distinct sums
    intro A hA B hB hsum
    rw [Finset.mem_coe, Finset.mem_powerset] at hA hB
    by_contra hne
    have hex : ∃ q, (q ∈ A ∧ q ∉ B) ∨ (q ∈ B ∧ q ∉ A) := by
      by_contra hcon
      push Not at hcon
      exact hne (Finset.ext fun q => ⟨(hcon q).1, (hcon q).2⟩)
    rcases hex with ⟨q, ⟨hqA, hqB⟩ | ⟨hqB, hqA⟩⟩
    · exact reciprocal_prime_sums_distinct (fun r hr => hprime r (hA hr))
        (fun r hr => hprime r (hB hr)) hqA hqB hsum
    · exact reciprocal_prime_sums_distinct (fun r hr => hprime r (hB hr))
        (fun r hr => hprime r (hA hr)) hqB hqA hsum.symm

/-- The number of primes in the interval `(⌊m/2⌋, m]` is exactly
`π(m) − π(m/2)` (with `π` evaluated at the real points `m` and `m/2`;
`π(m/2)` counts the primes `≤ ⌊m/2⌋`). -/
theorem card_primeInterval (m : ℕ) :
    ((Finset.Ioc (m / 2) m).filter Nat.Prime).card
      = primePi (m : ℝ) - primePi ((m : ℝ) / 2) := by
  have h1 : primePi (m : ℝ) = ((Finset.range (m + 1)).filter Nat.Prime).card := by
    rw [primePi, Nat.floor_natCast, Nat.primeCounting, Nat.primeCounting',
      Nat.count_eq_card_filter_range]
  have h2 : primePi ((m : ℝ) / 2)
      = ((Finset.range (m / 2 + 1)).filter Nat.Prime).card := by
    rw [primePi, Nat.floor_div_ofNat, Nat.floor_natCast, Nat.primeCounting,
      Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hsplit : (Finset.range (m + 1)).filter Nat.Prime
      = ((Finset.range (m / 2 + 1)).filter Nat.Prime)
        ∪ ((Finset.Ioc (m / 2) m).filter Nat.Prime) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨hk, hkp⟩
      rcases le_or_gt k (m / 2) with h | h
      · exact Or.inl ⟨by omega, hkp⟩
      · exact Or.inr ⟨⟨h, by omega⟩, hkp⟩
    · rintro (⟨hk, hkp⟩ | ⟨hk, hkp⟩) <;> exact ⟨by omega, hkp⟩
  have hdisj : Disjoint ((Finset.range (m / 2 + 1)).filter Nat.Prime)
      ((Finset.Ioc (m / 2) m).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hk1 hk2
    omega
  rw [h1, h2, hsplit, Finset.card_union_of_disjoint hdisj]
  omega

/-- The prime-subset counting bound of `lem:elementary-threshold`:
`2^{π(m) − π(m/2)} ≤ S(m)`, since the reciprocal subsets of the primes in
`(m/2, m]` are pairwise distinct elements of `𝓔_m`. -/
theorem two_pow_primeInterval_le_S (m : ℕ) :
    2 ^ (primePi (m : ℝ) - primePi ((m : ℝ) / 2)) ≤ S m := by
  rw [← card_primeInterval m]
  exact two_pow_card_le_S_of_primes
    (fun q hq => (Finset.mem_filter.mp hq).2)
    (fun q hq => (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2)

/-- The paper's `g(m) ≥ (π(m) − π(m/2)) · log 2` (proof of
`lem:elementary-threshold`), by taking logarithms in
`two_pow_primeInterval_le_S`. -/
theorem g_ge_primeInterval (m : ℕ) :
    ((primePi (m : ℝ) - primePi ((m : ℝ) / 2) : ℕ) : ℝ) * Real.log 2 ≤ g m := by
  have h := two_pow_primeInterval_le_S m
  have hlog : Real.log ((2 : ℝ) ^ (primePi (m : ℝ) - primePi ((m : ℝ) / 2)))
      ≤ Real.log (S m) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast h
  rw [Real.log_pow] at hlog
  exact hlog

/-! ## The dyadic `Li` gap: `Li(y) − Li(y/2) ≥ y / (2 log y)` -/

/-- The elementary integral bound used in the proof of
`lem:elementary-threshold`: `Li(y) − Li(y/2) ≥ y / (2 log y)`, because the
integrand `1/log t` is at least `1/log y` on the interval `[y/2, y]` of
length `y/2`. -/
theorem li_gap_lower {y : ℝ} (hy : 4 ≤ y) :
    y / (2 * Real.log y) ≤ Li y - Li (y / 2) := by
  have hy2 : (2 : ℝ) ≤ y / 2 := by linarith
  have hyy : y / 2 ≤ y := by linarith
  have hint1 : IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume 2 (y / 2) :=
    intervalIntegrable_one_div_log le_rfl hy2
  have hint2 : IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume (y / 2) y :=
    intervalIntegrable_one_div_log hy2 (by linarith)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have hmono : ∫ _t in (y / 2)..y, 1 / Real.log y ≤ ∫ t in (y / 2)..y, 1 / Real.log t := by
    apply intervalIntegral.integral_mono_on hyy intervalIntegrable_const hint2
    intro t ht
    have h2t : 2 ≤ t := le_trans hy2 ht.1
    exact one_div_le_one_div_of_le (Real.log_pos (by linarith))
      (Real.log_le_log (by linarith) ht.2)
  have hconst : ∫ _t in (y / 2)..y, 1 / Real.log y = (y - y / 2) * (1 / Real.log y) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hval : (y - y / 2) * (1 / Real.log y) = y / (2 * Real.log y) := by
    rw [show y - y / 2 = y / 2 by ring, div_mul_div_comm, mul_one]
  rw [hconst, hval] at hmono
  simp only [Li]
  linarith

/-! ## Smallness of the FKS error in the explicit range

For `log y ≥ 9·10⁶` the Fiori–Kadiri–Swidinsky error term
`9.2211 · y · √(log y) · exp(−0.8476·√(log y))` is at most
`y / (10⁹⁰ · log y)` — exactly the uniform ledger the paper's explicit-range
proof states and uses (`Err_π(y) ≤ 10⁻⁹⁰·y/log y` for
`log y ≥ 9·10⁶`), with room to spare for the `m ≍ 4t log(2t)`
bookkeeping uniformly in `t` (the extra `1/log y` factor is what makes the
comparison to `t` uniform). -/

/-- `√x ≥ 3000` once `x ≥ 9·10⁶ = 3000²`. -/
theorem three_thousand_le_sqrt {x : ℝ} (hx : (9 * 10 ^ 6 : ℝ) ≤ x) :
    (3000 : ℝ) ≤ Real.sqrt x := by
  have h : (3000 : ℝ) = Real.sqrt (9 * 10 ^ 6) := by
    rw [show (9 * 10 ^ 6 : ℝ) = 3000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h]
  exact Real.sqrt_le_sqrt hx

/-- A crude but uniform logarithm bound for large arguments:
`log x ≤ x / 1500` for `x ≥ 9·10⁶` (via `log x = 2 log √x ≤ 2√x` and
`√x ≤ x / 3000`). -/
theorem log_le_self_div_1500 {x : ℝ} (hx : (9 * 10 ^ 6 : ℝ) ≤ x) :
    Real.log x ≤ x / 1500 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs := three_thousand_le_sqrt hx
  have hs0 : (0 : ℝ) < Real.sqrt x := by linarith
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx0.le]
    ring
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hs0
  have h3 : 3000 * Real.sqrt x ≤ x := by
    have h := mul_le_mul_of_nonneg_right hs hs0.le
    rwa [Real.mul_self_sqrt hx0.le] at h
  linarith

/-- Sub-exponential growth of the identity at scale `3000`:
`s ≤ exp(0.015·s)` for `s ≥ 3000` (via `exp z ≥ (z/4)⁴`). -/
theorem self_le_exp_of_3000_le {s : ℝ} (hs : (3000 : ℝ) ≤ s) :
    s ≤ Real.exp (0.015 * s) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have h1 : 0.015 * s / 4 ≤ Real.exp (0.015 * s / 4) := by
    have h := Real.add_one_le_exp (0.015 * s / 4)
    linarith
  have h2 : (0.015 * s / 4) ^ (4 : ℕ) ≤ Real.exp (0.015 * s / 4) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by linarith) h1 4
  have h3 : Real.exp (0.015 * s / 4) ^ (4 : ℕ) = Real.exp (0.015 * s) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hcube : (0 : ℝ) ≤ (s ^ (3 : ℕ) - 3000 ^ (3 : ℕ)) * s :=
    mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) hs 3)) hs0.le
  have h4 : s ≤ (0.015 * s / 4) ^ (4 : ℕ) := by linarith [hcube]
  calc s ≤ (0.015 * s / 4) ^ (4 : ℕ) := h4
    _ ≤ Real.exp (0.015 * s / 4) ^ (4 : ℕ) := h2
    _ = Real.exp (0.015 * s) := h3

/-- **Smallness of the FKS error term** in the explicit range of
`lem:elementary-threshold`: for `log y ≥ 9·10⁶`,
`9.2211 · y · √(log y) · exp(−0.8476·√(log y)) ≤ y / (10⁹⁰ · log y)`. -/
theorem fksError_le_div_log {y : ℝ} (hy0 : 0 ≤ y)
    (hlog : (9 * 10 ^ 6 : ℝ) ≤ Real.log y) :
    9.2211 * y * Real.sqrt (Real.log y) * Real.exp (-0.8476 * Real.sqrt (Real.log y))
      ≤ y / (10 ^ 90 * Real.log y) := by
  have hL0 : (0 : ℝ) < Real.log y := by linarith
  set s := Real.sqrt (Real.log y) with hsdef
  have hs3000 : (3000 : ℝ) ≤ s := three_thousand_le_sqrt hlog
  have hs0 : (0 : ℝ) < s := by linarith
  have hL_eq : Real.log y = s ^ 2 := by rw [hsdef, Real.sq_sqrt hL0.le]
  -- `s³ ≤ exp(0.045 s)`
  have hcube : s ^ (3 : ℕ) ≤ Real.exp (0.045 * s) := by
    have h1 : s ≤ Real.exp (0.015 * s) := self_le_exp_of_3000_le hs3000
    have h2 : s ^ (3 : ℕ) ≤ Real.exp (0.015 * s) ^ (3 : ℕ) :=
      pow_le_pow_left₀ hs0.le h1 3
    have h3 : Real.exp (0.015 * s) ^ (3 : ℕ) = Real.exp (0.045 * s) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    linarith
  -- the key numeric bound
  have hkey : 9.2211 * 10 ^ 90 * (s ^ (3 : ℕ) * Real.exp (-0.8476 * s)) ≤ 1 := by
    have h1 : s ^ (3 : ℕ) * Real.exp (-0.8476 * s) ≤ Real.exp (-0.8026 * s) := by
      have h := mul_le_mul_of_nonneg_right hcube (Real.exp_pos (-0.8476 * s)).le
      rwa [← Real.exp_add, show 0.045 * s + -0.8476 * s = -0.8026 * s by ring] at h
    have h2 : Real.exp (-0.8026 * s) ≤ Real.exp (-2400 : ℝ) :=
      Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp (-2400 : ℝ) = Real.exp (-1 : ℝ) ^ (2400 : ℕ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
    have h4 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.exp_neg]
      have h2exp : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      calc (Real.exp 1)⁻¹ = 1 / Real.exp 1 := (one_div _).symm
        _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2exp
    have h5 : Real.exp (-1 : ℝ) ^ (2400 : ℕ) ≤ (1 / 2 : ℝ) ^ (2400 : ℕ) :=
      pow_le_pow_left₀ (Real.exp_pos _).le h4 2400
    have hpow : (10 : ℝ) ^ (91 : ℕ) ≤ (2 : ℝ) ^ (2400 : ℕ) := by
      calc (10 : ℝ) ^ (91 : ℕ) ≤ (10 : ℝ) ^ (720 : ℕ) :=
            pow_le_pow_right₀ (by norm_num) (by norm_num)
        _ = ((10 : ℝ) ^ (3 : ℕ)) ^ (240 : ℕ) := by rw [← pow_mul]
        _ ≤ ((2 : ℝ) ^ (10 : ℕ)) ^ (240 : ℕ) :=
            pow_le_pow_left₀ (by positivity) (by norm_num) 240
        _ = (2 : ℝ) ^ (2400 : ℕ) := by rw [← pow_mul]
    have h6 : (9.2211 : ℝ) * 10 ^ 90 * (1 / 2 : ℝ) ^ (2400 : ℕ) ≤ 1 := by
      rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
      calc (9.2211 : ℝ) * 10 ^ 90 ≤ 10 ^ (91 : ℕ) := by norm_num
        _ ≤ 2 ^ (2400 : ℕ) := hpow
    calc 9.2211 * 10 ^ 90 * (s ^ (3 : ℕ) * Real.exp (-0.8476 * s))
        ≤ 9.2211 * 10 ^ 90 * ((1 / 2 : ℝ) ^ (2400 : ℕ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc s ^ (3 : ℕ) * Real.exp (-0.8476 * s) ≤ Real.exp (-0.8026 * s) := h1
            _ ≤ Real.exp (-2400 : ℝ) := h2
            _ = Real.exp (-1 : ℝ) ^ (2400 : ℕ) := h3
            _ ≤ (1 / 2 : ℝ) ^ (2400 : ℕ) := h5
      _ ≤ 1 := h6
  rw [le_div_iff₀ (mul_pos (by positivity) hL0)]
  calc 9.2211 * y * s * Real.exp (-0.8476 * s) * (10 ^ 90 * Real.log y)
      = y * (9.2211 * 10 ^ 90 * (s ^ (3 : ℕ) * Real.exp (-0.8476 * s))) := by
        rw [hL_eq]
        ring
    _ ≤ y * 1 := mul_le_mul_of_nonneg_left hkey hy0
    _ = y := mul_one y

/-! ## Upper bound: `m_*(t) < 4 t log(2t)` in the explicit range -/

/-- **Upper half of eq. `elementary-threshold`** (`lem:elementary-threshold`),
in the paper's explicit range `t ≥ exp(9·10⁶)` ("which covers every numerical
use of that upper bound"): `m_*(t) < 4·t·log(2t)`.

Proof, following the paper: take `m` just below `4t·log(2t)`.  Then
`Li(m) − Li(m/2) ≥ m/(2 log m) ≥ 1.99t` (`li_gap_lower` plus the size
bookkeeping; the paper displays `> 1.98t`), the FKS errors at `m` and `m/2`
are below `0.001·t` each
(`fksError_le_div_log`, applied through the declared external input
`fioriKadiriSwidinsky_pi_approx` = eq. `FKS-pi`), so
`π(m) − π(m/2) ≥ 1.98t` and `g(m) ≥ (π(m) − π(m/2))·log 2 > 1.3t > t`
(`g_ge_primeInterval`), whence `m_*(t) ≤ m < 4t·log(2t)`. -/
theorem mStar_upper_explicit {t : ℝ} (ht : Real.exp (9 * 10 ^ 6) ≤ t) :
    (mStar t : ℝ) < 4 * t * Real.log (2 * t) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos _) ht
  have htbig : (1000 : ℝ) ≤ t := by
    have h := Real.add_one_le_exp (9 * 10 ^ 6 : ℝ)
    linarith
  have hL : (9 * 10 ^ 6 : ℝ) ≤ Real.log t := (Real.le_log_iff_exp_le ht0).mpr ht
  set L2 : ℝ := Real.log (2 * t) with hL2def
  have hlog2t : Real.log t ≤ L2 := by
    rw [hL2def]
    exact Real.log_le_log ht0 (by linarith)
  have hL2 : (9 * 10 ^ 6 : ℝ) ≤ L2 := le_trans hL hlog2t
  have hL2pos : (0 : ℝ) < L2 := by linarith
  have htL2 : (9 * 10 ^ 9 : ℝ) ≤ t * L2 := by
    have h := mul_le_mul htbig hL2 (by norm_num) (by linarith)
    linarith
  have htL2' : (9 * 10 ^ 6 : ℝ) * t ≤ t * L2 := by nlinarith
  set y0 : ℝ := 4 * t * L2 with hy0def
  have hy0pos : (0 : ℝ) < y0 := by rw [hy0def]; nlinarith
  have hfloor1 : 1 ≤ ⌊y0⌋₊ := Nat.le_floor (by rw [hy0def]; push_cast; nlinarith)
  set m : ℕ := ⌊y0⌋₊ - 1 with hmdef
  set y : ℝ := (m : ℝ) with hydef
  have hmcast : y = (⌊y0⌋₊ : ℝ) - 1 := by
    rw [hydef, hmdef, Nat.cast_sub hfloor1, Nat.cast_one]
  have hm_le : y ≤ y0 - 1 := by
    have h := Nat.floor_le hy0pos.le
    rw [hmcast]
    linarith
  have hm_ge : y0 - 2 ≤ y := by
    have h := Nat.lt_floor_add_one y0
    rw [hmcast]
    linarith
  have hy4t : 4 * t ≤ y := by linarith [hm_ge, hy0def, htL2', htbig]
  have hy4 : (4 : ℝ) ≤ y := by linarith
  have hypos : (0 : ℝ) < y := by linarith
  have hyley0 : y ≤ y0 := by linarith
  have hlogy_lb : L2 ≤ Real.log y := by
    rw [hL2def]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlogy2_lb : L2 ≤ Real.log (y / 2) := by
    rw [hL2def]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlogy_9e6 : (9 * 10 ^ 6 : ℝ) ≤ Real.log y := le_trans hL2 hlogy_lb
  have hlogy2_9e6 : (9 * 10 ^ 6 : ℝ) ≤ Real.log (y / 2) := le_trans hL2 hlogy2_lb
  have hlogypos : (0 : ℝ) < Real.log y := by linarith
  have hlogy2pos : (0 : ℝ) < Real.log (y / 2) := by linarith
  -- upper bound on `log y`: `log y ≤ 1.001 · L2`
  have hlog4 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hlogL2 : Real.log L2 ≤ L2 / 1500 := log_le_self_div_1500 hL2
  have hlogy0 : Real.log y0 = Real.log 4 + Real.log t + Real.log L2 := by
    rw [hy0def, Real.log_mul (mul_ne_zero (by norm_num) ht0.ne') hL2pos.ne',
      Real.log_mul (by norm_num) ht0.ne']
  have hlogy_ub : Real.log y ≤ 1.001 * L2 := by
    have h1 : Real.log y ≤ Real.log y0 := Real.log_le_log hypos hyley0
    rw [hlogy0] at h1
    linarith [hlog2t]
  -- the `Li` gap dominates: `y/(2 log y) ≥ 1.99 t`
  have hgap : 1.99 * t ≤ y / (2 * Real.log y) := by
    rw [le_div_iff₀ (mul_pos two_pos hlogypos)]
    have hint1 : t * Real.log y ≤ t * (1.001 * L2) :=
      mul_le_mul_of_nonneg_left hlogy_ub ht0.le
    linarith [hm_ge, hy0def, htL2, hint1]
  have hLi : y / (2 * Real.log y) ≤ Li y - Li (y / 2) := li_gap_lower hy4
  -- FKS errors at `y` and `y/2` are below `0.001 t` each
  have herr1 := fksError_le_div_log hypos.le hlogy_9e6
  have herr1' : y / (10 ^ 90 * Real.log y) ≤ 0.001 * t := by
    rw [div_le_iff₀ (mul_pos (by positivity) hlogypos)]
    have hint3 : t * L2 ≤ t * Real.log y := mul_le_mul_of_nonneg_left hlogy_lb ht0.le
    linarith [hyley0, hy0def, htL2, hint3]
  have herr2 := fksError_le_div_log (by linarith : (0 : ℝ) ≤ y / 2) hlogy2_9e6
  have herr2' : y / 2 / (10 ^ 90 * Real.log (y / 2)) ≤ 0.001 * t := by
    rw [div_le_iff₀ (mul_pos (by positivity) hlogy2pos)]
    have hint4 : t * L2 ≤ t * Real.log (y / 2) :=
      mul_le_mul_of_nonneg_left hlogy2_lb ht0.le
    linarith [hyley0, hy0def, htL2, hint4]
  have hfks1 := fioriKadiriSwidinsky_pi_approx y (by linarith)
  have hfks2 := fioriKadiriSwidinsky_pi_approx (y / 2) (by linarith)
  have hpi1 : Li y - 0.001 * t ≤ (primePi y : ℝ) := by
    have h := (abs_le.mp hfks1).1
    linarith [le_trans herr1 herr1']
  have hpi2 : (primePi (y / 2) : ℝ) ≤ Li (y / 2) + 0.001 * t := by
    have h := (abs_le.mp hfks2).2
    linarith [le_trans herr2 herr2']
  have hdiff : 1.98 * t ≤ (primePi y : ℝ) - (primePi (y / 2) : ℝ) := by linarith
  have hcast : (primePi y : ℝ) - (primePi (y / 2) : ℝ)
      ≤ ((primePi y - primePi (y / 2) : ℕ) : ℝ) := by
    rcases le_or_gt (primePi (y / 2)) (primePi y) with h | h
    · rw [Nat.cast_sub h]
    · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
      have h' : (primePi y : ℝ) ≤ (primePi (y / 2) : ℝ) := Nat.cast_le.mpr h.le
      linarith
  -- conclude `t < g(m)` and hence `m_*(t) ≤ m < 4 t log(2t)`
  have hglb := g_ge_primeInterval m
  rw [← hydef] at hglb
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hk : 1.98 * t ≤ ((primePi y - primePi (y / 2) : ℕ) : ℝ) := le_trans hdiff hcast
  have hgt : t < g m := by
    have h1 : 1.98 * t * Real.log 2
        ≤ ((primePi y - primePi (y / 2) : ℕ) : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hk (by linarith)
    have h2 : 1.98 * t * 0.6931471803 ≤ 1.98 * t * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2gt.le (by linarith)
    linarith
  have hms : (mStar t : ℝ) ≤ y := by
    rw [hydef]
    exact_mod_cast mStar_le_of_lt_g hgt
  linarith

end Erdos320
