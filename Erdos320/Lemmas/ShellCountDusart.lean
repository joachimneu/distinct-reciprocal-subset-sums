import Erdos320.Lemmas.ShellDecomposition
import Erdos320.Defs.PrimeCounting
import Erdos320.Assumptions

/-!
# Dusart-`ϑ`–based lower bound on shell prime counts (for the high finite input)

The high finite input `comp:high` (the proved theorem `highFiniteInput`,
`Erdos320/Lemmas/HighFiniteAssembly.lean`) needs, for each prime shell `m`, a
*lower* bound on the number of primes in the half-open interval
`(⌊N/(m+1)⌋, ⌊N/m⌋]` — that is, on `(shellPrimes N m).card`.
The manuscript (§8, eq. `theta-explicit`) obtains these counts from Dusart's
explicit Chebyshev estimate `|ϑ(t) − t| ≤ 0.006788·t/log t` for `t ≥ 89 967 803`.
That form is the *proved theorem* `dusart_theta_approx` below, derived here from
the axiom `dusart_theta_k3` (`Assumptions.lean`; Dusart 2018 Thm 4.2, the `k = 3`
row `|ϑ(t)−t| ≤ t/(log t)³`, `t ≥ 89 967 803`) by the manuscript's own one-line
step (`t ≥ 89 967 803 > e¹⁸ ⇒ log t ≥ 18 ⇒ 1/(log t)² ≤ 1/324 < 0.006788`).

The elementary inequality behind the bound is: for primes `p` with `a < p ≤ b`
we have `log p ≤ log b`, hence
```
(#primes in (a,b]) · log b ≥ ∑_{a<p≤b} log p = ϑ(b) − ϑ(a),
```
so `#primes in (a,b] ≥ (ϑ(b) − ϑ(a)) / log b`.  Bounding `ϑ(b)` below and
`ϑ(a)` above by Dusart (both endpoints `≥ 89 967 803`) turns the right-hand side
into a computable quantity.

## Interface for the Phase-D assembly

* `chebyshevTheta_sub_eq_sum_shellPrimes` — `ϑ(N/m) − ϑ(N/(m+1)) = ∑_{p ∈ shell} log p`
  (the `chebyshevTheta`→shell-sum bridge; pure `Finset`/`ℕ`-division algebra);
* `sum_log_shellPrimes_le` — `∑_{p ∈ shell} log p ≤ card · log(N/m)`;
* `shellPrimes_card_lower_of_theta` — the *generic* structural bound: from any
  `θlo ≤ ϑ(N/m)`, `ϑ(N/(m+1)) ≤ θhi`, and any `Lb ≥ log(N/m)` (`Lb > 0`), one
  gets `(θlo − θhi)/Lb ≤ card`.  **This is the primary Phase-D interface**: feed
  it rational `θlo`, `θhi`, `Lb`;
* `dusart_theta_lower_upper` — the two-sided Dusart enclosure at a point,
  `x·(1 − C/log x) ≤ ϑ(x) ≤ x·(1 + C/log x)` with `C = 0.006788` (uses
  `dusart_theta_approx`);
* `shellPrimes_card_lower_dusart` — the combined convenience: with rational
  lower bounds `logbLo ≤ log(N/m)`, `logaLo ≤ log(N/(m+1))` and a rational upper
  bound `Lb ≥ log(N/m)`, it yields a fully rational lower bound on `card`
  (the form Phase D consumes per shell).
-/

namespace Erdos320

open Finset

/-- **Consumed Chebyshev `ϑ` bound (proved from the axiom `dusart_theta_k3`).**
`|ϑ(t) − t| ≤ 0.006788·t/log t` for every `t ≥ 89 967 803` — the manuscript's
eq. `theta-explicit` (§8), the form the `comp:high` shell/aggregate prime counts
consume.  It is the paper's own "weaker consequence" of Dusart's `k = 3`
estimate `|ϑ(t) − t| ≤ t/(log t)³` (`dusart_theta_k3`, `Assumptions.lean`): for
`t ≥ 89 967 803 > e¹⁸` one has `log t ≥ 18`, hence `1/(log t)² ≤ 1/324 < 0.006788`,
so `t/(log t)³ ≤ 0.006788·t/log t`.  A proved theorem, **not** an axiom — its
only external input is `dusart_theta_k3`. -/
theorem dusart_theta_approx (t : ℝ) (ht : (89967803 : ℝ) ≤ t) :
    |chebyshevTheta t - t| ≤ 0.006788 * t / Real.log t := by
  have htpos : (0 : ℝ) < t := by linarith
  have hlog18 : (18 : ℝ) ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le htpos]
    calc Real.exp (18 : ℝ) = Real.exp 1 ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2.7182818286 : ℝ) ^ 18 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 18
      _ ≤ 89967803 := by norm_num
      _ ≤ t := ht
  have hlogpos : (0 : ℝ) < Real.log t := by linarith
  have hlogne : Real.log t ≠ 0 := ne_of_gt hlogpos
  have hsq : (324 : ℝ) ≤ (Real.log t) ^ 2 := by
    nlinarith [hlog18, sq_nonneg (Real.log t - 18)]
  have hfac : (0 : ℝ) ≤ 0.006788 * (Real.log t) ^ 2 - 1 := by nlinarith [hsq]
  have hstep : t / (Real.log t) ^ 3 ≤ 0.006788 * t / Real.log t := by
    have e1 : 0.006788 * t / Real.log t - t / (Real.log t) ^ 3
            = t * (0.006788 * (Real.log t) ^ 2 - 1) / (Real.log t) ^ 3 := by
      field_simp
    have hnn : (0 : ℝ) ≤ 0.006788 * t / Real.log t - t / (Real.log t) ^ 3 := by
      rw [e1]; exact div_nonneg (mul_nonneg htpos.le hfac) (by positivity)
    linarith
  exact le_trans (dusart_theta_k3 t ht) hstep

/-! ## The `chebyshevTheta`→shell-sum bridge -/

/-- **`ϑ(N/m) − ϑ(N/(m+1))` is the shell log-sum.**  For `1 ≤ m`, the
`ℕ`-division boundaries of `chebyshevTheta` at the real cut-points `N/m` and
`N/(m+1)` are exactly `⌊N/m⌋ = N/m` and `⌊N/(m+1)⌋ = N/(m+1)` (Nat division), so
the difference of the two Chebyshev sums telescopes to the sum of `log p` over
the primes of `shellPrimes N m = (⌊N/(m+1)⌋, ⌊N/m⌋] ∩ primes`.  No literature
input: pure `Finset`/`Nat.floor` algebra. -/
theorem chebyshevTheta_sub_eq_sum_shellPrimes {N m : ℕ} (hm : 1 ≤ m) :
    chebyshevTheta ((N : ℝ) / m) - chebyshevTheta ((N : ℝ) / (m + 1))
      = ∑ p ∈ shellPrimes N m, Real.log (p : ℝ) := by
  -- rewrite each `chebyshevTheta` as a sum over a prime-filtered `Iic`
  have hb : chebyshevTheta ((N : ℝ) / m)
      = ∑ p ∈ (Finset.Iic (N / m)).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [chebyshevTheta, Nat.floor_div_eq_div]
  have ha : chebyshevTheta ((N : ℝ) / (m + 1))
      = ∑ p ∈ (Finset.Iic (N / (m + 1))).filter Nat.Prime, Real.log (p : ℝ) := by
    have hcast : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [chebyshevTheta, hcast, Nat.floor_div_eq_div]
  -- the `Iic (N/m)` primes split as `Iic (N/(m+1))` primes ∪ the shell
  have hle : N / (m + 1) ≤ N / m := Nat.div_le_div_left (by omega) (by omega)
  have hunion : (Finset.Iic (N / m)).filter Nat.Prime
      = (Finset.Iic (N / (m + 1))).filter Nat.Prime ∪ shellPrimes N m := by
    rw [shellPrimes, ← Finset.filter_union, Finset.Iic_union_Ioc_eq_Iic hle]
  have hdisj : Disjoint ((Finset.Iic (N / (m + 1))).filter Nat.Prime)
      (shellPrimes N m) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_filter, Finset.mem_Iic] at hp1
    rw [mem_shellPrimes] at hp2
    omega
  rw [hb, ha, hunion, Finset.sum_union hdisj]
  ring

/-! ## The elementary log-sum bound -/

/-- **Each shell log-sum is bounded by `card · log(N/m)`.**  Every prime `p` in
`shellPrimes N m` satisfies `p ≤ ⌊N/m⌋ ≤ N/m` (as reals), hence
`log p ≤ log(N/m)`; summing over the `card` primes gives the bound. -/
theorem sum_log_shellPrimes_le (N m : ℕ) :
    ∑ p ∈ shellPrimes N m, Real.log (p : ℝ)
      ≤ ((shellPrimes N m).card : ℝ) * Real.log ((N : ℝ) / m) := by
  have hterm : ∀ p ∈ shellPrimes N m,
      Real.log (p : ℝ) ≤ Real.log ((N : ℝ) / m) := by
    intro p hp
    rw [mem_shellPrimes] at hp
    obtain ⟨_, hpb, hprime⟩ := hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    refine Real.log_le_log hp0 ?_
    calc (p : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast hpb
      _ ≤ (N : ℝ) / m := Nat.cast_div_le
  calc ∑ p ∈ shellPrimes N m, Real.log (p : ℝ)
      ≤ (shellPrimes N m).card • Real.log ((N : ℝ) / m) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((shellPrimes N m).card : ℝ) * Real.log ((N : ℝ) / m) := by
        rw [nsmul_eq_mul]

/-! ## The generic structural lower bound (primary Phase-D interface) -/

/-- **Structural shell-count lower bound.**  For `1 ≤ m`, given any real
`θlo ≤ ϑ(N/m)`, `ϑ(N/(m+1)) ≤ θhi`, and any upper bound `Lb ≥ log(N/m)` with
`Lb > 0`,
```
(θlo − θhi) / Lb ≤ (shellPrimes N m).card.
```
Phase D consumes this with *rational* `θlo`, `θhi`, `Lb`.  No literature input
(the Dusart estimate enters only when `θlo`/`θhi` are produced from
`dusart_theta_lower_upper`). -/
theorem shellPrimes_card_lower_of_theta {N m : ℕ} (hm : 1 ≤ m)
    (θlo θhi Lb : ℝ)
    (hθlo : θlo ≤ chebyshevTheta ((N : ℝ) / m))
    (hθhi : chebyshevTheta ((N : ℝ) / (m + 1)) ≤ θhi)
    (hLb : Real.log ((N : ℝ) / m) ≤ Lb) (hLbpos : 0 < Lb) :
    (θlo - θhi) / Lb ≤ ((shellPrimes N m).card : ℝ) := by
  rw [div_le_iff₀ hLbpos]
  have hcard0 : (0 : ℝ) ≤ ((shellPrimes N m).card : ℝ) := by positivity
  have hbridge := chebyshevTheta_sub_eq_sum_shellPrimes (N := N) (m := m) hm
  have h1 : chebyshevTheta ((N : ℝ) / m) - chebyshevTheta ((N : ℝ) / (m + 1))
      ≤ ((shellPrimes N m).card : ℝ) * Lb := by
    rw [hbridge]
    calc ∑ p ∈ shellPrimes N m, Real.log (p : ℝ)
        ≤ ((shellPrimes N m).card : ℝ) * Real.log ((N : ℝ) / m) :=
          sum_log_shellPrimes_le N m
      _ ≤ ((shellPrimes N m).card : ℝ) * Lb :=
          mul_le_mul_of_nonneg_left hLb hcard0
  linarith [hθlo, hθhi, h1]

/-! ## The Dusart two-sided enclosure -/

/-- **Dusart `ϑ` enclosure at a point** (eq. `theta-explicit`).  For
`x ≥ 89 967 803`, with `C = 0.006788`,
```
x − C·x/log x ≤ ϑ(x) ≤ x + C·x/log x.
```
Immediate from `dusart_theta_approx` via `abs_le`. -/
theorem dusart_theta_lower_upper {x : ℝ} (hx : (89967803 : ℝ) ≤ x) :
    x - 0.006788 * x / Real.log x ≤ chebyshevTheta x
      ∧ chebyshevTheta x ≤ x + 0.006788 * x / Real.log x := by
  have h := abs_le.mp (dusart_theta_approx x hx)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ## The combined Dusart shell-count lower bound -/

/-- **Combined shell-count lower bound via Dusart.**  For `1 ≤ m` with both
endpoints `N/m, N/(m+1) ≥ 89 967 803`, and given rational *lower* bounds
`logbLo ≤ log(N/m)`, `logaLo ≤ log(N/(m+1))` (both positive) and a rational
*upper* bound `Lb ≥ log(N/m)` (`Lb > 0`),
```
( (N/m − C·(N/m)/logbLo) − (N/(m+1) + C·(N/(m+1))/logaLo) ) / Lb
    ≤ (shellPrimes N m).card,     C = 0.006788.
```
Every quantity on the left is rational in `N, m, logbLo, logaLo, Lb`, so Phase D
obtains a rational lower bound on each shell's prime count.  Depends on
`dusart_theta_approx`. -/
theorem shellPrimes_card_lower_dusart {N m : ℕ} (hm : 1 ≤ m)
    (hb : (89967803 : ℝ) ≤ (N : ℝ) / m)
    (ha : (89967803 : ℝ) ≤ (N : ℝ) / (m + 1))
    (logbLo logaLo Lb : ℝ)
    (hlogbLo_pos : 0 < logbLo) (hlogbLo : logbLo ≤ Real.log ((N : ℝ) / m))
    (hlogaLo_pos : 0 < logaLo) (hlogaLo : logaLo ≤ Real.log ((N : ℝ) / (m + 1)))
    (hLb : Real.log ((N : ℝ) / m) ≤ Lb) (hLbpos : 0 < Lb) :
    (((N : ℝ) / m - 0.006788 * ((N : ℝ) / m) / logbLo)
        - ((N : ℝ) / (m + 1) + 0.006788 * ((N : ℝ) / (m + 1)) / logaLo)) / Lb
      ≤ ((shellPrimes N m).card : ℝ) := by
  obtain ⟨hbLo, -⟩ := dusart_theta_lower_upper hb
  obtain ⟨-, haUp⟩ := dusart_theta_lower_upper ha
  refine shellPrimes_card_lower_of_theta hm _ _ Lb ?_ ?_ hLb hLbpos
  · -- lower bound on `ϑ(N/m)`: replace `log(N/m)` by the smaller `logbLo`
    refine le_trans ?_ hbLo
    have hmono : 0.006788 * ((N : ℝ) / m) / Real.log ((N : ℝ) / m)
        ≤ 0.006788 * ((N : ℝ) / m) / logbLo :=
      div_le_div_of_nonneg_left (by positivity) hlogbLo_pos hlogbLo
    linarith [hmono]
  · -- upper bound on `ϑ(N/(m+1))`: replace `log(N/(m+1))` by the smaller `logaLo`
    refine le_trans haUp ?_
    have hmono : 0.006788 * ((N : ℝ) / (m + 1)) / Real.log ((N : ℝ) / (m + 1))
        ≤ 0.006788 * ((N : ℝ) / (m + 1)) / logaLo :=
      div_le_div_of_nonneg_left (by positivity) hlogaLo_pos hlogaLo
    linarith [hmono]

end Erdos320
