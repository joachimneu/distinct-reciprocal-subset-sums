import Erdos320.Lemmas.LargePrimeDecomposition
import Erdos320.Lemmas.SBasic
import Erdos320.Defs.PrimeCounting
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Real.Sqrt

/-!
# Shell decomposition of `g(N)` (eq. `shell-sum` of `prop:averaging-relation`)

The proof of `prop:averaging-relation` groups the large-prime product of
`prop:large-prime-decomposition` (with `Q = ⌊N/(M+1)⌋`) into *shells*
indexed by the common quotient `m = ⌊N/p⌋`:
```
g(N) = ∑_{m ≤ M} ∑_{N/(m+1) < p ≤ N/m} log σ_p(m) + O(log 𝔇_Q + log X),
```
eq. `shell-sum` (with `𝔇_Q(N)` the smooth denominator of
eq. `smooth-denominator-def`).  This file provides:

* the shell index sets `shellPrimes N m` (the primes in `(⌊N/(m+1)⌋, ⌊N/m⌋]`)
  and the exact partition `largePrimes (N/(M+1)) N = ⋃_{1 ≤ m ≤ M}
  shellPrimes N m` (`largePrimes_eq_biUnion_shellPrimes`,
  `shellPrimes_pairwiseDisjoint`) — the paper's "the large-prime product is
  exactly the disjoint union of the shells indexed by `1 ≤ m ≤ M`", including
  the remark that "since primes are integers, the conditions `p > Q` and
  `p > N/(M+1)` are equivalent";
* the two-sided shell-sum form of `g(N)` with the explicit fibre error
  `log(H_N + 1) + log 𝔇_Q` (`g_shell_decomposition`), the Lean rendering of
  eq. `shell-sum` with the `O(·)` made explicit;
* the smooth-core estimate `log 𝔇_Q ≤ ϑ(Q) + √N · log N`
  (`log_smoothPart_le`) — the paper's first-layer `ϑ(Q)` / higher-layers
  `O(√N log N)` split (via `lem:prime-power-splitting`), here with
  explicit constant `1`;
* the harmonic-sum bound `H_N ≤ 1 + log N` (`harmonicSum_le_one_add_log`,
  from Mathlib's `harmonic_le_one_add_log`), which makes the fibre error of
  `g_shell_decomposition` into the paper's `O(log X)` term.

**Remark.**  The partition
`largePrimes_eq_biUnion_shellPrimes` holds for *all* `N, M : ℕ` with no
hypotheses at all: the equivalence `p > ⌊N/(M+1)⌋ ↔ ⌊N/p⌋ ≤ M` (for `p ≥ 1`)
is pure `ℕ`-division bracketing, so none of the standing hypotheses of
`prop:large-prime-decomposition` are needed for the shell *regrouping* itself;
they enter only through the two product bounds in `g_shell_decomposition`.
-/

namespace Erdos320

open Finset

/-! ## Shells of large primes -/

/-- `shellPrimes N m` is the `m`-th *prime shell* of eq. `shell-sum`
(`prop:averaging-relation`): the primes `p` with `⌊N/(m+1)⌋ < p ≤ ⌊N/m⌋`
(equivalently, by `div_eq_of_mem_shell`, the primes with `⌊N/p⌋ = m`,
provided `m ≥ 1`). -/
def shellPrimes (N m : ℕ) : Finset ℕ :=
  (Ioc (N / (m + 1)) (N / m)).filter Nat.Prime

theorem mem_shellPrimes {N m p : ℕ} :
    p ∈ shellPrimes N m ↔ N / (m + 1) < p ∧ p ≤ N / m ∧ p.Prime := by
  simp [shellPrimes, mem_filter, mem_Ioc, and_assoc]

/-- **Shell membership determines the quotient.**  If `m ≥ 1` and
`⌊N/(m+1)⌋ < p ≤ ⌊N/m⌋`, then `⌊N/p⌋ = m` — the `ℕ`-division bracketing
behind the paper's regrouping "according to `m = ⌊N/p⌋`" in eq. `shell-sum`. -/
theorem div_eq_of_mem_shell {N m p : ℕ} (hm : 1 ≤ m)
    (hp : p ∈ Ioc (N / (m + 1)) (N / m)) : N / p = m := by
  obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hp
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hlo
  -- `p ≤ ⌊N/m⌋` gives `p·m ≤ N`, hence `m ≤ ⌊N/p⌋`
  have hpm : p * m ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hhi
  have h1 : m ≤ N / p :=
    (Nat.le_div_iff_mul_le hp0).mpr (by rw [Nat.mul_comm]; exact hpm)
  -- `⌊N/(m+1)⌋ < p` gives `N < p·(m+1)`, hence `⌊N/p⌋ < m + 1`
  have hlt : N < p * (m + 1) := (Nat.div_lt_iff_lt_mul (Nat.succ_pos m)).mp hlo
  have h2 : N / p < m + 1 :=
    (Nat.div_lt_iff_lt_mul hp0).mpr (by rw [Nat.mul_comm]; exact hlt)
  exact le_antisymm (Nat.lt_succ_iff.mp h2) h1

/-- **Shell partition of the large primes** (eq. `shell-sum`,
`prop:averaging-relation`): with `Q = ⌊N/(M+1)⌋`, the large primes
`Q < p ≤ N` are exactly the union of the shells `1 ≤ m ≤ M`.  This encodes
the paper's remark that "since primes are integers, the conditions `p > Q`
and `p > N/(M+1)` are equivalent": in `ℕ`-division, `⌊N/(M+1)⌋ < p` and
`⌊N/p⌋ ≤ M` are both equivalent to `N < p·(M+1)`.  No hypotheses on `N, M`
are needed (see the module docstring). -/
theorem largePrimes_eq_biUnion_shellPrimes (N M : ℕ) :
    largePrimes (N / (M + 1)) N = (Icc 1 M).biUnion (shellPrimes N) := by
  ext p
  simp only [mem_largePrimes, Finset.mem_biUnion, mem_Icc, mem_shellPrimes]
  constructor
  · rintro ⟨hQp, hpN, hprime⟩
    have hp0 : 0 < p := hprime.pos
    -- the shell index of `p` is `m = ⌊N/p⌋`; it satisfies `1 ≤ m ≤ M`
    have hm1 : 1 ≤ N / p := (Nat.one_le_div_iff hp0).mpr hpN
    have hlt : N < p * (M + 1) := (Nat.div_lt_iff_lt_mul (Nat.succ_pos M)).mp hQp
    have hmM : N / p ≤ M := Nat.lt_succ_iff.mp
      ((Nat.div_lt_iff_lt_mul hp0).mpr (by rw [Nat.mul_comm]; exact hlt))
    -- and `p` lies in its own shell: `⌊N/(m+1)⌋ < p ≤ ⌊N/m⌋` for `m = ⌊N/p⌋`
    have hupper : p ≤ N / (N / p) :=
      (Nat.le_div_iff_mul_le hm1).mpr (Nat.mul_div_le N p)
    have hlower : N / (N / p + 1) < p := by
      apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr
      calc N = p * (N / p) + N % p := (Nat.div_add_mod N p).symm
        _ < p * (N / p) + p := Nat.add_lt_add_left (Nat.mod_lt N hp0) _
        _ = p * (N / p + 1) := by ring
    exact ⟨N / p, ⟨hm1, hmM⟩, hlower, hupper, hprime⟩
  · rintro ⟨m, ⟨hm1, hmM⟩, hlo, hhi, hprime⟩
    refine ⟨?_, le_trans hhi (Nat.div_le_self N m), hprime⟩
    calc N / (M + 1) ≤ N / (m + 1) := Nat.div_le_div_left (by omega) (by omega)
      _ < p := hlo

/-- **The shells are pairwise disjoint** (`1 ≤ m ≤ M`): a common member `p`
of two shells would have `⌊N/p⌋` equal to both indices
(`div_eq_of_mem_shell`).  This is the paper's "the resulting large-prime
blocks are disjoint" at the level of shell indices, in the form
`Finset.sum_biUnion` consumes. -/
theorem shellPrimes_pairwiseDisjoint (N M : ℕ) :
    Set.PairwiseDisjoint ↑(Icc 1 M) (shellPrimes N) := by
  intro m₁ hm₁ m₂ hm₂ hne
  have h₁ : 1 ≤ m₁ := (mem_Icc.mp (Finset.mem_coe.mp hm₁)).1
  have h₂ : 1 ≤ m₂ := (mem_Icc.mp (Finset.mem_coe.mp hm₂)).1
  show Disjoint (shellPrimes N m₁) (shellPrimes N m₂)
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  exact hne ((div_eq_of_mem_shell h₁ (mem_filter.mp hp₁).1).symm.trans
    (div_eq_of_mem_shell h₂ (mem_filter.mp hp₂).1))

/-- Regrouping a sum over the large primes (with `Q = ⌊N/(M+1)⌋`) into shells,
substituting `⌊N/p⌋ = m` on the `m`-th shell — the summation-side content of
eq. `shell-sum`, generic in the summand. -/
theorem sum_largePrimes_eq_shell_sum (N M : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ largePrimes (N / (M + 1)) N, f p (N / p)
      = ∑ m ∈ Icc 1 M, ∑ p ∈ shellPrimes N m, f p m := by
  rw [largePrimes_eq_biUnion_shellPrimes,
    Finset.sum_biUnion (shellPrimes_pairwiseDisjoint N M)]
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun p hp => ?_
  rw [div_eq_of_mem_shell (mem_Icc.mp hm).1 (mem_filter.mp hp).1]

/-! ## Harmonic-sum bounds (for the fibre error term) -/

/-- `H_N` is Mathlib's `harmonic N`; `harmonicSum` is now definitionally
`harmonic`, so this is `rfl`. -/
theorem harmonicSum_eq_harmonic (N : ℕ) : harmonicSum N = harmonic N := rfl

theorem harmonicSum_nonneg (N : ℕ) : 0 ≤ harmonicSum N := by
  rw [harmonicSum_eq_sum_Icc]
  exact Finset.sum_nonneg fun n _ => by positivity

theorem one_le_harmonicSum {N : ℕ} (hN : 1 ≤ N) : 1 ≤ harmonicSum N := by
  rw [harmonicSum_eq_sum_Icc]
  have h := Finset.single_le_sum (f := fun n : ℕ => (1 : ℚ) / n)
    (fun n _ => by positivity) (mem_Icc.mpr ⟨le_rfl, hN⟩)
  simpa using h

/-- `H_N ≤ 1 + log N`: the elementary harmonic-sum bound that turns the fibre
factor `log(H_N + 1)` of `g_shell_decomposition` into the paper's `O(log X)`
error in eq. `shell-sum` (`prop:averaging-relation`).  Holds for all `N`
(for `N = 0` both sides degenerate: `H_0 = 0 ≤ 1`). -/
theorem harmonicSum_le_one_add_log (N : ℕ) :
    ((harmonicSum N : ℚ) : ℝ) ≤ 1 + Real.log N := by
  rw [harmonicSum_eq_harmonic]
  exact harmonic_le_one_add_log N

/-! ## The shell decomposition of `g(N)` -/

/-- **Shell decomposition of `g(N)`** — eq. `shell-sum` of
`prop:averaging-relation`, with the paper's `O(log 𝔇_Q + log X)` error made
explicit: under the hypotheses of `prop:large-prime-decomposition` for
`Q = ⌊N/(M+1)⌋`,
```
∑_{m ≤ M} ∑_{p ∈ shell m} log σ_p(m)  ≤  g(N)
  ≤  ∑_{m ≤ M} ∑_{p ∈ shell m} log σ_p(m) + log(H_N + 1) + log 𝔇_Q(N).
```
The lower bound is exact (no error term); the upper-bound error
`log(H_N + 1) + log 𝔇_Q` bounds the paper's fibre factor
`log(⌊H_N·𝔇_Q⌋ + 1)`, and becomes `O(log X) + O(log 𝔇_Q)` via
`harmonicSum_le_one_add_log` and `log_smoothPart_le`. -/
theorem g_shell_decomposition {N M : ℕ} (hQN : N / (M + 1) < N)
    (hQ2 : N < N / (M + 1) * (N / (M + 1))) :
    (∑ m ∈ Icc 1 M, ∑ p ∈ shellPrimes N m, Real.log (sigma p m)) ≤ g N ∧
      g N ≤ (∑ m ∈ Icc 1 M, ∑ p ∈ shellPrimes N m, Real.log (sigma p m))
        + Real.log ((harmonicSum N : ℝ) + 1)
        + Real.log (smoothPart (N / (M + 1)) N) := by
  -- the large-prime product, its positivity, and its log as the shell sum
  have hprodpos : 0 < ∏ p ∈ largePrimes (N / (M + 1)) N, sigma p (N / p) :=
    Finset.prod_pos fun p _ => one_le_sigma p (N / p)
  have hlogProd :
      Real.log ((∏ p ∈ largePrimes (N / (M + 1)) N, sigma p (N / p) : ℕ) : ℝ)
        = ∑ m ∈ Icc 1 M, ∑ p ∈ shellPrimes N m, Real.log (sigma p m) := by
    rw [Nat.cast_prod, Real.log_prod fun p _ =>
      Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp (one_le_sigma p (N / p)))]
    exact sum_largePrimes_eq_shell_sum N M fun p m => Real.log (sigma p m)
  constructor
  · -- lower half: `log ∏ σ ≤ log S(N)` from `prod_sigma_le_S`
    rw [← hlogProd]
    exact Real.log_le_log (by exact_mod_cast hprodpos)
      (by exact_mod_cast prod_sigma_le_S hQN hQ2)
  · -- upper half: `log S(N) ≤ log(⌊H·D⌋+1) + log ∏ σ`, then bound the fibre
    -- factor by `log(H+1) + log D` using `⌊H·D⌋ + 1 ≤ (H+1)·D` (valid since
    -- `H ≥ 0` and `D ≥ 1`)
    have hstep1 : g N ≤ Real.log
        (((⌊harmonicSum N * (smoothPart (N / (M + 1)) N : ℚ)⌋₊ + 1)
          * ∏ p ∈ largePrimes (N / (M + 1)) N, sigma p (N / p) : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast S_pos N)
        (by exact_mod_cast S_le_fibre_mul_prod_sigma hQN hQ2)
    rw [Nat.cast_mul, Real.log_mul
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
      (by exact_mod_cast hprodpos.ne'), hlogProd] at hstep1
    have hH0 : (0 : ℝ) ≤ ((harmonicSum N : ℚ) : ℝ) := by
      exact_mod_cast harmonicSum_nonneg N
    have hD1 : (1 : ℝ) ≤ ((smoothPart (N / (M + 1)) N : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (smoothPart_ne_zero (N / (M + 1)) N)
    have hflR : ((⌊harmonicSum N * (smoothPart (N / (M + 1)) N : ℚ)⌋₊ : ℕ) : ℝ)
        ≤ ((harmonicSum N : ℚ) : ℝ) * ((smoothPart (N / (M + 1)) N : ℕ) : ℝ) := by
      exact_mod_cast Nat.floor_le
        (mul_nonneg (harmonicSum_nonneg N)
          (Nat.cast_nonneg (smoothPart (N / (M + 1)) N)))
    have hHD : ((⌊harmonicSum N * (smoothPart (N / (M + 1)) N : ℚ)⌋₊ + 1 : ℕ) : ℝ)
        ≤ (((harmonicSum N : ℚ) : ℝ) + 1)
          * ((smoothPart (N / (M + 1)) N : ℕ) : ℝ) := by
      push_cast
      nlinarith [hflR, hD1, hH0]
    have hlogfl : Real.log
        ((⌊harmonicSum N * (smoothPart (N / (M + 1)) N : ℚ)⌋₊ + 1 : ℕ) : ℝ)
        ≤ Real.log (((harmonicSum N : ℚ) : ℝ) + 1)
          + Real.log ((smoothPart (N / (M + 1)) N : ℕ) : ℝ) := by
      have hpos : (0 : ℝ) <
          ((⌊harmonicSum N * (smoothPart (N / (M + 1)) N : ℚ)⌋₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos _
      calc Real.log
            ((⌊harmonicSum N * (smoothPart (N / (M + 1)) N : ℚ)⌋₊ + 1 : ℕ) : ℝ)
          ≤ Real.log ((((harmonicSum N : ℚ) : ℝ) + 1)
              * ((smoothPart (N / (M + 1)) N : ℕ) : ℝ)) :=
            Real.log_le_log hpos hHD
        _ = Real.log (((harmonicSum N : ℚ) : ℝ) + 1)
              + Real.log ((smoothPart (N / (M + 1)) N : ℕ) : ℝ) :=
            Real.log_mul (by linarith) (by linarith)
    linarith [hstep1, hlogfl]

/-! ## The smooth-core estimate `log 𝔇_Q ≤ ϑ(Q) + √N·log N` -/

/-- `ϑ` at a natural argument is the sum of `log q` over the primes
`q ∈ {1, …, Q}` — the bridge between `chebyshevTheta` (indexed by
`Iic ⌊(Q:ℝ)⌋₊`) and the index set of `smoothPart` (indexed by `Icc 1 Q`);
the two agree because `0` is not prime. -/
theorem chebyshevTheta_natCast_eq_sum_primes (Q : ℕ) :
    chebyshevTheta (Q : ℝ)
      = ∑ q ∈ (Icc 1 Q).filter Nat.Prime, Real.log q := by
  rw [chebyshevTheta, Nat.floor_natCast]
  apply Finset.sum_congr _ fun _ _ => rfl
  ext q
  simp only [mem_filter, Finset.mem_Iic, mem_Icc]
  exact ⟨fun h => ⟨⟨h.2.one_lt.le, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩

/-- **Smooth-core estimate** (proof of `prop:averaging-relation`, after
eq. `shell-sum`): `log 𝔇_Q(N) ≤ ϑ(Q) + √N · log N`.  The paper's
`lem:prime-power-splitting` isolates the first layer `ϑ(Q)`, with all
higher layers contributing `O(√N log N)`; here the higher
layers are bounded explicitly by `√N · log N` (each of the at most `√N`
primes with `q² ≤ N` contributes `(⌊log N/log q⌋ − 1)·log q ≤ log N`), i.e.
the paper's shape with explicit constant `1`. -/
theorem log_smoothPart_le {Q N : ℕ} (hQ : 2 ≤ Q) (hQN : Q ≤ N) :
    Real.log (smoothPart Q N) ≤ chebyshevTheta Q + Real.sqrt N * Real.log N := by
  have hN0 : N ≠ 0 := by omega
  have hlogN0 : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN0)
  -- `log 𝔇_Q` as the prime-power layer sum `∑ (Nat.log q N) · log q`
  have hlog : Real.log ((smoothPart Q N : ℕ) : ℝ)
      = ∑ q ∈ (Icc 1 Q).filter Nat.Prime, (Nat.log q N : ℝ) * Real.log q := by
    rw [smoothPart, Nat.cast_prod, Real.log_prod fun q hq =>
      Nat.cast_ne_zero.mpr (pow_ne_zero _ (mem_filter.mp hq).2.pos.ne')]
    exact Finset.sum_congr rfl fun q _ => by rw [Nat.cast_pow, Real.log_pow]
  -- split each prime's contribution into first layer + higher layers
  have hsplit : ∀ q ∈ (Icc 1 Q).filter Nat.Prime,
      (Nat.log q N : ℝ) * Real.log q
        = Real.log q + ((Nat.log q N - 1 : ℕ) : ℝ) * Real.log q := by
    intro q hq
    obtain ⟨hq_mem, hq_prime⟩ := mem_filter.mp hq
    have hL1 : 1 ≤ Nat.log q N :=
      Nat.log_pos hq_prime.one_lt (le_trans (mem_Icc.mp hq_mem).2 hQN)
    rw [Nat.cast_sub hL1, Nat.cast_one]
    ring
  -- the higher layers: supported on primes with `q² ≤ N`, each term `≤ log N`
  have hS₂ : ∑ q ∈ (Icc 1 Q).filter Nat.Prime,
      ((Nat.log q N - 1 : ℕ) : ℝ) * Real.log q ≤ Real.sqrt N * Real.log N := by
    have hvanish : ∀ q ∈ (Icc 1 Q).filter Nat.Prime,
        q ∉ ((Icc 1 Q).filter Nat.Prime).filter (fun q => 2 ≤ Nat.log q N) →
        ((Nat.log q N - 1 : ℕ) : ℝ) * Real.log q = 0 := by
      intro q hq hq2
      have hle : ¬ 2 ≤ Nat.log q N := fun h => hq2 (mem_filter.mpr ⟨hq, h⟩)
      have hL : Nat.log q N - 1 = 0 := by omega
      rw [hL, Nat.cast_zero, zero_mul]
    rw [← Finset.sum_subset (Finset.filter_subset _ _) hvanish]
    have hterm : ∀ q ∈ ((Icc 1 Q).filter Nat.Prime).filter
        (fun q => 2 ≤ Nat.log q N),
        ((Nat.log q N - 1 : ℕ) : ℝ) * Real.log q ≤ Real.log N := by
      intro q hq
      have hq_prime : q.Prime := (mem_filter.mp (mem_filter.mp hq).1).2
      have hlogq0 : 0 ≤ Real.log q :=
        Real.log_nonneg (by exact_mod_cast hq_prime.one_lt.le)
      calc ((Nat.log q N - 1 : ℕ) : ℝ) * Real.log q
          ≤ (Nat.log q N : ℝ) * Real.log q :=
            mul_le_mul_of_nonneg_right
              (by exact_mod_cast Nat.sub_le (Nat.log q N) 1) hlogq0
        _ = Real.log ((q : ℝ) ^ Nat.log q N) := (Real.log_pow _ _).symm
        _ ≤ Real.log N := by
            apply Real.log_le_log
              (pow_pos (by exact_mod_cast hq_prime.pos) _)
            exact_mod_cast Nat.pow_log_le_self q hN0
    have hsqrtsub : ((Icc 1 Q).filter Nat.Prime).filter
        (fun q => 2 ≤ Nat.log q N) ⊆ Icc 1 (Nat.sqrt N) := by
      intro q hq
      obtain ⟨hqP, hqL⟩ := mem_filter.mp hq
      have hq_prime : q.Prime := (mem_filter.mp hqP).2
      have hqq : q * q ≤ N := by
        calc q * q = q ^ 2 := (pow_two q).symm
          _ ≤ q ^ Nat.log q N := Nat.pow_le_pow_right hq_prime.pos hqL
          _ ≤ N := Nat.pow_log_le_self q hN0
      exact mem_Icc.mpr ⟨hq_prime.one_lt.le, Nat.le_sqrt.mpr hqq⟩
    have hcard : ((((Icc 1 Q).filter Nat.Prime).filter
        (fun q => 2 ≤ Nat.log q N)).card : ℝ) ≤ Real.sqrt N := by
      calc ((((Icc 1 Q).filter Nat.Prime).filter
            (fun q => 2 ≤ Nat.log q N)).card : ℝ)
          ≤ ((Icc 1 (Nat.sqrt N)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsqrtsub
        _ = (Nat.sqrt N : ℝ) := by rw [Nat.card_Icc]; norm_num
        _ ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
    calc ∑ q ∈ ((Icc 1 Q).filter Nat.Prime).filter (fun q => 2 ≤ Nat.log q N),
          ((Nat.log q N - 1 : ℕ) : ℝ) * Real.log q
        ≤ ∑ _q ∈ ((Icc 1 Q).filter Nat.Prime).filter
            (fun q => 2 ≤ Nat.log q N), Real.log N :=
          Finset.sum_le_sum hterm
      _ = ((((Icc 1 Q).filter Nat.Prime).filter
            (fun q => 2 ≤ Nat.log q N)).card : ℝ) * Real.log N := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.sqrt N * Real.log N :=
          mul_le_mul_of_nonneg_right hcard hlogN0
  calc Real.log ((smoothPart Q N : ℕ) : ℝ)
      = ∑ q ∈ (Icc 1 Q).filter Nat.Prime, (Nat.log q N : ℝ) * Real.log q :=
        hlog
    _ = ∑ q ∈ (Icc 1 Q).filter Nat.Prime,
          (Real.log q + ((Nat.log q N - 1 : ℕ) : ℝ) * Real.log q) :=
        Finset.sum_congr rfl hsplit
    _ = (∑ q ∈ (Icc 1 Q).filter Nat.Prime, Real.log q)
          + ∑ q ∈ (Icc 1 Q).filter Nat.Prime,
              ((Nat.log q N - 1 : ℕ) : ℝ) * Real.log q :=
        Finset.sum_add_distrib
    _ ≤ chebyshevTheta Q + Real.sqrt N * Real.log N := by
        rw [chebyshevTheta_natCast_eq_sum_primes]
        exact add_le_add le_rfl hS₂

end Erdos320
