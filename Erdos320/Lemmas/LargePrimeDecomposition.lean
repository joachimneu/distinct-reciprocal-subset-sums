import Erdos320.Defs.RatToZMod
import Erdos320.Defs.HarmonicSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Fintype.BigOperators

/-!
# Exact large-prime decomposition (`prop:large-prime-decomposition`)

The manuscript's Proposition `prop:large-prime-decomposition`
(§ `sec:large-prime-decomposition`, eq. `exact-large-prime-decomposition`):
for an integer `Q < N` with `Q² > N`, and with `M = ⌊N/(Q+1)⌋`,
```
∏_{Q < p ≤ N} σ_p(⌊N/p⌋)  ≤  S(N)  ≤  (⌊H_N · 𝔇_Q(N)⌋ + 1) · ∏_{Q < p ≤ N} σ_p(⌊N/p⌋),
```
where `𝔇_Q(N) = ∏_{q ≤ Q prime} q^{⌊log N / log q⌋}` is the smooth
denominator of eq. `smooth-denominator-def` (here `smoothPart Q N`, with
`Nat.log q N = ⌊log N / log q⌋`), `H_N` is the harmonic sum, the products
run over primes, and `σ_p` is the modular subset-sum image size of
eq. `sigma-def` (here `sigma`).

The two halves are `prod_sigma_le_S` and `S_le_fibre_mul_prod_sigma` below.

Following the paper's proof, the heart is the *coordinate map*: for a large
prime `p` (i.e. `Q < p ≤ N`), multiplication by `p` followed by reduction
modulo `p` (`coord p` below, built on `ratToZMod`) sends every reciprocal
subset sum in `𝓔_N` into the modular image `Σ_p(⌊N/p⌋)`
(`coord_mem_modularImage`), because `Q² > N` forces every `n ≤ N` to have at
most one prime factor above `Q` and the large-prime blocks
`{p, 2p, …, ⌊N/p⌋p}` to be pairwise disjoint.

* Lower bound: any choice of one coordinate value per large prime is realized
  simultaneously by a single subset (the blocks are disjoint), so the
  coordinate vector map is surjective onto the product of the modular images
  (`prod_sigma_le_S` via `realizeSet` and `coord_realize`).
* Upper bound: two elements of `𝓔_N` with the same coordinate vector differ
  by a rational whose reduced denominator is `Q`-smooth with prime powers at
  most `N`, i.e. divides `𝔇_Q(N)` (`den_sub_dvd_smoothPart`); since all
  subset sums lie in `[0, H_N]`, each fibre has at most `⌊H_N·𝔇_Q(N)⌋ + 1`
  elements (`fibre_card_le`).

As in the paper, the proposition takes no `Q > M` hypothesis: `Q > M`
(`N / (Q + 1) < Q`) is already implied by `N < Q²` — the paper's in-proof
display `M ≤ N/(Q+1) < Q²/(Q+1) < Q` — so it is derived inside the proof.
Here the block-disjointness step (`filter_realizeSet`) obtains it from
`Q² > N` via `div_Q_add_one_lt_Q_of_lt_Q_mul_Q` below.
-/

namespace Erdos320

open Finset

/-- `smoothPart Q N` is the paper's smooth-core denominator bound
`𝔇_Q(N) = ∏_{q ≤ Q prime} q^{⌊log N / log q⌋}` (eq. `smooth-denominator-def`)
from `prop:large-prime-decomposition` (for `q ≥ 2` one has
`Nat.log q N = ⌊log N / log q⌋`, the largest `e` with `q^e ≤ N`). -/
def smoothPart (Q N : ℕ) : ℕ :=
  ∏ q ∈ (Icc 1 Q).filter Nat.Prime, q ^ Nat.log q N

/-- `largePrimes Q N` is the index set of the paper's products
`∏_{Q < p ≤ N}` over primes in `prop:large-prime-decomposition`. -/
def largePrimes (Q N : ℕ) : Finset ℕ := (Ioc Q N).filter Nat.Prime

theorem mem_largePrimes {Q N p : ℕ} :
    p ∈ largePrimes Q N ↔ Q < p ∧ p ≤ N ∧ p.Prime := by
  simp [largePrimes, mem_filter, mem_Ioc, and_assoc]

/-- `Q > M = ⌊N/(Q+1)⌋` follows from `Q² > N`, so
`prop:large-prime-decomposition` needs no separate `Q > M` hypothesis: this
is the paper's in-proof display `M ≤ N/(Q+1) < Q²/(Q+1) < Q`, consumed at
the block-disjointness step (see `filter_realizeSet`). -/
theorem div_Q_add_one_lt_Q_of_lt_Q_mul_Q {Q N : ℕ} (hQ2 : N < Q * Q) :
    N / (Q + 1) < Q := by
  rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos Q)]
  calc N < Q * Q := hQ2
    _ ≤ Q * (Q + 1) := Nat.mul_le_mul_left Q (Nat.le_succ Q)

theorem smoothPart_ne_zero (Q N : ℕ) : smoothPart Q N ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _q hq =>
    pow_ne_zero _ (mem_filter.mp hq).2.pos.ne'

/-- The prime factorization of `smoothPart Q N = 𝔇_Q(N)`: exponent
`Nat.log q N` at each prime `q ≤ Q`, and `0` elsewhere. -/
theorem factorization_smoothPart (Q N q : ℕ) :
    (smoothPart Q N).factorization q
      = if q.Prime ∧ q ≤ Q then Nat.log q N else 0 := by
  classical
  rw [smoothPart, Nat.factorization_prod fun r hr =>
    pow_ne_zero _ (mem_filter.mp hr).2.pos.ne']
  rw [Finset.sum_apply']
  rw [Finset.sum_congr rfl fun r hr => by
    rw [(mem_filter.mp hr).2.factorization_pow, Finsupp.single_apply]]
  rw [Finset.sum_ite_eq' ((Icc 1 Q).filter Nat.Prime) q fun r => Nat.log r N]
  by_cases hq : q.Prime ∧ q ≤ Q
  · rw [if_pos hq, if_pos (mem_filter.mpr ⟨mem_Icc.mpr ⟨hq.1.one_lt.le, hq.2⟩, hq.1⟩)]
  · rw [if_neg hq, if_neg fun hmem => hq
      ⟨(mem_filter.mp hmem).2, (mem_Icc.mp (mem_filter.mp hmem).1).2⟩]

/-- Every `n ∈ {1, …, N}` divides `𝔇_N(N)` — this is the paper's "every
prime-power denominator occurring before reduction is at most `N`" packaged
as a single universal denominator (a substitute for `lcm(1, …, N)`, with
directly computable factorization). -/
theorem dvd_smoothPart_of_le {n N : ℕ} (h1 : 1 ≤ n) (hnN : n ≤ N) :
    n ∣ smoothPart N N := by
  rw [← Nat.factorization_le_iff_dvd (by omega) (smoothPart_ne_zero N N),
    Finsupp.le_def]
  intro q
  rw [factorization_smoothPart]
  by_cases hq : q.Prime
  · rcases Nat.eq_zero_or_pos (n.factorization q) with h0 | hpos
    · simp [h0]
    · have hqn : q ∣ n := Nat.dvd_of_factorization_pos hpos.ne'
      have hqN : q ≤ N := le_trans (Nat.le_of_dvd (by omega) hqn) hnN
      rw [if_pos ⟨hq, hqN⟩]
      exact Nat.le_log_of_pow_le hq.one_lt
        (le_trans (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n q)) hnN)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

/-! ### Denominator bookkeeping for rationals

Auxiliary facts relating "`z · L` is an integer" (recorded as
`(z * L).den = 1`) to divisibility of the reduced denominator of `z`.
-/

/-- A difference of two rationals with denominator `1` has denominator `1`. -/
theorem den_sub_eq_one {a b : ℚ} (ha : a.den = 1) (hb : b.den = 1) :
    (a - b).den = 1 := by
  have ha' : ((a.num : ℤ) : ℚ) = a := (Rat.den_eq_one_iff _).mp ha
  have hb' : ((b.num : ℤ) : ℚ) = b := (Rat.den_eq_one_iff _).mp hb
  have h : a - b = ((a.num - b.num : ℤ) : ℚ) := by push_cast; rw [ha', hb']
  rw [h, Rat.den_intCast]

/-- If the reduced denominator of `z` divides `D`, then `z · D` is an
integer. -/
theorem mul_natCast_den_eq_one_of_den_dvd {z : ℚ} {D : ℕ} (h : z.den ∣ D) :
    (z * (D : ℚ)).den = 1 := by
  obtain ⟨c, hc⟩ := h
  have hzD : z * (D : ℚ) = ((z.num * c : ℤ) : ℚ) := by
    subst hc
    push_cast
    linear_combination (c : ℚ) * Rat.mul_den_eq_num z
  rw [hzD, Rat.den_intCast]

/-- Conversely, if `z · L` is an integer then the reduced denominator of `z`
divides `L`. -/
theorem den_dvd_of_mul_natCast_den_eq_one {z : ℚ} {L : ℕ}
    (h : (z * (L : ℚ)).den = 1) : z.den ∣ L := by
  have h1 : ((z * (L : ℚ)).num : ℚ) = z * (L : ℚ) := (Rat.den_eq_one_iff _).mp h
  have hab : z * ((L : ℤ) : ℚ) = ((z * (L : ℚ)).num : ℚ) := by
    push_cast at h1 ⊢
    linear_combination -h1
  have key : z.num * (L : ℤ) = (z * (L : ℚ)).num * (z.den : ℤ) :=
    num_mul_eq_of_mul_intCast_eq hab
  have hdvd : (z.den : ℤ) ∣ z.num * (L : ℤ) :=
    ⟨(z * (L : ℚ)).num, by linear_combination key⟩
  have hnat : z.den ∣ z.num.natAbs * L := by
    have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa [Int.natAbs_mul] using h2
  exact Nat.Coprime.dvd_of_dvd_mul_left z.reduced.symm hnat

/-- Every reciprocal subset sum in `𝓔_N` becomes an integer after
multiplication by the universal denominator `D_N(N)`. -/
theorem mul_smoothPart_den_eq_one {N : ℕ} {x : ℚ}
    (hx : x ∈ reciprocalSubsetSumSet N) :
    (x * (smoothPart N N : ℚ)).den = 1 := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
  have hA' : A ⊆ Icc 1 N := mem_powerset.mp hA
  have hsum : (∑ n ∈ A, (1 : ℚ) / n) * (smoothPart N N : ℚ)
      = ((∑ n ∈ A, smoothPart N N / n : ℕ) : ℚ) := by
    rw [Finset.sum_mul, Nat.cast_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨h1, _⟩ := mem_Icc.mp (hA' hn)
    have hdvd : n ∣ smoothPart N N :=
      dvd_smoothPart_of_le h1 (mem_Icc.mp (hA' hn)).2
    have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.cast_div hdvd hn0, one_div, inv_mul_eq_div]
  have hcast : ((∑ n ∈ A, smoothPart N N / n : ℕ) : ℚ)
      = (((∑ n ∈ A, smoothPart N N / n : ℕ) : ℤ) : ℚ) :=
    (Int.cast_natCast _).symm
  rw [hsum, hcast, Rat.den_intCast]

/-! ### The coordinate map -/

/-- The `p`-coordinate of a rational `x`: "multiplication by `p` followed by
reduction modulo `p`" from the proof of `prop:large-prime-decomposition`.
For `x ∈ 𝓔_N` and a large prime `p`, the factor `p` cancels the (unique)
`p` in the denominators of the `p`-block terms and kills all other terms
(see `coord_sum_reciprocals`). -/
def coord (p : ℕ) (x : ℚ) : ZMod p := ratToZMod p ((p : ℚ) * x)

theorem coord_def (p : ℕ) (x : ℚ) :
    coord p x = ratToZMod p ((p : ℚ) * x) := rfl

/-- **Coordinate computation.** For a prime `p` with `p² > N` and a subset
`A ⊆ {1, …, N}`, the `p`-coordinate of `∑_{n ∈ A} 1/n` is the modular subset
sum `∑ (n/p)⁻¹` over the members of `A` divisible by `p`: terms `n = pk`
contribute `k⁻¹ (mod p)`, all other terms are annihilated by the factor `p`. -/
theorem coord_sum_reciprocals {p N : ℕ} (hp : p.Prime) (hNpp : N < p * p)
    {A : Finset ℕ} (hA : A ⊆ Icc 1 N) :
    coord p (∑ n ∈ A, (1 : ℚ) / n)
      = ∑ n ∈ A.filter (p ∣ ·), ((n / p : ℕ) : ZMod p)⁻¹ := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  rw [coord_def, Finset.mul_sum]
  have hden : ∀ n ∈ A, ¬ p ∣ ((p : ℚ) * ((1 : ℚ) / n)).den := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Icc.mp (hA hn)
    by_cases hpn : p ∣ n
    · obtain ⟨k, rfl⟩ := hpn
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · rw [Nat.mul_zero] at h1; omega
        · exact h
      have hkp : k < p := Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h2 hNpp)
      have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hbk : ¬ (p : ℤ) ∣ (k : ℤ) := by
        rw [Int.natCast_dvd_natCast]
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      refine not_dvd_den_of_mul_intCast_eq hp hbk (a := 1) ?_
      push_cast
      field_simp
    · have hbn : ¬ (p : ℤ) ∣ (n : ℤ) := fun hd => hpn (Int.natCast_dvd_natCast.mp hd)
      have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      refine not_dvd_den_of_mul_intCast_eq hp hbn (a := (p : ℤ)) ?_
      push_cast
      field_simp
  rw [ratToZMod_sum hp hden, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨h1, h2⟩ := mem_Icc.mp (hA hn)
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    obtain ⟨k, rfl⟩ := hpn
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · rw [Nat.mul_zero] at h1; omega
      · exact h
    have hkp : k < p := Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h2 hNpp)
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hnpk : ¬ p ∣ k := fun hd => by
      have := Nat.le_of_dvd (by omega) hd
      omega
    rw [Nat.mul_div_cancel_left k hp.pos]
    have heq : (p : ℚ) * ((1 : ℚ) / ((p * k : ℕ) : ℚ)) = 1 / (k : ℚ) := by
      push_cast
      field_simp
    rw [heq, ratToZMod_inv_natCast hp hnpk]
  · rw [if_neg hpn]
    have h1n : ¬ p ∣ ((1 : ℚ) / (n : ℚ)).den := by
      have hbn : ¬ (p : ℤ) ∣ (n : ℤ) := fun hd => hpn (Int.natCast_dvd_natCast.mp hd)
      have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      refine not_dvd_den_of_mul_intCast_eq hp hbn (a := 1) ?_
      push_cast
      field_simp
    rw [ratToZMod_natCast_mul hp p h1n, ZMod.natCast_self, zero_mul]

/-- The `p`-coordinate of any element of `𝓔_N` lies in the modular image
`Σ_p(⌊N/p⌋)` (for a prime `p` with `p² > N`); this is the "sends its subset
sums to `Σ_p(⌊N/p⌋)`" step of `prop:large-prime-decomposition`. -/
theorem coord_mem_modularImage {N p : ℕ} (hp : p.Prime) (hNpp : N < p * p)
    {x : ℚ} (hx : x ∈ reciprocalSubsetSumSet N) :
    coord p x ∈ modularImage p (N / p) := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
  have hA' : A ⊆ Icc 1 N := mem_powerset.mp hA
  rw [coord_sum_reciprocals hp hNpp hA']
  have hinj : ∀ n₁ ∈ A.filter (p ∣ ·), ∀ n₂ ∈ A.filter (p ∣ ·),
      n₁ / p = n₂ / p → n₁ = n₂ := by
    intro n₁ h₁ n₂ h₂ h
    have d₁ := (mem_filter.mp h₁).2
    have d₂ := (mem_filter.mp h₂).2
    rw [← Nat.div_mul_cancel d₁, ← Nat.div_mul_cancel d₂, h]
  refine Finset.mem_image.mpr
    ⟨(A.filter (p ∣ ·)).image (· / p), mem_powerset.mpr ?_, Finset.sum_image hinj⟩
  intro k hk
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hnA, hpn⟩ := mem_filter.mp hn
  obtain ⟨h1, h2⟩ := mem_Icc.mp (hA' hnA)
  rw [mem_Icc]
  exact ⟨(Nat.one_le_div_iff hp.pos).mpr (Nat.le_of_dvd (by omega) hpn),
    Nat.div_le_div_right h2⟩

/-! ### Lower bound: joint realization of all coordinates -/

/-- A chosen subset `B ⊆ {1, …, m}` realizing a given value of the modular
image `Σ_p(m)` (an arbitrary preimage under the subset-sum map; `∅`,
realizing `0`, for values outside the image). -/
noncomputable def modularPreimage (p m : ℕ) (c : ZMod p) : Finset ℕ :=
  if hc : c ∈ modularImage p m then (Finset.mem_image.mp hc).choose else ∅

theorem modularPreimage_subset (p m : ℕ) (c : ZMod p) :
    modularPreimage p m c ⊆ Icc 1 m := by
  rw [modularPreimage]
  split_ifs with hc
  · exact mem_powerset.mp (Finset.mem_image.mp hc).choose_spec.1
  · exact empty_subset _

theorem sum_modularPreimage {p m : ℕ} {c : ZMod p}
    (hc : c ∈ modularImage p m) :
    ∑ k ∈ modularPreimage p m c, (k : ZMod p)⁻¹ = c := by
  rw [modularPreimage, dif_pos hc]
  exact (Finset.mem_image.mp hc).choose_spec.2

/-- Given a choice of one coordinate value per large prime, the subset of
`{1, …, N}` realizing all of them simultaneously: the union over the large
primes `p` of the `p`-block `{pk : k ∈ B_p}`, where `B_p ⊆ {1, …, ⌊N/p⌋}`
realizes the chosen value in `Σ_p(⌊N/p⌋)`.  The blocks are pairwise disjoint
(the paper's "an equality `pk = p'k'` with `p ≠ p'` would imply `p ∣ k'`,
although `k' ≤ M < p`"), which is `filter_realizeSet` below. -/
noncomputable def realizeSet (Q N : ℕ) (f : ∀ p ∈ largePrimes Q N, ZMod p) :
    Finset ℕ :=
  (largePrimes Q N).attach.biUnion fun p =>
    (modularPreimage p.1 (N / p.1) (f p.1 p.2)).image (p.1 * ·)

theorem realizeSet_subset {Q N : ℕ} (f : ∀ p ∈ largePrimes Q N, ZMod p) :
    realizeSet Q N f ⊆ Icc 1 N := by
  intro n hn
  simp only [realizeSet, Finset.mem_biUnion, Finset.mem_attach, true_and] at hn
  obtain ⟨⟨p, hp⟩, hn⟩ := hn
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hk1, hk2⟩ := mem_Icc.mp (modularPreimage_subset _ _ _ hk)
  have hppos : 0 < p := (mem_largePrimes.mp hp).2.2.pos
  rw [mem_Icc]
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hppos.ne' (by omega))
  · calc p * k ≤ p * (N / p) := Nat.mul_le_mul_left p hk2
      _ ≤ N := Nat.mul_div_le N p

/-- **Block disjointness.** For a large prime `p`, the members of
`realizeSet Q N f` divisible by `p` are exactly the `p`-block: a member
`p' · k'` of another block cannot be divisible by `p`, since that would force
`p ∣ k'` while `k' ≤ ⌊N/p'⌋ ≤ ⌊N/(Q+1)⌋ < Q < p`.  This is where the fact
`Q > M = ⌊N/(Q+1)⌋` enters the proof of `prop:large-prime-decomposition`;
it is derived here from `Q² > N` via `div_Q_add_one_lt_Q_of_lt_Q_mul_Q`,
exactly as in the paper. -/
theorem filter_realizeSet {Q N : ℕ} (hQ2 : N < Q * Q)
    (f : ∀ p ∈ largePrimes Q N, ZMod p) {p : ℕ} (hp : p ∈ largePrimes Q N) :
    (realizeSet Q N f).filter (p ∣ ·)
      = (modularPreimage p (N / p) (f p hp)).image (p * ·) := by
  have hQM : N / (Q + 1) < Q := div_Q_add_one_lt_Q_of_lt_Q_mul_Q hQ2
  ext n
  simp only [mem_filter, realizeSet, Finset.mem_biUnion, Finset.mem_attach,
    true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨p', hp'⟩, k, hk, rfl⟩, hpdvd⟩
    by_cases hpp' : p' = p
    · subst hpp'
      exact ⟨k, hk, rfl⟩
    · exfalso
      obtain ⟨hk1, hk2⟩ := mem_Icc.mp (modularPreimage_subset _ _ _ hk)
      obtain ⟨hQp', hp'N, hp'prime⟩ := mem_largePrimes.mp hp'
      obtain ⟨hQp, hpN, hpprime⟩ := mem_largePrimes.mp hp
      have hpk : p ∣ k := by
        rcases (Nat.Prime.dvd_mul hpprime).mp hpdvd with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hpprime hp'prime).mp h)
            fun he => hpp' he.symm
        · exact h
      have hkQ : k < Q :=
        lt_of_le_of_lt (le_trans hk2 (Nat.div_le_div_left hQp' (by omega))) hQM
      have hple : p ≤ k := Nat.le_of_dvd (by omega) hpk
      omega
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨⟨p, hp⟩, k, hk, rfl⟩, dvd_mul_right p k⟩

/-- The realizing subset does realize every chosen coordinate: for each large
prime `p`, the `p`-coordinate of `∑_{n ∈ realizeSet} 1/n` is the chosen value
`f p`. -/
theorem coord_realize {Q N : ℕ} (hQ2 : N < Q * Q)
    {f : ∀ p ∈ largePrimes Q N, ZMod p}
    (hf : ∀ p (hp : p ∈ largePrimes Q N), f p hp ∈ modularImage p (N / p))
    {p : ℕ} (hp : p ∈ largePrimes Q N) :
    coord p (∑ n ∈ realizeSet Q N f, (1 : ℚ) / n) = f p hp := by
  obtain ⟨hQp, hpN, hprime⟩ := mem_largePrimes.mp hp
  have hNpp : N < p * p := lt_of_lt_of_le hQ2 (Nat.mul_le_mul hQp.le hQp.le)
  rw [coord_sum_reciprocals hprime hNpp (realizeSet_subset f),
    filter_realizeSet hQ2 f hp,
    Finset.sum_image fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hprime.pos h]
  rw [Finset.sum_congr rfl fun k _ => by
    rw [Nat.mul_div_cancel_left k hprime.pos]]
  exact sum_modularPreimage (hf p hp)

/-- **Lower half of eq. `exact-large-prime-decomposition`:**
`∏_{Q < p ≤ N} σ_p(⌊N/p⌋) ≤ S(N)`.  Every vector of coordinate values is
realized by an element of `𝓔_N` (`coord_realize`), and distinct vectors give
distinct elements since the coordinates are functions of the rational value
alone.  (The paper's hypothesis `Q < N` is carried for fidelity to
`prop:large-prime-decomposition` but is not needed for this half.) -/
theorem prod_sigma_le_S {N Q : ℕ} (_hQN : Q < N) (hQ2 : N < Q * Q) :
    (∏ p ∈ largePrimes Q N, sigma p (N / p)) ≤ S N := by
  classical
  have hcard : ((largePrimes Q N).pi fun p => modularImage p (N / p)).card
      = ∏ p ∈ largePrimes Q N, sigma p (N / p) := Finset.card_pi _ _
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun f => ∑ n ∈ realizeSet Q N f, (1 : ℚ) / n) (fun f hf => ?_)
    (fun f hf g hg hfg => ?_)
  · exact Finset.mem_image.mpr
      ⟨realizeSet Q N f, mem_powerset.mpr (realizeSet_subset f), rfl⟩
  · funext p hp
    have hf' := Finset.mem_pi.mp (Finset.mem_coe.mp hf)
    have hg' := Finset.mem_pi.mp (Finset.mem_coe.mp hg)
    have hfg' : (∑ n ∈ realizeSet Q N f, (1 : ℚ) / n)
        = ∑ n ∈ realizeSet Q N g, (1 : ℚ) / n := hfg
    rw [← coord_realize hQ2 hf' hp, ← coord_realize hQ2 hg' hp, hfg']

/-! ### Upper bound: fibres of the coordinate vector are small -/

/-- **Coordinate rigidity.** If `x · L` and `y · L` are integers, `p` is a
prime with `p ∣∣ L` at most to the first power (`¬ p² ∣ L`), and `x, y` have
the same `p`-coordinate, then `p` does not divide the reduced denominator of
`x - y`.  (Applied with `L = D_N(N)`, `Q < p ≤ N`: this is "the difference of
any two subset sums in the resulting fibre has no prime larger than `Q` in
its reduced denominator".) -/
theorem not_dvd_den_sub_of_coord_eq {p L : ℕ} (hp : p.Prime) (hL0 : L ≠ 0)
    (hppL : ¬ p * p ∣ L) {x y : ℚ}
    (hxL : (x * (L : ℚ)).den = 1) (hyL : (y * (L : ℚ)).den = 1)
    (hcoord : coord p x = coord p y) : ¬ p ∣ (x - y).den := by
  haveI := Fact.mk hp
  by_cases hpL : p ∣ L
  case neg =>
    have hdL : ((x - y) * (L : ℚ)).den = 1 := by
      rw [sub_mul]; exact den_sub_eq_one hxL hyL
    exact fun h => hpL (h.trans (den_dvd_of_mul_natCast_den_eq_one hdL))
  case pos =>
    obtain ⟨L', rfl⟩ := hpL
    have hpL' : ¬ p ∣ L' := fun h => hppL (mul_dvd_mul_left p h)
    have hL'0 : L' ≠ 0 := by rintro rfl; exact hL0 (Nat.mul_zero p)
    have hbZ : ¬ (p : ℤ) ∣ (L' : ℤ) := fun h => hpL' (Int.natCast_dvd_natCast.mp h)
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
    -- any `z` with `z · (pL')` integral gives `(p·z)·L' = (z·(pL')).num`
    have key : ∀ z : ℚ, (z * ((p * L' : ℕ) : ℚ)).den = 1 →
        ((p : ℚ) * z) * ((L' : ℤ) : ℚ)
          = (((z * ((p * L' : ℕ) : ℚ)).num : ℤ) : ℚ) := by
      intro z hz
      have h1 : ((z * ((p * L' : ℕ) : ℚ)).num : ℚ) = z * ((p * L' : ℕ) : ℚ) :=
        (Rat.den_eq_one_iff _).mp hz
      push_cast at h1 ⊢
      linear_combination -h1
    have hd : ((x - y) * ((p * L' : ℕ) : ℚ)).den = 1 := by
      rw [sub_mul]; exact den_sub_eq_one hxL hyL
    have hdenx : ¬ p ∣ ((p : ℚ) * x).den :=
      not_dvd_den_of_mul_intCast_eq hp hbZ (key x hxL)
    have hdeny : ¬ p ∣ ((p : ℚ) * y).den :=
      not_dvd_den_of_mul_intCast_eq hp hbZ (key y hyL)
    have hdend : ¬ p ∣ ((p : ℚ) * (x - y)).den :=
      not_dvd_den_of_mul_intCast_eq hp hbZ (key _ hd)
    -- the difference's coordinate vanishes
    have hzero : ratToZMod p ((p : ℚ) * (x - y)) = 0 := by
      have hadd : ratToZMod p ((p : ℚ) * (x - y) + (p : ℚ) * y)
          = ratToZMod p ((p : ℚ) * (x - y)) + ratToZMod p ((p : ℚ) * y) :=
        ratToZMod_add hp hdend hdeny
      rw [show (p : ℚ) * (x - y) + (p : ℚ) * y = (p : ℚ) * x by ring] at hadd
      rw [coord_def, coord_def] at hcoord
      rw [hcoord] at hadd
      have hsub : ratToZMod p ((p : ℚ) * (x - y))
          = ratToZMod p ((p : ℚ) * y) - ratToZMod p ((p : ℚ) * y) := by
        rw [eq_sub_iff_add_eq]
        exact hadd.symm
      rw [sub_self] at hsub
      exact hsub
    -- hence `p` divides the integer `(x-y)·(pL')`
    have huniq := ratToZMod_unique hp hbZ (key _ hd)
    rw [hzero] at huniq
    have hL'ne : ((L' : ℤ) : ZMod p) ≠ 0 := fun h =>
      hbZ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
    have hc0 : ((((x - y) * ((p * L' : ℕ) : ℚ)).num : ℤ) : ZMod p) = 0 := by
      rcases mul_eq_zero.mp huniq.symm with h | h
      · exact h
      · exact absurd h (inv_ne_zero hL'ne)
    obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hc0
    -- cancel `p`: `(x-y)·L'` is the integer `c'`
    have h1d : (((x - y) * ((p * L' : ℕ) : ℚ)).num : ℚ)
        = (x - y) * ((p * L' : ℕ) : ℚ) := (Rat.den_eq_one_iff _).mp hd
    have hc'' : (x - y) * ((p * L' : ℕ) : ℚ) = (p : ℚ) * (c' : ℚ) := by
      rw [← h1d, hc']
      push_cast
      ring
    have hdL' : (x - y) * ((L' : ℕ) : ℚ) = ((c' : ℤ) : ℚ) := by
      apply mul_left_cancel₀ hp0
      push_cast at hc'' ⊢
      linear_combination hc''
    have hden' : ((x - y) * ((L' : ℕ) : ℚ)).den = 1 := by
      rw [hdL', Rat.den_intCast]
    exact fun h =>
      hpL' (h.trans (den_dvd_of_mul_natCast_den_eq_one hden'))

/-- **Fibre smoothness.** Two elements of `𝓔_N` with equal coordinates at
every large prime differ by a rational whose reduced denominator divides
`𝔇_Q(N)`: at primes `q ≤ Q` the exponent is at most
`ν_q(D_N(N)) = ⌊log N/log q⌋`, at primes `Q < q ≤ N` the equal coordinates
force exponent `0` (`not_dvd_den_sub_of_coord_eq`, using `ν_q(D_N(N)) ≤ 1`
from `q² > Q² > N`), and primes `q > N` never occur. -/
theorem den_sub_dvd_smoothPart {N Q : ℕ} (hQN : Q < N) (hQ2 : N < Q * Q)
    {x y : ℚ} (hx : x ∈ reciprocalSubsetSumSet N)
    (hy : y ∈ reciprocalSubsetSumSet N)
    (hcoord : ∀ p ∈ largePrimes Q N, coord p x = coord p y) :
    (x - y).den ∣ smoothPart Q N := by
  have hN0 : N ≠ 0 := by omega
  have hL0 : smoothPart N N ≠ 0 := smoothPart_ne_zero N N
  have hxL := mul_smoothPart_den_eq_one hx
  have hyL := mul_smoothPart_den_eq_one hy
  have hdL : ((x - y) * (smoothPart N N : ℚ)).den = 1 := by
    rw [sub_mul]; exact den_sub_eq_one hxL hyL
  have hdvdL : (x - y).den ∣ smoothPart N N :=
    den_dvd_of_mul_natCast_den_eq_one hdL
  rw [← Nat.factorization_le_iff_dvd (x - y).den_ne_zero (smoothPart_ne_zero Q N),
    Finsupp.le_def]
  intro q
  by_cases hq : q.Prime
  swap
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  by_cases hqQ : q ≤ Q
  · -- small primes: bounded by the exponent in the universal denominator
    have h1 : (x - y).den.factorization q ≤ (smoothPart N N).factorization q :=
      Finsupp.le_def.mp
        ((Nat.factorization_le_iff_dvd (x - y).den_ne_zero hL0).mpr hdvdL) q
    rw [factorization_smoothPart, if_pos ⟨hq, by omega⟩] at h1
    rw [factorization_smoothPart, if_pos ⟨hq, hqQ⟩]
    exact h1
  · -- large primes: exponent zero
    have hzero : (x - y).den.factorization q = 0 := by
      by_cases hqN : q ≤ N
      · -- `Q < q ≤ N`: the coordinate argument
        have hqmem : q ∈ largePrimes Q N := mem_largePrimes.mpr ⟨by omega, hqN, hq⟩
        have hlog : Nat.log q N < 2 :=
          Nat.log_lt_of_lt_pow hN0 (by
            rw [pow_two]
            exact lt_of_lt_of_le hQ2 (Nat.mul_le_mul (by omega) (by omega)))
        have hppL : ¬ q * q ∣ smoothPart N N := by
          intro hdvd
          have h2le : 2 ≤ (smoothPart N N).factorization q :=
            (hq.pow_dvd_iff_le_factorization hL0).mp (by rw [pow_two]; exact hdvd)
          rw [factorization_smoothPart, if_pos ⟨hq, hqN⟩] at h2le
          omega
        exact Nat.factorization_eq_zero_of_not_dvd
          (not_dvd_den_sub_of_coord_eq hq hL0 hppL hxL hyL (hcoord q hqmem))
      · -- `q > N`: cannot divide the universal denominator at all
        have hnd : ¬ q ∣ smoothPart N N := by
          intro hdvd
          have hpos := hq.factorization_pos_of_dvd hL0 hdvd
          rw [factorization_smoothPart, if_neg fun h => hqN h.2] at hpos
          omega
        exact Nat.factorization_eq_zero_of_not_dvd fun h => hnd (h.trans hdvdL)
    rw [hzero]
    exact Nat.zero_le _

/-- **Fibre count.** Any set of elements of `𝓔_N` with pairwise equal
large-prime coordinates has at most `⌊H_N · 𝔇_Q(N)⌋ + 1` members: measured
from its least element, its members are distinct integer multiples of
`1/𝔇_Q(N)` inside `[0, H_N]`. -/
theorem fibre_card_le {N Q : ℕ} (hQN : Q < N) (hQ2 : N < Q * Q)
    {T : Finset ℚ} (hT : T ⊆ reciprocalSubsetSumSet N)
    (hcoords : ∀ x ∈ T, ∀ y ∈ T, ∀ p ∈ largePrimes Q N, coord p x = coord p y) :
    T.card ≤ ⌊harmonicSum N * (smoothPart Q N : ℚ)⌋₊ + 1 := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  set x₀ := T.min' hne with hx₀def
  have hx₀ : x₀ ∈ T := T.min'_mem hne
  have hD0 : (smoothPart Q N : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (smoothPart_ne_zero Q N)
  have hDnn : (0 : ℚ) ≤ (smoothPart Q N : ℚ) := Nat.cast_nonneg _
  have key : ∀ x ∈ T, ((x - x₀) * (smoothPart Q N : ℚ)).den = 1 ∧
      (0 : ℚ) ≤ (x - x₀) * (smoothPart Q N : ℚ) ∧
      (x - x₀) * (smoothPart Q N : ℚ)
        ≤ harmonicSum N * (smoothPart Q N : ℚ) := by
    intro x hx
    have hdvd : (x - x₀).den ∣ smoothPart Q N :=
      den_sub_dvd_smoothPart hQN hQ2 (hT hx) (hT hx₀)
        fun p hp => hcoords x hx x₀ hx₀ p hp
    have hnn : (0 : ℚ) ≤ x - x₀ := sub_nonneg.mpr (T.min'_le x hx)
    have hle : x - x₀ ≤ harmonicSum N := by
      have hb := mem_reciprocalSubsetSumSet_bounds (hT hx)
      have hb0 := mem_reciprocalSubsetSumSet_bounds (hT hx₀)
      linarith [hb.2, hb0.1]
    exact ⟨mul_natCast_den_eq_one_of_den_dvd hdvd, mul_nonneg hnn hDnn,
      mul_le_mul_of_nonneg_right hle hDnn⟩
  have hmap : ∀ x ∈ T, ((x - x₀) * (smoothPart Q N : ℚ)).num.toNat
      ∈ Finset.range (⌊harmonicSum N * (smoothPart Q N : ℚ)⌋₊ + 1) := by
    intro x hx
    obtain ⟨hden, hnn, hle⟩ := key x hx
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.le_floor
    have hnum : (((x - x₀) * (smoothPart Q N : ℚ)).num : ℚ)
        = (x - x₀) * (smoothPart Q N : ℚ) := (Rat.den_eq_one_iff _).mp hden
    have hnn' : 0 ≤ ((x - x₀) * (smoothPart Q N : ℚ)).num :=
      Rat.num_nonneg.mpr hnn
    have hcast : ((((x - x₀) * (smoothPart Q N : ℚ)).num.toNat : ℕ) : ℚ)
        = (((x - x₀) * (smoothPart Q N : ℚ)).num : ℚ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (Int.toNat_of_nonneg hnn')
    rw [hcast, hnum]
    exact hle
  have hinj : Set.InjOn
      (fun x => ((x - x₀) * (smoothPart Q N : ℚ)).num.toNat) T := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    obtain ⟨hdx, hnx, -⟩ := key x hx
    obtain ⟨hdy, hny, -⟩ := key y hy
    have hnx' : 0 ≤ ((x - x₀) * (smoothPart Q N : ℚ)).num :=
      Rat.num_nonneg.mpr hnx
    have hny' : 0 ≤ ((y - x₀) * (smoothPart Q N : ℚ)).num :=
      Rat.num_nonneg.mpr hny
    have hnum_eq : ((x - x₀) * (smoothPart Q N : ℚ)).num
        = ((y - x₀) * (smoothPart Q N : ℚ)).num := by
      rw [← Int.toNat_of_nonneg hnx', ← Int.toNat_of_nonneg hny']
      exact_mod_cast hxy
    have hq_eq : (x - x₀) * (smoothPart Q N : ℚ)
        = (y - x₀) * (smoothPart Q N : ℚ) := by
      rw [← (Rat.den_eq_one_iff _).mp hdx, ← (Rat.den_eq_one_iff _).mp hdy,
        hnum_eq]
    exact sub_left_inj.mp (mul_right_cancel₀ hD0 hq_eq)
  simpa using Finset.card_le_card_of_injOn _ hmap hinj

/-- **Upper half of eq. `exact-large-prime-decomposition`:**
`S(N) ≤ (⌊H_N · 𝔇_Q(N)⌋ + 1) · ∏_{Q < p ≤ N} σ_p(⌊N/p⌋)`.  Partition `𝓔_N`
by the vector of large-prime coordinates: there are at most
`∏ σ_p(⌊N/p⌋)` possible vectors (`coord_mem_modularImage`), and each fibre
has at most `⌊H_N · 𝔇_Q(N)⌋ + 1` elements (`fibre_card_le`). -/
theorem S_le_fibre_mul_prod_sigma {N Q : ℕ} (hQN : Q < N) (hQ2 : N < Q * Q) :
    S N ≤ (⌊harmonicSum N * (smoothPart Q N : ℚ)⌋₊ + 1)
      * ∏ p ∈ largePrimes Q N, sigma p (N / p) := by
  classical
  have hcard : ((largePrimes Q N).pi fun p => modularImage p (N / p)).card
      = ∏ p ∈ largePrimes Q N, sigma p (N / p) := Finset.card_pi _ _
  have hmaps : ∀ x ∈ reciprocalSubsetSumSet N,
      (fun p (_ : p ∈ largePrimes Q N) => coord p x)
        ∈ (largePrimes Q N).pi fun p => modularImage p (N / p) := by
    intro x hx
    rw [Finset.mem_pi]
    intro p hp
    obtain ⟨hQp, hpN, hprime⟩ := mem_largePrimes.mp hp
    exact coord_mem_modularImage hprime
      (lt_of_lt_of_le hQ2 (Nat.mul_le_mul hQp.le hQp.le)) hx
  have hfibre : ∀ f ∈ (largePrimes Q N).pi fun p => modularImage p (N / p),
      ((reciprocalSubsetSumSet N).filter
        (fun x => (fun p (_ : p ∈ largePrimes Q N) => coord p x) = f)).card
        ≤ ⌊harmonicSum N * (smoothPart Q N : ℚ)⌋₊ + 1 := by
    intro f _
    refine fibre_card_le hQN hQ2 (Finset.filter_subset _ _) ?_
    intro x hx y hy p hp
    have hxf := (Finset.mem_filter.mp hx).2
    have hyf := (Finset.mem_filter.mp hy).2
    exact congrFun (congrFun (hxf.trans hyf.symm) p) hp
  calc S N
      = ∑ f ∈ (largePrimes Q N).pi fun p => modularImage p (N / p),
          ((reciprocalSubsetSumSet N).filter
            (fun x => (fun p (_ : p ∈ largePrimes Q N) => coord p x) = f)).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _f ∈ (largePrimes Q N).pi fun p => modularImage p (N / p),
          (⌊harmonicSum N * (smoothPart Q N : ℚ)⌋₊ + 1) :=
        Finset.sum_le_sum hfibre
    _ = ((largePrimes Q N).pi fun p => modularImage p (N / p)).card
          * (⌊harmonicSum N * (smoothPart Q N : ℚ)⌋₊ + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (⌊harmonicSum N * (smoothPart Q N : ℚ)⌋₊ + 1)
          * ∏ p ∈ largePrimes Q N, sigma p (N / p) := by
        rw [hcard, Nat.mul_comm]

end Erdos320
