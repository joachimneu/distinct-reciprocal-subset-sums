import Erdos320.Lemmas.AverageCollision
import Erdos320.Lemmas.LargePrimeDecomposition
import Erdos320.Lemmas.SBasic
import Erdos320.Lemmas.ShellCounts
import Erdos320.Lemmas.ShellDecomposition
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.BigOperators.Associated

/-!
# Shellwise collision lower bound (eq. `collision-sum` in `prop:averaging-relation`)

The manuscript applies the average collision bound (`lem:average-collision`)
to the set `T_m = 𝓔_m` of the `S(m)` distinct rational subset sums formed from
`1, 1/2, …, 1/m`.  This file provides the bookkeeping that makes the lemma
applicable and the resulting bound, eq. `collision-sum`:

```
(1/P_m) ∑_{p in shell m} log σ_p(m) ≥ g(m) − log(1 + b_m(e^{g(m)} − 1)/P_m).
```

* **lcm denominator bookkeeping** (paper: "If `L_m = lcm(1,…,m)`, then
  `L(T_m) ∣ L_m`" and "`W(T_m) = L(T_m)·H_m ≤ L_m·H_m`"):
  `lcm_Icc_pos`, `mul_lcm_Icc_den_eq_one`, `den_dvd_lcm_Icc`,
  `lcm_Icc_scaled_num_nonneg`, `lcm_Icc_scaled_num_le`.
* **Shell primes avoid the lcm** (paper: "Every shell prime exceeds `m` and
  hence divides neither `L_m` nor `L(T_m)`"): `not_dvd_lcm_Icc_of_lt`.
* **Chebyshev-type bound for the lcm** (paper: "the elementary Chebyshev
  estimate" `log L_m = Σ_{p^k≤m} log p ≪ m`, which "controls the numerator
  span"):
  `log_lcm_Icc_le` gives `log L_m ≤ ϑ(m) + √m·log m` —
  `lem:prime-power-splitting` specialized to `Q = N = m`
  (`L_m = 𝔇_m(m)`), realized here by specializing `log_smoothPart_le` — and
  `log_lcm_mul_harmonicSum_le` combines it with `ϑ(m) ≤ (log 4)·m` and a
  supplied harmonic bound `H_m ≤ 1 + log m` into an explicit bound on
  `log(L_m·H_m)` (cf. eq. `explicit-bm` in `lem:explicit-low-averaging`).
* **Main result** `shell_collision_lower` — eq. `collision-sum`, stated over
  an abstract finite set `P` of primes exceeding both `m` and `N/(m+1)`
  (the consumer instantiates `P` with the `m`-th prime shell), multiplied
  through by `P_m = |P|` and with `e^{g(m)} = S(m)`:
  `|P|·(g(m) − log(1 + b(S(m)−1)/|P|)) ≤ ∑_{p ∈ P} log σ_p(m)` for any
  integer `b ≥ log(L_m·H_m)/log(N/(m+1))` (the paper's `b_m`).
-/

namespace Erdos320

open Finset

/-! ## lcm denominator bookkeeping

The paper's `L_m = lcm(1,…,m)` is `(Finset.Icc 1 m).lcm id`.  Multiplying any
element of `𝓔_m` by `L_m` clears its denominator, and the resulting integer
numerators span `[0, L_m·H_m]` — the paper's numerator span `W(T_m) ≤ L_m·H_m`
in the proof of `prop:averaging-relation` (and of
`lem:explicit-low-averaging`, "The integer numerator span of `𝓔_m` is at most
`L_m·H_m`").
-/

/-- `L_m = lcm(1,…,m)` divides the universal smooth denominator
`D_m(m) = ∏_{q ≤ m} q^{⌊log m/log q⌋}` of `prop:large-prime-decomposition`
(each `n ≤ m` divides `D_m(m)`, hence so does their lcm). -/
theorem lcm_Icc_dvd_smoothPart (m : ℕ) :
    (Finset.Icc 1 m).lcm id ∣ smoothPart m m :=
  Finset.lcm_dvd fun _n hn =>
    dvd_smoothPart_of_le (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2

/-- `L_m = lcm(1,…,m) > 0` (all members of `{1,…,m}` are positive). -/
theorem lcm_Icc_pos (m : ℕ) : 0 < (Finset.Icc 1 m).lcm id := by
  rcases Nat.eq_zero_or_pos ((Finset.Icc 1 m).lcm id) with h0 | h
  · exfalso
    have h := lcm_Icc_dvd_smoothPart m
    rw [h0] at h
    exact smoothPart_ne_zero m m (zero_dvd_iff.mp h)
  · exact h

/-- Multiplying a reciprocal subset sum `x ∈ 𝓔_m` by `L_m = lcm(1,…,m)`
yields an integer: this is the paper's "`L(T_m) ∣ L_m`" step in the proof of
eq. `collision-sum` (the least common denominator of `T_m = 𝓔_m` divides
`L_m`), stated in the form the scaling bridge of `lem:average-collision`
consumes. -/
theorem mul_lcm_Icc_den_eq_one {m : ℕ} {x : ℚ}
    (hx : x ∈ reciprocalSubsetSumSet m) :
    ((((Finset.Icc 1 m).lcm id : ℕ) : ℚ) * x).den = 1 := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
  have hA' : A ⊆ Finset.Icc 1 m := Finset.mem_powerset.mp hA
  have hsum : (((Finset.Icc 1 m).lcm id : ℕ) : ℚ) * (∑ n ∈ A, (1 : ℚ) / n)
      = ((∑ n ∈ A, (Finset.Icc 1 m).lcm id / n : ℕ) : ℚ) := by
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hmem := Finset.mem_Icc.mp (hA' hn)
    have hdvd : n ∣ (Finset.Icc 1 m).lcm id := Finset.dvd_lcm (hA' hn)
    have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.cast_div hdvd hn0, mul_one_div]
  rw [hsum,
    show ((∑ n ∈ A, (Finset.Icc 1 m).lcm id / n : ℕ) : ℚ)
      = (((∑ n ∈ A, (Finset.Icc 1 m).lcm id / n : ℕ) : ℤ) : ℚ) from
      (Int.cast_natCast _).symm,
    Rat.den_intCast]

/-- The reduced denominator of every `x ∈ 𝓔_m` divides `L_m = lcm(1,…,m)`
(the paper's "`L(T_m) ∣ L_m`" for eq. `collision-sum`). -/
theorem den_dvd_lcm_Icc {m : ℕ} {x : ℚ} (hx : x ∈ reciprocalSubsetSumSet m) :
    x.den ∣ (Finset.Icc 1 m).lcm id :=
  den_dvd_of_mul_natCast_den_eq_one
    (by rw [mul_comm]; exact mul_lcm_Icc_den_eq_one hx)

/-- Lower end of the integer numerator span of `L_m·𝓔_m`: the scaled
numerators are nonnegative (paper: "Since `0, H_m ∈ T_m`, `W(T_m) =
L(T_m)·H_m ≤ L_m·H_m`" — the span starts at `0`). -/
theorem lcm_Icc_scaled_num_nonneg {m : ℕ} {x : ℚ}
    (hx : x ∈ reciprocalSubsetSumSet m) :
    0 ≤ ((((Finset.Icc 1 m).lcm id : ℕ) : ℚ) * x).num :=
  Rat.num_nonneg.mpr
    (mul_nonneg (Nat.cast_nonneg _) (mem_reciprocalSubsetSumSet_bounds hx).1)

/-- Upper end of the integer numerator span of `L_m·𝓔_m`: each scaled
numerator is at most `L_m·H_m` (the paper's numerator span `W(T_m) ≤ L_m·H_m`
for eq. `collision-sum`). -/
theorem lcm_Icc_scaled_num_le {m : ℕ} {x : ℚ}
    (hx : x ∈ reciprocalSubsetSumSet m) :
    (((((Finset.Icc 1 m).lcm id : ℕ) : ℚ) * x).num : ℚ)
      ≤ (((Finset.Icc 1 m).lcm id : ℕ) : ℚ) * harmonicSum m := by
  rw [(Rat.den_eq_one_iff _).mp (mul_lcm_Icc_den_eq_one hx)]
  exact mul_le_mul_of_nonneg_left (mem_reciprocalSubsetSumSet_bounds hx).2
    (Nat.cast_nonneg _)

/-- A prime `p > m` does not divide `L_m = lcm(1,…,m)` (paper: "Every shell
prime exceeds `m` and hence divides neither `L_m` nor `L(T_m)`", proof of
eq. `collision-sum`): if it did, it would divide some `n ∈ {1,…,m}`, forcing
`p ≤ m`. -/
theorem not_dvd_lcm_Icc_of_lt {p m : ℕ} (hp : Nat.Prime p) (hmp : m < p) :
    ¬ p ∣ (Finset.Icc 1 m).lcm id := by
  intro hdvd
  have hprod : (Finset.Icc 1 m).lcm id ∣ ∏ n ∈ Finset.Icc 1 m, n :=
    Finset.lcm_dvd fun n hn => Finset.dvd_prod_of_mem (fun k => k) hn
  obtain ⟨n, hn, hpn⟩ :=
    (hp.prime.dvd_finsetProd_iff _).mp (hdvd.trans hprod)
  have h1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have h2 : n ≤ m := (Finset.mem_Icc.mp hn).2
  have := Nat.le_of_dvd (by omega) hpn
  omega

/-! ## Chebyshev-type bound for the lcm

The paper controls the numerator span through "the elementary Chebyshev
estimate" `log L_m = Σ_{p^k≤m} log p ≪ m` (i.e. `log L_m = ψ(m)`).  We
realize `ψ(m)` through the smooth
denominator `D_m(m)` of `prop:large-prime-decomposition` (which has the same
prime factorization `∏_{q ≤ m} q^{⌊log m/log q⌋}` as `lcm(1,…,m)` — we only
need the divisibility `L_m ∣ D_m(m)`), splitting off the first prime-power
layer `ϑ(m)` and bounding the higher layers by `√m · log m`.
-/

/-- `log L_m ≤ ϑ(m) + √m·log m` — the paper's `log L_m = Σ_{p^k≤m} log p ≪ m`
bound (proof
of eq. `collision-sum`) in explicit form: the first prime-power layer of
`ψ(m)` is `ϑ(m)`, and the higher layers are supported on the at most `√m`
primes `q ≤ √m`, each contributing at most `log m`.

The prime-power-layer split is proved once, generally, in
`ShellDecomposition.log_smoothPart_le` (`log D_Q(N) ≤ ϑ(Q) + √N·log N`); here
we specialize it to the diagonal `Q = N = m` and transport it back to
`L_m = lcm(1,…,m)` through the divisibility `L_m ∣ D_m(m)`
(`lcm_Icc_dvd_smoothPart`). -/
theorem log_lcm_Icc_le (m : ℕ) :
    Real.log (((Finset.Icc 1 m).lcm id : ℕ) : ℝ)
      ≤ chebyshevTheta m + Real.sqrt m * Real.log m := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · -- `m ∈ {0, 1}`: `L_m = 1`, so the left side is `log 1 = 0 ≤` a nonnegative
    -- right side (`ϑ` is a sum of `log p ≥ 0`, and `√m·log m = 0` here).
    have hlcm : (Finset.Icc 1 m).lcm id = 1 := by interval_cases m <;> decide
    rw [hlcm, Nat.cast_one, Real.log_one]
    have hθ : (0 : ℝ) ≤ chebyshevTheta m :=
      Finset.sum_nonneg fun p hp =>
        Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
    have hsq : (0 : ℝ) ≤ Real.sqrt m * Real.log m := by
      interval_cases m <;> simp
    linarith
  · -- `m ≥ 2`: transport `log_smoothPart_le` (at `Q = N = m`) back along
    -- `L_m ∣ D_m(m)`.
    have hsp_pos : 0 < smoothPart m m := Nat.pos_of_ne_zero (smoothPart_ne_zero m m)
    have hlog1 : Real.log (((Finset.Icc 1 m).lcm id : ℕ) : ℝ)
        ≤ Real.log ((smoothPart m m : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast lcm_Icc_pos m)
        (by exact_mod_cast Nat.le_of_dvd hsp_pos (lcm_Icc_dvd_smoothPart m))
    exact hlog1.trans (log_smoothPart_le hm le_rfl)

/-! ## The main bound -/

/-- **Shellwise collision lower bound** — eq. `collision-sum` in the proof of
`prop:averaging-relation`, multiplied through by `P_m = |P|` and with
`e^{g(m)} = S(m)`:

```
|P| · (g(m) − log(1 + b(S(m)−1)/|P|)) ≤ ∑_{p ∈ P} log σ_p(m).
```

`P` is an abstract nonempty finite set of primes exceeding both `m` and
`N/(m+1)` — the consumer instantiates it with the `m`-th prime shell
`{p prime : N/(m+1) < p ≤ N/m}` (whose members do satisfy both, the first
because `N/(m+1) ≥ m` there).  The hypothesis `hb` admits any integer `b`
dominating the paper's collision multiplicity
`b_m = ⌊log(L_m·H_m) / log(N/(m+1))⌋`: a nonzero difference of two scaled
numerators of `𝓔_m` has absolute value at most `W(T_m) ≤ L_m·H_m`
(`lcm_Icc_scaled_num_nonneg` / `lcm_Icc_scaled_num_le`), while every prime of
`P` exceeds `N/(m+1)`, so at most `b` of them divide it
(`card_filter_dvd_le_of_abs_le`).  The scaling `𝓔_m → L_m·𝓔_m ⊆ ℤ` does not
change the number of residues modulo `p ∈ P` because `p ∤ L_m`
(`not_dvd_lcm_Icc_of_lt`, `card_image_intCast_scaled_eq_card_image_ratToZMod`),
and the residues of `𝓔_m` are exactly `Σ_p(m)`
(`ratToZMod_image_reciprocalSubsetSumSet`, using `m < p`). -/
theorem shell_collision_lower {N m : ℕ}
    (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hlarge : ∀ p ∈ P, m < p)
    (hshell : ∀ p ∈ P, (N : ℝ) / ((m : ℝ) + 1) < (p : ℝ))
    (hbig : (1 : ℝ) < (N : ℝ) / ((m : ℝ) + 1)) (b : ℕ)
    (hb : Real.log ((((Finset.Icc 1 m).lcm id : ℕ) : ℝ)
            * ((harmonicSum m : ℚ) : ℝ))
          / Real.log ((N : ℝ) / ((m : ℝ) + 1)) ≤ (b : ℝ)) :
    (P.card : ℝ)
        * (g m - Real.log (1 + (b : ℝ) * ((S m : ℝ) - 1) / (P.card : ℝ)))
      ≤ ∑ p ∈ P, Real.log ((sigma p m : ℝ)) := by
  set L : ℕ := (Finset.Icc 1 m).lcm id with hLdef
  set T : Finset ℤ :=
    (reciprocalSubsetSumSet m).image (fun x : ℚ => (((L : ℕ) : ℚ) * x).num)
    with hTdef
  have hL0 : ((L : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (lcm_Icc_pos m).ne'
  -- `L·𝓔_m ⊆ ℤ`: the paper's `L(T_m) ∣ L_m` step
  have hden1 : ∀ x ∈ reciprocalSubsetSumSet m, (((L : ℕ) : ℚ) * x).den = 1 :=
    fun _x hx => mul_lcm_Icc_den_eq_one hx
  -- scaling is injective on `𝓔_m`, so `|T| = S(m)`
  have hinj : Set.InjOn (fun x : ℚ => (((L : ℕ) : ℚ) * x).num)
      (reciprocalSubsetSumSet m) := by
    intro x hx y hy hxy
    have hxy' : (((L : ℕ) : ℚ) * x).num = (((L : ℕ) : ℚ) * y).num := hxy
    have hx1 : (((((L : ℕ) : ℚ) * x).num : ℤ) : ℚ) = ((L : ℕ) : ℚ) * x :=
      (Rat.den_eq_one_iff _).mp (hden1 x (Finset.mem_coe.mp hx))
    have hy1 : (((((L : ℕ) : ℚ) * y).num : ℤ) : ℚ) = ((L : ℕ) : ℚ) * y :=
      (Rat.den_eq_one_iff _).mp (hden1 y (Finset.mem_coe.mp hy))
    have hq : ((L : ℕ) : ℚ) * x = ((L : ℕ) : ℚ) * y := by
      rw [← hx1, ← hy1, hxy']
    exact mul_left_cancel₀ hL0 hq
  have hTcard : T.card = S m := Finset.card_image_of_injOn hinj
  have hTne : T.Nonempty := (reciprocalSubsetSumSet_nonempty m).image _
  -- collision multiplicity: at most `b` primes of `P` divide a nonzero
  -- difference of two elements of `T` (paper: `b_m ≤ log(L_m H_m)/log(N/(m+1))`)
  have hbcount : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      (P.filter fun p : ℕ => (p : ℤ) ∣ (x - y)).card ≤ b := by
    intro x hx y hy hxy
    rw [hTdef] at hx hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have hz : (((L : ℕ) : ℚ) * u).num - (((L : ℕ) : ℚ) * v).num ≠ 0 :=
      sub_ne_zero.mpr hxy
    have hu0 : (0 : ℝ) ≤ ((((L : ℕ) : ℚ) * u).num : ℝ) := by
      exact_mod_cast lcm_Icc_scaled_num_nonneg hu
    have hv0 : (0 : ℝ) ≤ ((((L : ℕ) : ℚ) * v).num : ℝ) := by
      exact_mod_cast lcm_Icc_scaled_num_nonneg hv
    have huW : ((((L : ℕ) : ℚ) * u).num : ℝ)
        ≤ ((L : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr (lcm_Icc_scaled_num_le hu)
      push_cast at h
      exact h
    have hvW : ((((L : ℕ) : ℚ) * v).num : ℝ)
        ≤ ((L : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr (lcm_Icc_scaled_num_le hv)
      push_cast at h
      exact h
    have habs : |(((((L : ℕ) : ℚ) * u).num - (((L : ℕ) : ℚ) * v).num : ℤ) : ℝ)|
        ≤ ((L : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ) := by
      rw [abs_le]
      push_cast
      constructor <;> linarith
    have hcnt := card_filter_dvd_le_of_abs_le _ hz _ habs
      ((N : ℝ) / ((m : ℝ) + 1)) hbig P hprime hshell
    have hle : (((P.filter fun p : ℕ =>
        (p : ℤ) ∣ ((((L : ℕ) : ℚ) * u).num - (((L : ℕ) : ℚ) * v).num)).card : ℕ) : ℝ)
        ≤ (b : ℝ) := hcnt.trans hb
    exact_mod_cast hle
  have hmain := average_collision_bound T hTne P hP b hbcount
  rw [hTcard] at hmain
  -- residues of the scaled set are exactly the modular images `Σ_p(m)`
  have himg : ∀ p ∈ P, (T.image fun x : ℤ => (x : ZMod p)).card = sigma p m := by
    intro p hp
    have hpp := hprime p hp
    have hLp : ¬ p ∣ L := not_dvd_lcm_Icc_of_lt hpp (hlarge p hp)
    have h1 := card_image_intCast_scaled_eq_card_image_ratToZMod hpp hLp
      (reciprocalSubsetSumSet m) hden1
    rw [ratToZMod_image_reciprocalSubsetSumSet hpp (hlarge p hp)] at h1
    rw [hTdef]
    exact h1
  show (P.card : ℝ)
      * (Real.log ((S m : ℕ) : ℝ)
        - Real.log (1 + (b : ℝ) * (((S m : ℕ) : ℝ) - 1) / (P.card : ℝ)))
    ≤ ∑ p ∈ P, Real.log ((sigma p m : ℝ))
  refine hmain.trans (le_of_eq (Finset.sum_congr rfl fun p hp => ?_))
  rw [himg p hp]

/-- Explicit numerator-span bound `log(L_m·H_m) ≤ (log 4)·m + √m·log m +
log(1 + log m)`, the fully explicit form of the paper's Chebyshev estimate
`log L_m = Σ_{p^k≤m} log p ≪ m` "which, together with `H_m ≤ 1 + log m`,
controls the numerator span" (proof of
eq. `collision-sum`; cf. eq. `explicit-bm` in `lem:explicit-low-averaging`).
The harmonic bound `H_m ≤ 1 + log m` is taken as a hypothesis (it is proved
elsewhere in the development); the lcm part is `log_lcm_Icc_le` combined with
the primorial Chebyshev bound `ϑ(m) ≤ (log 4)·m`. -/
theorem log_lcm_mul_harmonicSum_le {m : ℕ} (hm : 1 ≤ m)
    (hH : ((harmonicSum m : ℚ) : ℝ) ≤ 1 + Real.log m) :
    Real.log ((((Finset.Icc 1 m).lcm id : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ))
      ≤ Real.log 4 * m + Real.sqrt m * Real.log m
        + Real.log (1 + Real.log m) := by
  have hLpos : (0 : ℝ) < (((Finset.Icc 1 m).lcm id : ℕ) : ℝ) := by
    exact_mod_cast lcm_Icc_pos m
  have hH1 : (1 : ℚ) ≤ harmonicSum m := by
    have h1 : harmonicSum 1 = 1 := by
      rw [harmonicSum_eq_sum_Icc, Finset.Icc_self, Finset.sum_singleton]
      norm_num
    calc (1 : ℚ) = harmonicSum 1 := h1.symm
      _ ≤ harmonicSum m := harmonicSum_strictMono.monotone hm
  have hHpos : (0 : ℝ) < ((harmonicSum m : ℚ) : ℝ) := by
    have h : (1 : ℝ) ≤ ((harmonicSum m : ℚ) : ℝ) := by exact_mod_cast hH1
    linarith
  rw [Real.log_mul hLpos.ne' hHpos.ne']
  have h1 := log_lcm_Icc_le m
  have h2 : chebyshevTheta m ≤ Real.log 4 * m :=
    chebyshevTheta_le_log_four_mul (Nat.cast_nonneg m)
  have h3 : Real.log ((harmonicSum m : ℚ) : ℝ) ≤ Real.log (1 + Real.log m) :=
    Real.log_le_log hHpos hH
  linarith

end Erdos320
