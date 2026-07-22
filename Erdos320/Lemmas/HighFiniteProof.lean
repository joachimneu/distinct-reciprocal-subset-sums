import Erdos320.Lemmas.CollisionLower
import Erdos320.Lemmas.ShellDecomposition
import Erdos320.Defs.LogCount

/-!
# Mechanizing the high finite input `highFiniteInput : 3.2411 < F ⌊e⁶⁵⌋`

This file reproduces, from already-proved Lean lemmas and the sanctioned
BGMS/Dusart axioms, the `high_bridge_lower` computation of the manuscript's
directed-interval certificate, whose conclusion is
```
F(N₁) = (log N₁ / N₁)·log S(N₁) > 3.2411,   N₁ = ⌊e⁶⁵⌋
     = 16948892444103337141417836114.
```
(The Python certificate's exact rational total is `3.241195652…`, slack
`≈ 9.6·10⁻⁵` above `3.2411`.)

## The collision-multiplicity subtlety

The certificate's collision multiplicity for shell `m` is
`b_cert = ⌊log W_m / log r_m⌋` (`divisor_bound`), where `W_m = L_m·H_m` is the
integer numerator span and `r_m = N₁/(m+1)`.  This is the *exact* maximal number
of shell primes dividing a nonzero numerator difference: `card ≤ log W/log r`
and `card ∈ ℕ`, so `card ≤ ⌊log W/log r⌋`.

By contrast, `shell_collision_lower` (`CollisionLower.lean`) requires
`hb : log W/log r ≤ b` — a *sufficient* but stronger condition, forcing
`b = ⌈log W/log r⌉ = b_cert + 1` on every shell where `log W/log r ∉ ℤ` (i.e.
essentially all of them).  Numerically that inflated multiplicity drops the
bridge total from `3.24120` to `3.23730 < 3.2411` — it destroys the certificate.

So the mechanization uses the *tight* integer bound:
`shell_collision_lower_tight` below takes the pure integer hypothesis
`W_m < r_m^{b+1}`
(equivalently `W_m·(m+1)^{b+1} < N₁^{b+1}`, a `decide`-able `ℕ` inequality) and
derives `card ≤ b` from `card ≤ log W/log r < b+1`, keeping `b = b_cert`.
-/

namespace Erdos320

open Finset

/-! ## The tight shellwise collision lower bound

This is `shell_collision_lower` with the real-valued admissibility hypothesis
`hb` replaced by the tight integer-power hypothesis `hWlt : W < r^{b+1}`.  The
proof body is identical except for the final step of the collision-count bound,
where `card ≤ log W/log r` (from `card_filter_dvd_le_of_abs_le`) is combined with
`log W < (b+1)·log r` (from `hWlt`) to give the *integer* `card ≤ b` — rather
than the coarser `card ≤ b` obtained from `log W/log r ≤ b`. -/
theorem shell_collision_lower_tight {N m : ℕ}
    (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hlarge : ∀ p ∈ P, m < p)
    (hshell : ∀ p ∈ P, (N : ℝ) / ((m : ℝ) + 1) < (p : ℝ))
    (hbig : (1 : ℝ) < (N : ℝ) / ((m : ℝ) + 1)) (b : ℕ)
    (hWlt : (((Finset.Icc 1 m).lcm id : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ)
            < ((N : ℝ) / ((m : ℝ) + 1)) ^ (b + 1)) :
    (P.card : ℝ)
        * (g m - Real.log (1 + (b : ℝ) * ((S m : ℝ) - 1) / (P.card : ℝ)))
      ≤ ∑ p ∈ P, Real.log ((sigma p m : ℝ)) := by
  set L : ℕ := (Finset.Icc 1 m).lcm id with hLdef
  set T : Finset ℤ :=
    (reciprocalSubsetSumSet m).image (fun x : ℚ => (((L : ℕ) : ℚ) * x).num)
    with hTdef
  have hL0 : ((L : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (lcm_Icc_pos m).ne'
  have hden1 : ∀ x ∈ reciprocalSubsetSumSet m, (((L : ℕ) : ℚ) * x).den = 1 :=
    fun _x hx => mul_lcm_Icc_den_eq_one hx
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
  -- the tight collision-multiplicity bound
  have hlogr_pos : 0 < Real.log ((N : ℝ) / ((m : ℝ) + 1)) := Real.log_pos hbig
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
    -- the numerator difference is a nonzero integer, so `1 ≤ |·| ≤ W`, giving `W > 0`
    have hone : (1 : ℝ) ≤ |(((((L : ℕ) : ℚ) * u).num
        - (((L : ℕ) : ℚ) * v).num : ℤ) : ℝ)| := by
      have := Int.one_le_abs hz
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|(((L : ℕ) : ℚ) * u).num - (((L : ℕ) : ℚ) * v).num| : ℤ) : ℝ) := by
            exact_mod_cast this
        _ = |(((((L : ℕ) : ℚ) * u).num - (((L : ℕ) : ℚ) * v).num : ℤ) : ℝ)| := by
            rw [Int.cast_abs]
    have hWpos : 0 < ((L : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ) := by
      linarith [hone.trans habs]
    have hcnt := card_filter_dvd_le_of_abs_le _ hz _ habs
      ((N : ℝ) / ((m : ℝ) + 1)) hbig P hprime hshell
    -- `log W < (b+1)·log r`, hence `log W / log r < b+1`, hence `card < b+1`
    have hloglt : Real.log (((L : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ))
        < ((b : ℝ) + 1) * Real.log ((N : ℝ) / ((m : ℝ) + 1)) := by
      have h := Real.log_lt_log hWpos hWlt
      rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
    have hlt : Real.log (((L : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ))
        / Real.log ((N : ℝ) / ((m : ℝ) + 1)) < (b : ℝ) + 1 := by
      rw [div_lt_iff₀ hlogr_pos]; linarith
    have hcardlt : (((P.filter fun p : ℕ =>
        (p : ℤ) ∣ ((((L : ℕ) : ℚ) * u).num - (((L : ℕ) : ℚ) * v).num)).card : ℕ) : ℝ)
        < (b : ℝ) + 1 := lt_of_le_of_lt hcnt hlt
    have : (P.filter fun p : ℕ =>
        (p : ℤ) ∣ ((((L : ℕ) : ℚ) * u).num - (((L : ℕ) : ℚ) * v).num)).card < b + 1 := by
      exact_mod_cast hcardlt
    omega
  have hmain := average_collision_bound T hTne P hP b hbcount
  rw [hTcard] at hmain
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

/-! ## Per-shell contribution lower bounds

`shell_collision_lower_tight` gives `P.card·(g m − log(1 + b(S m−1)/P.card)) ≤
∑_{p} log σ`.  To turn this into a *rational* lower bound `κ_m` we replace the
true `P.card`, `S m` by rational lower bounds `Pm ≤ P.card`, `sL ≤ S m` and the
log-penalty by a rational upper bound `pen`.  This is valid because the map
`f(s,P) = P·(log s − log(1 + b(s−1)/P))` is *increasing in both `s` and `P`*
whenever `P ≥ b` (Lean-checked below), exactly the certificate's use of
`s_lower[m]` in both the count and the penalty.

The `b = 0` case (shells `m ≤ 60`) has no penalty and is separated out. -/

/-- Primality of a shell prime: `p ∈ shellPrimes N m` gives `Nat.Prime p`.  One
of three membership extractors (with `shellPrimes_shell_real` and
`shellPrimes_gt_m`) that keep each shell instantiation a one-liner. -/
theorem shellPrimes_prime {N m p : ℕ} (hp : p ∈ shellPrimes N m) : Nat.Prime p :=
  (mem_shellPrimes.mp hp).2.2

/-- On the `m`-th shell every prime exceeds `⌊N/(m+1)⌋`, hence (as reals) exceeds
`N/(m+1)` up to the floor, which is what the collision lemma consumes. -/
theorem shellPrimes_shell_real {N m p : ℕ}
    (hp : p ∈ shellPrimes N m) : (N : ℝ) / ((m : ℝ) + 1) < (p : ℝ) := by
  have h := (mem_shellPrimes.mp hp).1
  have key : N < p * (m + 1) := (Nat.div_lt_iff_lt_mul (Nat.succ_pos m)).mp h
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [div_lt_iff₀ hm1]
  have hc : (N : ℝ) < ((p * (m + 1) : ℕ) : ℝ) := by exact_mod_cast key
  push_cast at hc
  linarith

/-- On the `m`-th shell every prime exceeds `m` (needed for `sigma`↔`S`), given
`m·(m+1) ≤ N` so that `⌊N/(m+1)⌋ ≥ m`. -/
theorem shellPrimes_gt_m {N m p : ℕ} (hbN : m * (m + 1) ≤ N)
    (hp : p ∈ shellPrimes N m) : m < p := by
  have h := (mem_shellPrimes.mp hp).1
  have hmle : m ≤ N / (m + 1) :=
    (Nat.le_div_iff_mul_le (Nat.succ_pos m)).mpr hbN
  omega

/-- **`b = 0` shell contribution** (shells `m ≤ 60`): with no collision penalty,
`∑_{p ∈ shell} log σ ≥ P.card · g m ≥ Pm · ℓ` for rational `Pm ≤ P.card`,
`ℓ ≤ g m`, `0 ≤ ℓ`, `0 < Pm`. -/
theorem shell_contribution_b0 {N m : ℕ} (Pm ℓ : ℝ) (hbN : m * (m + 1) < N)
    (hbig : (1 : ℝ) < (N : ℝ) / ((m : ℝ) + 1))
    (hWlt : (((Finset.Icc 1 m).lcm id : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ)
            < ((N : ℝ) / ((m : ℝ) + 1)) ^ (0 + 1))
    (hPmpos : 0 < Pm) (hPmle : Pm ≤ ((shellPrimes N m).card : ℝ))
    (hℓ : ℓ ≤ g m) (hℓpos : 0 ≤ ℓ) :
    Pm * ℓ ≤ ∑ p ∈ shellPrimes N m, Real.log (sigma p m) := by
  have hcardpos : (0 : ℝ) < ((shellPrimes N m).card : ℝ) := lt_of_lt_of_le hPmpos hPmle
  have hne : (shellPrimes N m).Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hcardpos
  have hcoll := shell_collision_lower_tight (shellPrimes N m) hne
    (fun p hp => shellPrimes_prime hp) (fun p hp => shellPrimes_gt_m (le_of_lt hbN) hp)
    (fun p hp => shellPrimes_shell_real hp) hbig 0 hWlt
  simp only [Nat.cast_zero, zero_mul, zero_div, add_zero, Real.log_one, sub_zero] at hcoll
  refine le_trans ?_ hcoll
  exact mul_le_mul hPmle hℓ hℓpos hcardpos.le

/-- **General shell contribution** (any `b`, so it also covers `b ≥ 1`, shells
`m ≥ 61`).  With rational lower bounds `Pm ≤ P.card`, `sL ≤ S m` and a rational
penalty upper bound `pen ≥ log(1 + b(sL−1)/Pm)`, and the crucial `b ≤ Pm`,
```
Pm·(ℓ − pen) ≤ ∑_{p ∈ shell} log σ_p(m).
```
The proof supplies the two monotonicities of `f(s,P) = P·(log s − log(1+b(s−1)/P))`
— increasing in `P` (`Pm ≤ P.card`) and in `s` (`sL ≤ S m`) — each of which
reduces to `(P − b)(s − s') ≥ 0`, valid since `P ≥ b` and `s ≥ s'`. -/
theorem shell_contribution_pos {N m : ℕ} (b : ℕ) (Pm ℓ pen : ℝ) (sL : ℕ)
    (hbN : m * (m + 1) ≤ N)
    (hbig : (1 : ℝ) < (N : ℝ) / ((m : ℝ) + 1))
    (hWlt : (((Finset.Icc 1 m).lcm id : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ)
            < ((N : ℝ) / ((m : ℝ) + 1)) ^ (b + 1))
    (hPmpos : 0 < Pm) (hPmle : Pm ≤ ((shellPrimes N m).card : ℝ))
    (hbP : (b : ℝ) ≤ Pm) (hsL1 : 1 ≤ sL) (hsLS : sL ≤ S m)
    (hℓ : ℓ ≤ Real.log (sL : ℝ))
    (hpen : Real.log (1 + (b : ℝ) * ((sL : ℝ) - 1) / Pm) ≤ pen) :
    Pm * (ℓ - pen) ≤ ∑ p ∈ shellPrimes N m, Real.log (sigma p m) := by
  have hcardpos : (0 : ℝ) < ((shellPrimes N m).card : ℝ) := lt_of_lt_of_le hPmpos hPmle
  have hne : (shellPrimes N m).Nonempty := by rw [← Finset.card_pos]; exact_mod_cast hcardpos
  have hcoll := shell_collision_lower_tight (shellPrimes N m) hne
    (fun p hp => shellPrimes_prime hp) (fun p hp => shellPrimes_gt_m hbN hp)
    (fun p hp => shellPrimes_shell_real hp) hbig b hWlt
  refine le_trans ?_ hcoll
  set Pc : ℝ := ((shellPrimes N m).card : ℝ) with hPcdef
  set Sm : ℝ := ((S m : ℕ) : ℝ) with hSmdef
  have hgeq : g m = Real.log Sm := rfl
  rw [hgeq]
  have hPcpos : 0 < Pc := hcardpos
  have hbnn : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hSmge1 : (1 : ℝ) ≤ Sm := by rw [hSmdef]; exact_mod_cast one_le_S m
  have hsLR1 : (1 : ℝ) ≤ (sL : ℝ) := by exact_mod_cast hsL1
  have hsLSm : (sL : ℝ) ≤ Sm := by rw [hSmdef]; exact_mod_cast hsLS
  have hbPc : (b : ℝ) ≤ Pc := le_trans hbP hPmle
  have hSm1 : (0 : ℝ) ≤ Sm - 1 := by linarith
  have hsL1' : (0 : ℝ) ≤ (sL : ℝ) - 1 := by linarith
  -- the three penalty arguments and their positivity
  set A : ℝ := 1 + (b : ℝ) * (Sm - 1) / Pc with hAdef
  set Ap : ℝ := 1 + (b : ℝ) * (Sm - 1) / Pm with hApdef
  set App : ℝ := 1 + (b : ℝ) * ((sL : ℝ) - 1) / Pm with hAppdef
  have hApos : 0 < A := by
    rw [hAdef]; have := div_nonneg (mul_nonneg hbnn hSm1) hPcpos.le; linarith
  have hAppos : 0 < Ap := by
    rw [hApdef]; have := div_nonneg (mul_nonneg hbnn hSm1) hPmpos.le; linarith
  have hApppos : 0 < App := by
    rw [hAppdef]; have := div_nonneg (mul_nonneg hbnn hsL1') hPmpos.le; linarith
  -- (a) `A ≤ Sm` (penalty ≤ count): `(Pc − b)(Sm − 1) ≥ 0`
  have hAleSm : A ≤ Sm := by
    rw [hAdef]
    have h : (b : ℝ) * (Sm - 1) / Pc ≤ Sm - 1 := by
      rw [div_le_iff₀ hPcpos]; nlinarith [hbPc, hSm1]
    linarith
  have hbrk : 0 ≤ Real.log Sm - Real.log A := by
    have := Real.log_le_log hApos hAleSm; linarith
  -- (b) `A ≤ Ap` (penalty decreases when the count grows): `Pm ≤ Pc`
  have hAleAp : A ≤ Ap := by
    rw [hAdef, hApdef]
    have := div_le_div_of_nonneg_left (mul_nonneg hbnn hSm1) hPmpos hPmle
    linarith
  have hlogAAp : Real.log A ≤ Real.log Ap := Real.log_le_log hApos hAleAp
  -- (c) S-monotonicity: `sL·Ap ≤ Sm·App`, i.e. `(Pm − b)(Sm − sL) ≥ 0`
  have hPmne : Pm ≠ 0 := hPmpos.ne'
  have hSmono : (sL : ℝ) * Ap ≤ Sm * App := by
    rw [hApdef, hAppdef]
    refine le_of_mul_le_mul_right ?_ hPmpos
    have expand : ((sL : ℝ) * (1 + (b : ℝ) * (Sm - 1) / Pm)) * Pm
        = (sL : ℝ) * Pm + (sL : ℝ) * (b : ℝ) * (Sm - 1) := by field_simp
    have expand2 : (Sm * (1 + (b : ℝ) * ((sL : ℝ) - 1) / Pm)) * Pm
        = Sm * Pm + Sm * (b : ℝ) * ((sL : ℝ) - 1) := by field_simp
    rw [expand, expand2]
    nlinarith [mul_nonneg (by linarith [hbP] : (0 : ℝ) ≤ Pm - b)
      (by linarith : (0 : ℝ) ≤ Sm - (sL : ℝ))]
  have hlogSmono : Real.log (sL : ℝ) - Real.log App ≤ Real.log Sm - Real.log Ap := by
    have h1 : Real.log ((sL : ℝ) * Ap) ≤ Real.log (Sm * App) :=
      Real.log_le_log (by positivity) hSmono
    rw [Real.log_mul (by positivity) hAppos.ne', Real.log_mul (by positivity) hApppos.ne'] at h1
    linarith
  -- assemble: `ℓ − pen ≤ log Sm − log A`
  have hmid : ℓ - pen ≤ Real.log Sm - Real.log A := by
    have hpen' : Real.log App ≤ pen := hpen
    linarith [hℓ, hpen', hlogSmono, hlogAAp]
  -- combine the two monotonicities
  calc Pm * (ℓ - pen)
      ≤ Pm * (Real.log Sm - Real.log A) :=
        mul_le_mul_of_nonneg_left hmid hPmpos.le
    _ ≤ Pc * (Real.log Sm - Real.log A) :=
        mul_le_mul_of_nonneg_right hPmle hbrk
    _ = Pc * (Real.log Sm - Real.log (1 + (b : ℝ) * (Sm - 1) / Pc)) := by rw [hAdef]

/-! ## Steps 1–2: `g(N₁) ≥ ∑_{m=1}^{10⁶} ∑_{p ∈ shell m} log σ_p(m)`

The large-prime decomposition (`prop:large-prime-decomposition`) regrouped into
shells (`prop:averaging-relation`, eq. `shell-sum`).  This is exactly the lower
half of `g_shell_decomposition` at `N = N₁`, `M = 10⁶`, so it needs only the two
concrete `ℕ`-arithmetic hypotheses `Q < N₁` and `N₁ < Q²`
(`Q = ⌊N₁/(10⁶+1)⌋`). -/

/-- `N₁ = ⌊e⁶⁵⌋`. -/
abbrev highN : ℕ := 16948892444103337141417836114

/-- `Q = ⌊N₁/(10⁶+1)⌋`, the decomposition threshold of the high bridge. -/
theorem highN_div : highN / (1000000 + 1) = 16948875495227841913575 := by
  norm_num [highN]

theorem high_shell_sum_le_g :
    (∑ m ∈ Finset.Icc 1 1000000, ∑ p ∈ shellPrimes highN m,
        Real.log (sigma p m)) ≤ g highN := by
  have hQN : highN / (1000000 + 1) < highN := by
    rw [highN_div]; norm_num [highN]
  have hQ2 : highN < highN / (1000000 + 1) * (highN / (1000000 + 1)) := by
    rw [highN_div]; norm_num [highN]
  exact (g_shell_decomposition hQN hQ2).1

/-! ## A sharp lower bound on `log N₁`

The final scaling by `log N₁ / N₁` needs `log N₁` to the precision the bridge
demands.  The a-priori `cert_log_N1_bounds` gives only `log N₁ ≥ 64.99`, which is
*too coarse*: rescaling the certificate's shell sum by `64.99/65` drops the total
to `≈ 3.2407 < 3.2411`.  The ground-truth total survives at `log N₁ ≥ 64.999`
(scaled total `≈ 3.24114`), so that is what we prove here, by the same
`exp`-comparison as `cert_log_N1_bounds` but with the sharper split
`exp 64.999 · exp 0.001 = exp 65`. -/
theorem high_log_N1_lower : (64.999 : ℝ) ≤ Real.log (highN : ℝ) := by
  have hpos : (0 : ℝ) < (highN : ℝ) := by norm_num [highN]
  rw [Real.le_log_iff_exp_le hpos]
  have heq : Real.exp (65 : ℝ) = Real.exp 1 ^ 65 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hub : Real.exp (65 : ℝ) ≤ 1.695e28 := by
    have h1 : Real.exp 1 ^ 65 ≤ (2.7182818286 : ℝ) ^ 65 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 65
    have h2 : (2.7182818286 : ℝ) ^ 65 ≤ 1.695e28 := by norm_num
    rw [heq]; linarith
  have hsplit : Real.exp (64.999 : ℝ) * Real.exp (0.001 : ℝ) = Real.exp (65 : ℝ) := by
    rw [← Real.exp_add]; norm_num
  have h1 : (1.001 : ℝ) ≤ Real.exp (0.001 : ℝ) := by
    have := Real.add_one_le_exp (0.001 : ℝ); linarith
  have h2 : Real.exp (64.999 : ℝ) * 1.001 ≤ Real.exp (65 : ℝ) := by
    rw [← hsplit]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have h3 : Real.exp (64.999 : ℝ) * 1.001 ≤ 1.695e28 := le_trans h2 hub
  have hN : (1.695e28 : ℝ) ≤ (highN : ℝ) * 1.001 := by norm_num [highN]
  nlinarith [Real.exp_pos (64.999 : ℝ)]

/-- Companion upper bound `log N₁ ≤ 65.001`, needed as the Dusart denominator
`Lb ≥ log(N₁/m)` in each shell's prime count.  Same `exp`-comparison as
`high_log_N1_lower`, using `exp 65 ≥ 1.6948·10²⁸` and `exp 0.001 ≥ 1.001`. -/
theorem high_log_N1_upper : Real.log (highN : ℝ) ≤ 65.001 := by
  have hpos : (0 : ℝ) < (highN : ℝ) := by norm_num [highN]
  rw [Real.log_le_iff_le_exp hpos]
  have heq : Real.exp (65 : ℝ) = Real.exp 1 ^ 65 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hlb : (1.6948e28 : ℝ) ≤ Real.exp (65 : ℝ) := by
    have h1 : (2.7182818283 : ℝ) ^ 65 ≤ Real.exp 1 ^ 65 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 65
    have h2 : (1.6948e28 : ℝ) ≤ (2.7182818283 : ℝ) ^ 65 := by norm_num
    rw [heq]; linarith
  have h1 : (1.001 : ℝ) ≤ Real.exp (0.001 : ℝ) := by
    have := Real.add_one_le_exp (0.001 : ℝ); linarith
  have hsplit : Real.exp (65.001 : ℝ) = Real.exp (65 : ℝ) * Real.exp (0.001 : ℝ) := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  have hprod : (1.6948e28 : ℝ) * 1.001 ≤ Real.exp (65 : ℝ) * Real.exp (0.001 : ℝ) :=
    mul_le_mul hlb h1 (by norm_num) (Real.exp_pos _).le
  have hN : (highN : ℝ) ≤ 1.6948e28 * 1.001 := by norm_num [highN]
  linarith

/-- **Reusable `hWlt` for a concrete shell.**  The tight collision hypothesis
`(L_m:ℝ)·H_m < (N₁/(m+1))^(b+1)` of `shell_contribution_*`, proved by evaluating
the exact rational `L_m·H_m` and the power inequality with `native_decide` in ℚ
(instant) and casting to ℝ.  Each shell supplies its own `m, b` and discharges
the `native_decide`. -/
theorem hWlt_of_ratLt {N m b : ℕ}
    (hq : (((Finset.Icc 1 m).lcm id : ℕ) : ℚ) * harmonicSum m
          < ((N : ℚ) / ((m : ℚ) + 1)) ^ (b + 1)) :
    (((Finset.Icc 1 m).lcm id : ℕ) : ℝ) * ((harmonicSum m : ℚ) : ℝ)
      < ((N : ℝ) / ((m : ℝ) + 1)) ^ (b + 1) := by
  have h := (Rat.cast_lt (K := ℝ)).mpr hq
  push_cast at h
  exact h

/-! ## Step 4: the final assembly, reduced to the shell-sum ledger

`F(N₁) = (log N₁ / N₁)·g(N₁)`, and `g(N₁) ≥ ∑_{m,p} log σ_p(m)`
(`high_shell_sum_le_g`).  So any rational lower bound `Krat` on that shell sum
with `3.2411·N₁ < 64.999·Krat` (and `64.999 ≤ log N₁`, `high_log_N1_lower`)
yields `F(N₁) > 3.2411`.

This isolates the remaining work — the 154-shell + aggregate collision ledger —
into the single hypothesis `hK`.  The ground-truth witness is
`Krat ≈ 8.4515·10²⁶` (`64.999·Krat/N₁ ≈ 3.24114`). -/
theorem highFiniteInput_of_shell_sum_ge (Krat : ℚ) (hKpos : 0 ≤ Krat)
    (hslack : (3.2411 : ℝ) * (highN : ℝ) < 64.999 * (Krat : ℝ))
    (hK : (Krat : ℝ) ≤ ∑ m ∈ Finset.Icc 1 1000000, ∑ p ∈ shellPrimes highN m,
            Real.log (sigma p m)) :
    (3.2411 : ℝ) < F highN := by
  have hg : (Krat : ℝ) ≤ g highN := le_trans hK high_shell_sum_le_g
  have hNpos : (0 : ℝ) < (highN : ℝ) := by norm_num [highN]
  have hlog := high_log_N1_lower
  have hFeq : F highN = Real.log (highN : ℝ) / (highN : ℝ) * g highN := rfl
  rw [hFeq, div_mul_eq_mul_div, lt_div_iff₀ hNpos]
  have hprod : (64.999 : ℝ) * (Krat : ℝ) ≤ Real.log (highN : ℝ) * g highN :=
    mul_le_mul hlog hg (by exact_mod_cast hKpos)
      (le_trans (by norm_num) hlog)
  linarith [hslack, hprod]

end Erdos320
