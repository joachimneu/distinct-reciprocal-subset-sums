import Erdos320.Defs.Basic
import Erdos320.Defs.ModularImage
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Reduction of rationals with `p`-coprime denominators into `ZMod p`

Machinery for the manuscript's Proposition `prop:large-prime-decomposition`
(§ `sec:large-prime-decomposition`): a rational subset sum whose (reduced)
denominator is coprime to a prime `p` can be reduced modulo `p`, and the
reduction is a homomorphism on such rationals.  The paper uses this twice:

* "multiplication by `p` followed by reduction modulo `p` sends its subset
  sums to `Σ_p(⌊N/p⌋)`" — the map `ratToZMod` below realizes "reduction
  modulo `p`" on rationals, and `ratToZMod_image_reciprocalSubsetSumSet`
  shows it carries the rational image `𝓔_m` *onto* the modular image
  `Σ_p(m)` when `m < p` (so `σ_p(m) ≤ S(m)`, `sigma_le_S`);
* in `lem:average-collision` the finite set `T ⊆ ℚ` is scaled by
  `L = L(T)` into the integer set `L·T ⊆ ℤ` and reduced modulo primes `p`
  not dividing `L`; `card_image_intCast_scaled_eq_card_image_ratToZMod`
  says this integer reduction has exactly as many values as the direct
  rational reduction of `T`.

The load-bearing fact is `ratToZMod_unique`: for prime `p`, the value of the
reduction can be computed from **any** fraction representation `x = a / b`
with denominator `b` prime to `p` — not just the reduced one.  Additivity and
all the bridges follow from it by common-denominator arithmetic in the field
`ZMod p`.
-/

namespace Erdos320

open Finset

/-- Reduction of a rational with denominator prime to `p` into `ZMod p`:
`x = num/den ↦ num · den⁻¹` with the inverse taken in `ZMod p`.  For
denominators divisible by `p` the value is junk (Mathlib's `ZMod`-inverse of
a non-unit is `0`), so the lemmas below that pin down its value assume
`¬ p ∣ x.den` (or restrict to integers). -/
def ratToZMod (p : ℕ) (x : ℚ) : ZMod p := (x.num : ZMod p) * (x.den : ZMod p)⁻¹

/-- For a prime `p`, the hand-rolled reduction `ratToZMod p` **is** Mathlib's
canonical rational cast `Rat.cast : ℚ → ZMod p` — well-defined because `ZMod p`
is a field under `Fact p.Prime`.  This bridge lets the lemmas below reuse the
`Rat.cast_*_of_ne_zero` family instead of re-deriving representation
independence, additivity, and scaling by hand.  (The `[Fact p.Prime]` binder is
needed already to *state* the right-hand side: the `RatCast (ZMod p)` instance
comes from the field structure.) -/
theorem ratToZMod_eq_ratCast (p : ℕ) [Fact p.Prime] (x : ℚ) :
    ratToZMod p x = ((x : ℚ) : ZMod p) := by
  rw [ratToZMod, Rat.cast_def, div_eq_mul_inv]

@[simp] theorem ratToZMod_intCast (p : ℕ) (n : ℤ) :
    ratToZMod p (n : ℚ) = (n : ZMod p) := by
  simp [ratToZMod]

@[simp] theorem ratToZMod_natCast (p : ℕ) (n : ℕ) :
    ratToZMod p (n : ℚ) = (n : ZMod p) := by
  simp [ratToZMod]

@[simp] theorem ratToZMod_zero (p : ℕ) : ratToZMod p 0 = 0 := by
  simp [ratToZMod]

@[simp] theorem ratToZMod_one (p : ℕ) : ratToZMod p 1 = 1 := by
  simp [ratToZMod]

/-- If `x · b = a` with `a, b` integers, then the corresponding identity
`x.num · b = a · x.den` holds between the numerator and reduced denominator. -/
theorem num_mul_eq_of_mul_intCast_eq {x : ℚ} {a b : ℤ}
    (hab : x * (b : ℚ) = (a : ℚ)) : x.num * b = a * (x.den : ℤ) := by
  have h : ((x.num * b : ℤ) : ℚ) = ((a * (x.den : ℤ) : ℤ) : ℚ) := by
    push_cast
    linear_combination (x.den : ℚ) * hab - (b : ℚ) * Rat.mul_den_eq_num x
  exact_mod_cast h

/-- If `x` admits *some* fraction representation `x = a / b` (in the form
`x · b = a`) whose denominator `b` is prime to the prime `p`, then the
*reduced* denominator of `x` is also prime to `p`. -/
theorem not_dvd_den_of_mul_intCast_eq {p : ℕ} (hp : p.Prime) {x : ℚ} {a b : ℤ}
    (hb : ¬ (p : ℤ) ∣ b) (hab : x * (b : ℚ) = (a : ℚ)) : ¬ p ∣ x.den := by
  haveI := Fact.mk hp
  intro hpden
  have key : x.num * b = a * (x.den : ℤ) := num_mul_eq_of_mul_intCast_eq hab
  have hdZ : ((x.den : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff x.den p).mpr hpden
  have keyZ : (x.num : ZMod p) * (b : ZMod p) = 0 := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) key
    push_cast at h
    rw [h, hdZ, mul_zero]
  have hbZ : (b : ZMod p) ≠ 0 := fun h0 =>
    hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h0)
  have hnum : (p : ℤ) ∣ x.num := by
    rcases mul_eq_zero.mp keyZ with h0 | h0
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd x.num p).mp h0
    · exact absurd h0 hbZ
  have hgcd : p ∣ Nat.gcd x.num.natAbs x.den :=
    Nat.dvd_gcd (Int.natCast_dvd.mp hnum) hpden
  rw [Nat.coprime_iff_gcd_eq_one.mp x.reduced] at hgcd
  exact hp.ne_one (Nat.dvd_one.mp hgcd)

/-- **Workhorse.**  For prime `p`, the reduction `ratToZMod p x` can be
computed from *any* fraction representation of `x` with denominator prime to
`p`: if `x · b = a` in `ℚ` with `¬ (p : ℤ) ∣ b`, then
`ratToZMod p x = a · b⁻¹` in `ZMod p`.  In particular the value does not
depend on the representation being reduced. -/
theorem ratToZMod_unique {p : ℕ} (hp : p.Prime) {x : ℚ} {a b : ℤ}
    (hb : ¬ (p : ℤ) ∣ b) (hab : x * (b : ℚ) = (a : ℚ)) :
    ratToZMod p x = (a : ZMod p) * (b : ZMod p)⁻¹ := by
  haveI := Fact.mk hp
  have hbZ : (b : ZMod p) ≠ 0 := fun h0 =>
    hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h0)
  have hbℚ : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr fun h => hb (h ▸ dvd_zero (p : ℤ))
  -- `x·b = a` with `b ≠ 0` pins `x = a / b`; then Mathlib's cast of `divInt`
  -- (valid since `(b : ZMod p) ≠ 0`) does the representation-independence work.
  have hxeq : x = Rat.divInt a b := by
    rw [Rat.divInt_eq_div, eq_div_iff hbℚ]; exact hab
  rw [ratToZMod_eq_ratCast p, hxeq, Rat.cast_divInt_of_ne_zero a hbZ, div_eq_mul_inv]

/-- Reduction of a unit fraction: `ratToZMod p (1/k) = k⁻¹` in `ZMod p` for
`¬ p ∣ k`.  This matches the manuscript's eq. `sigma-def`, where "the
inverses are taken in `𝔽_p`". -/
theorem ratToZMod_inv_natCast {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : ¬ p ∣ k) :
    ratToZMod p (1 / (k : ℚ)) = (k : ZMod p)⁻¹ := by
  have hk0 : (k : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h0 => hk (h0 ▸ dvd_zero p)
  have hb : ¬ (p : ℤ) ∣ ((k : ℕ) : ℤ) := fun hd => hk (Int.natCast_dvd_natCast.mp hd)
  have hab : (1 / (k : ℚ)) * (((k : ℕ) : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
    push_cast
    rw [one_div, inv_mul_cancel₀ hk0]
  have h := ratToZMod_unique hp hb hab
  simpa using h

/-- Additivity of the reduction on rationals with `p`-coprime denominators. -/
theorem ratToZMod_add {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : ¬ p ∣ x.den) (hy : ¬ p ∣ y.den) :
    ratToZMod p (x + y) = ratToZMod p x + ratToZMod p y := by
  haveI := Fact.mk hp
  have hdx : (x.den : ZMod p) ≠ 0 := fun h0 =>
    hx ((ZMod.natCast_eq_zero_iff x.den p).mp h0)
  have hdy : (y.den : ZMod p) ≠ 0 := fun h0 =>
    hy ((ZMod.natCast_eq_zero_iff y.den p).mp h0)
  rw [ratToZMod_eq_ratCast p, ratToZMod_eq_ratCast p, ratToZMod_eq_ratCast p,
    Rat.cast_add_of_ne_zero hdx hdy]

/-- A sum of two rationals with `p`-coprime denominators again has a
`p`-coprime denominator (the sum's denominator divides the product of the
denominators). -/
theorem not_dvd_den_add {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : ¬ p ∣ x.den) (hy : ¬ p ∣ y.den) : ¬ p ∣ (x + y).den := fun h =>
  (hp.dvd_mul.mp (h.trans (Rat.add_den_dvd x y))).elim hx hy

/-- A finite sum of rationals with `p`-coprime denominators has a
`p`-coprime denominator. -/
theorem not_dvd_den_sum {p : ℕ} (hp : p.Prime) {ι : Type*} {s : Finset ι}
    {f : ι → ℚ} (h : ∀ i ∈ s, ¬ p ∣ (f i).den) : ¬ p ∣ (∑ i ∈ s, f i).den := fun hd =>
  Prime.not_dvd_finsetProd hp.prime h (hd.trans (Finset.Rat.den_sum_dvd_prod_den s f))

/-- The reduction commutes with finite sums of rationals with `p`-coprime
denominators. -/
theorem ratToZMod_sum {p : ℕ} (hp : p.Prime) {ι : Type*} {s : Finset ι}
    {f : ι → ℚ} (h : ∀ i ∈ s, ¬ p ∣ (f i).den) :
    ratToZMod p (∑ i ∈ s, f i) = ∑ i ∈ s, ratToZMod p (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s _ ih =>
    rw [Finset.sum_cons, Finset.sum_cons,
      ratToZMod_add hp (h a (Finset.mem_cons_self a s))
        (not_dvd_den_sum hp fun i hi => h i (Finset.mem_cons_of_mem hi)),
      ih fun i hi => h i (Finset.mem_cons_of_mem hi)]

/-- For `p` prime and `m < p`, reduction modulo `p` maps the rational image
`𝓔_m` **onto** the modular image `Σ_p(m)`: both are images of the same
powerset, and on subsets of `{1, …, m}` the reduction of `∑ 1/k` is
`∑ k⁻¹` in `ZMod p`.  This is the map used in the proof of
`prop:large-prime-decomposition` ("multiplication by `p` followed by
reduction modulo `p`" acts on each large-prime block this way). -/
theorem ratToZMod_image_reciprocalSubsetSumSet {p m : ℕ} (hp : Nat.Prime p)
    (hmp : m < p) :
    (reciprocalSubsetSumSet m).image (ratToZMod p) = modularImage p m := by
  simp only [reciprocalSubsetSumSet, modularImage]
  rw [Finset.image_image]
  refine Finset.image_congr fun A hA => ?_
  have hsub : A ⊆ Icc 1 m := Finset.mem_powerset.mp (Finset.mem_coe.mp hA)
  have hnd : ∀ k ∈ A, ¬ p ∣ k := by
    intro k hk hdvd
    have hk' := Finset.mem_Icc.mp (hsub hk)
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hden : ∀ k ∈ A, ¬ p ∣ ((1 : ℚ) / (k : ℚ)).den := by
    intro k hk
    have hk0 : (k : ℚ) ≠ 0 := by
      have hk' := Finset.mem_Icc.mp (hsub hk)
      exact Nat.cast_ne_zero.mpr (by omega)
    have hb : ¬ (p : ℤ) ∣ ((k : ℕ) : ℤ) := fun hd =>
      hnd k hk (Int.natCast_dvd_natCast.mp hd)
    refine not_dvd_den_of_mul_intCast_eq hp hb (a := 1) ?_
    push_cast
    rw [one_div, inv_mul_cancel₀ hk0]
  show ratToZMod p (∑ n ∈ A, (1 : ℚ) / (n : ℚ)) = ∑ k ∈ A, (k : ZMod p)⁻¹
  rw [ratToZMod_sum hp hden]
  exact Finset.sum_congr rfl fun k hk => ratToZMod_inv_natCast hp (hnd k hk)

/-- `σ_p(m) ≤ S(m)` for `p` prime and `m < p`: the modular image `Σ_p(m)` is
a quotient (an image) of the rational image `𝓔_m`.  This is the counting
consequence of the reduction map used in `prop:large-prime-decomposition`. -/
theorem sigma_le_S {p m : ℕ} (hp : Nat.Prime p) (hmp : m < p) : sigma p m ≤ S m := by
  show (modularImage p m).card ≤ (reciprocalSubsetSumSet m).card
  rw [← ratToZMod_image_reciprocalSubsetSumSet hp hmp]
  exact Finset.card_image_le

/-- On integers (rationals with denominator `1`) the reduction is just the
numerator cast into `ZMod p` — no primality needed. -/
theorem ratToZMod_of_den_eq_one {p : ℕ} {x : ℚ} (h : x.den = 1) :
    ratToZMod p x = (x.num : ZMod p) := by
  show (x.num : ZMod p) * ((x.den : ZMod p))⁻¹ = (x.num : ZMod p)
  rw [h]
  simp

/-- Scaling by a natural number commutes with the reduction:
`ratToZMod p (L·x) = L · ratToZMod p x` for `¬ p ∣ x.den`. -/
theorem ratToZMod_natCast_mul {p : ℕ} (hp : p.Prime) (L : ℕ) {x : ℚ}
    (hx : ¬ p ∣ x.den) :
    ratToZMod p ((L : ℚ) * x) = (L : ZMod p) * ratToZMod p x := by
  haveI := Fact.mk hp
  have hdx : (x.den : ZMod p) ≠ 0 := fun h0 =>
    hx ((ZMod.natCast_eq_zero_iff x.den p).mp h0)
  have hdL : (((L : ℚ)).den : ZMod p) ≠ 0 := by simp
  rw [ratToZMod_eq_ratCast p, ratToZMod_eq_ratCast p,
    Rat.cast_mul_of_ne_zero hdL hdx, Rat.cast_natCast]

/-- **Scaling bridge, rational form.**  For a prime `p`, a scalar `L` with
`¬ p ∣ L`, and a finite set `T ⊆ ℚ` of rationals with `p`-coprime
denominators, the scaled set `L·T` has exactly as many residues modulo `p`
as `T` itself: scaling acts on the residues as multiplication by the unit
`L` of `ZMod p`, which is injective. -/
theorem card_image_ratToZMod_natCast_mul {p : ℕ} (hp : p.Prime) {L : ℕ}
    (hL : ¬ p ∣ L) (T : Finset ℚ) (hT : ∀ x ∈ T, ¬ p ∣ x.den) :
    ((T.image fun x => (L : ℚ) * x).image (ratToZMod p)).card
      = (T.image (ratToZMod p)).card := by
  haveI := Fact.mk hp
  have hL0 : (L : ZMod p) ≠ 0 := fun h0 => hL ((ZMod.natCast_eq_zero_iff L p).mp h0)
  have himg : (T.image fun x => (L : ℚ) * x).image (ratToZMod p)
      = (T.image (ratToZMod p)).image fun z => (L : ZMod p) * z := by
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr fun x hx => ?_
    simp only [Function.comp_apply]
    exact ratToZMod_natCast_mul hp L (hT x (Finset.mem_coe.mp hx))
  rw [himg, Finset.card_image_of_injective _ (mul_right_injective₀ hL0)]

/-- **Scaling bridge, integer form** — the shape `lem:average-collision`
consumes.  Suppose `L` clears all denominators of the finite set `T ⊆ ℚ`
(every `L·x` with `x ∈ T` is an integer, stated as `((L:ℚ)*x).den = 1` —
for `L = L(T)` this is the paper's integer set `L(T)·T ⊆ ℤ`), and `p` is a
prime not dividing `L`.  Then the integer set `L·T` reduced modulo `p` (via
`Int.cast : ℤ → ZMod p`) has exactly as many elements as the direct rational
reduction `T.image (ratToZMod p)` — the paper's `|T mod p|` in
eq. `average-collision`.
Note the denominator-coprimality of the elements of `T` is *derived*, not
assumed: `x · L ∈ ℤ` and `p ∤ L` force `p ∤ x.den`. -/
theorem card_image_intCast_scaled_eq_card_image_ratToZMod {p : ℕ}
    (hp : p.Prime) {L : ℕ} (hL : ¬ p ∣ L) (T : Finset ℚ)
    (hT : ∀ x ∈ T, ((L : ℚ) * x).den = 1) :
    ((T.image fun x => ((L : ℚ) * x).num).image fun z : ℤ => (z : ZMod p)).card
      = (T.image (ratToZMod p)).card := by
  have hden : ∀ x ∈ T, ¬ p ∣ x.den := by
    intro x hx
    have h1 : ((((L : ℚ) * x).num : ℤ) : ℚ) = (L : ℚ) * x :=
      (Rat.den_eq_one_iff _).mp (hT x hx)
    have hb : ¬ (p : ℤ) ∣ ((L : ℕ) : ℤ) := fun hd => hL (Int.natCast_dvd_natCast.mp hd)
    refine not_dvd_den_of_mul_intCast_eq hp hb (a := ((L : ℚ) * x).num) ?_
    push_cast
    linear_combination -h1
  have himg : (T.image fun x => ((L : ℚ) * x).num).image (fun z : ℤ => (z : ZMod p))
      = (T.image fun x => (L : ℚ) * x).image (ratToZMod p) := by
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr fun x hx => ?_
    simp only [Function.comp_apply]
    exact (ratToZMod_of_den_eq_one (hT x (Finset.mem_coe.mp hx))).symm
  rw [himg, card_image_ratToZMod_natCast_mul hp hL T hden]

end Erdos320
