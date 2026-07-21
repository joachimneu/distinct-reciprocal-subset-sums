-- Import only the Mathlib modules actually used, not all of `Mathlib` (see
-- `Erdos320/Defs/Basic.lean` for the rationale).
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The average collision bound (paper `lem:average-collision`)

This file formalizes the manuscript's Lemma "Average collision bound"
(`lem:average-collision`, eq. `average-collision`), the elementary
second-moment estimate that turns the modular images of the large-prime
decomposition into an asymptotic formula.

**Decoupled integer form.** The paper states the lemma for a nonempty finite
set `T ⊂ ℚ`, scaled by the least common denominator `L(T)` so that
`L(T)·T ⊂ ℤ`, with `𝓟` a finite set of primes *not dividing `L(T)`* (so that
reduction of `T` modulo `p` agrees with reduction of the integer set
`L(T)·T`). Here we work directly with the integer set `T ⊂ ℤ` (the paper's
`L(T)·T`); the `ℚ → ℤ` scaling, and with it the "primes not dividing `L(T)`"
side condition, happens at the application site. In this decoupled form the
moduli need not even be prime: the counting argument (Cauchy–Schwarz on the
fibres, double counting of collisions, concavity of `log`) never uses
primality, so `average_collision_bound` below is stated for an arbitrary
nonempty finite set of natural moduli. Primality re-enters only in the
lemma's "In particular" clause (`card_filter_dvd_le_of_abs_le`), which bounds
the admissible collision multiplicity `b`.

Main results:

* `average_collision_bound` — eq. `average-collision`:
  `∑_{p ∈ 𝓟} log |T mod p| ≥ |𝓟| · [log s − log(1 + b(s−1)/|𝓟|)]`
  where `s = |T|` and every nonzero difference of two elements of `T` is
  divisible by at most `b` of the moduli in `𝓟`.
* `card_filter_dvd_le_of_abs_le` — the "In particular" clause: a nonzero
  integer of absolute value at most `W` is divisible by at most
  `log W / log p₀` primes exceeding `p₀ > 1`.
-/

namespace Erdos320

open Finset Function

/-- `orderedCollisionCount T p` is the paper's `E_p` (proof of
`lem:average-collision`): the number of *ordered* pairs `(t, t') ∈ T × T`
having the same image modulo `p`, organized as the sum over `t ∈ T` of the
size of the congruence fibre of `t`. -/
def orderedCollisionCount (T : Finset ℤ) (p : ℕ) : ℕ :=
  ∑ x ∈ T, (T.filter fun y : ℤ => ((y : ZMod p) = (x : ZMod p))).card

/-- The ordered collision count is the second moment of the fibre sizes over
the modular image: `E_p = ∑_{c ∈ T mod p} |{t ∈ T : t ≡ c}|²`. -/
theorem orderedCollisionCount_eq_sum_sq_fiber (T : Finset ℤ) (p : ℕ) :
    orderedCollisionCount T p
      = ∑ c ∈ T.image (fun x : ℤ => (x : ZMod p)),
          (T.filter fun y : ℤ => ((y : ZMod p) = c)).card ^ 2 := by
  have h := Finset.sum_comp (s := T)
    (fun c : ZMod p => (T.filter fun y : ℤ => ((y : ZMod p) = c)).card)
    (fun x : ℤ => (x : ZMod p))
  simpa [orderedCollisionCount, smul_eq_mul, sq] using h

/-- Cauchy–Schwarz on the congruence fibres (paper: `|T mod p| ≥ s²/E_p`,
stated multiplicatively to stay in `ℕ`): `s² ≤ |T mod p| · E_p`. -/
theorem sq_card_le_card_image_mul_orderedCollisionCount (T : Finset ℤ) (p : ℕ) :
    T.card ^ 2
      ≤ (T.image fun x : ℤ => (x : ZMod p)).card * orderedCollisionCount T p := by
  rw [orderedCollisionCount_eq_sum_sq_fiber T p,
    Finset.card_eq_sum_card_image (fun x : ℤ => (x : ZMod p)) T]
  exact sq_sum_le_card_mul_sum_sq

/-- The diagonal pairs alone give `s ≤ E_p`. -/
theorem card_le_orderedCollisionCount (T : Finset ℤ) (p : ℕ) :
    T.card ≤ orderedCollisionCount T p := by
  calc T.card = ∑ _x ∈ T, 1 := by simp
    _ ≤ ∑ x ∈ T, (T.filter fun y : ℤ => ((y : ZMod p) = (x : ZMod p))).card := by
        refine Finset.sum_le_sum fun x hx => ?_
        exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩

/-- Double counting the collisions (paper: `∑_{p ∈ 𝓟} (E_p − s) ≤ b·s·(s−1)`,
stated additively to stay in `ℕ`): if every nonzero difference of two elements
of `T` is divisible by at most `b` of the moduli in `P`, then
`∑_{p ∈ P} E_p ≤ s·|P| + s·(s−1)·b`. -/
theorem sum_orderedCollisionCount_le
    (T : Finset ℤ) (P : Finset ℕ) (b : ℕ)
    (hb : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      (P.filter fun p : ℕ => (p : ℤ) ∣ (x - y)).card ≤ b) :
    ∑ p ∈ P, orderedCollisionCount T p
      ≤ T.card * P.card + T.card * ((T.card - 1) * b) := by
  classical
  -- Reorganize as a sum over ordered pairs of elements of `T` of the number
  -- of moduli at which they collide.
  have hswap : ∑ p ∈ P, orderedCollisionCount T p
      = ∑ x ∈ T, ∑ y ∈ T,
          (P.filter fun p : ℕ => ((y : ZMod p) = (x : ZMod p))).card := by
    unfold orderedCollisionCount
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  -- For each `x ∈ T`: the diagonal pair collides at every modulus, and each
  -- of the `s − 1` off-diagonal pairs collides at most `b` times.
  have hxbound : ∀ x ∈ T,
      ∑ y ∈ T, (P.filter fun p : ℕ => ((y : ZMod p) = (x : ZMod p))).card
        ≤ P.card + (T.card - 1) * b := by
    intro x hx
    rw [← Finset.add_sum_erase T _ hx]
    have hdiag : (P.filter fun p : ℕ => ((x : ZMod p) = (x : ZMod p))).card
        = P.card := by
      rw [Finset.filter_true_of_mem fun p _ => rfl]
    have hoff : ∑ y ∈ T.erase x,
        (P.filter fun p : ℕ => ((y : ZMod p) = (x : ZMod p))).card
          ≤ (T.card - 1) * b := by
      calc ∑ y ∈ T.erase x,
            (P.filter fun p : ℕ => ((y : ZMod p) = (x : ZMod p))).card
          ≤ ∑ _y ∈ T.erase x, b := by
            refine Finset.sum_le_sum fun y hy => ?_
            have hyT : y ∈ T := Finset.mem_of_mem_erase hy
            have hyx : y ≠ x := Finset.ne_of_mem_erase hy
            have hpred : ∀ p ∈ P,
                (((y : ℤ) : ZMod p) = ((x : ℤ) : ZMod p)) ↔ ((p : ℤ) ∣ x - y) :=
              fun p _ => ZMod.intCast_eq_intCast_iff_dvd_sub y x p
            rw [Finset.filter_congr hpred]
            exact hb x hx y hyT hyx.symm
        _ = (T.card - 1) * b := by
            rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hx]
    rw [hdiag]
    exact Nat.add_le_add_left hoff P.card
  calc ∑ x ∈ T, ∑ y ∈ T,
        (P.filter fun p : ℕ => ((y : ZMod p) = (x : ZMod p))).card
      ≤ ∑ _x ∈ T, (P.card + (T.card - 1) * b) := Finset.sum_le_sum hxbound
    _ = T.card * P.card + T.card * ((T.card - 1) * b) := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_add]

/-- **Average collision bound** (paper `lem:average-collision`,
eq. `average-collision`), decoupled integer form: let `T ⊂ ℤ` be finite and
nonempty with `s = |T|`, and let `P` be a nonempty finite set of moduli such
that every nonzero difference of two elements of `T` is divisible by at most
`b` of them. Then
`∑_{p ∈ P} log |T mod p| ≥ |P| · [log s − log(1 + b(s−1)/|P|)]`.

The paper's `T ⊂ ℚ` and its scaling by `L(T)` are handled at the application
site (this `T` is the paper's integer set `L(T)·T`). The paper's hypothesis
that the moduli are primes not dividing `L(T)` is only needed for that
`ℚ → ℤ` transfer, not for the counting argument, so it does not appear here. -/
theorem average_collision_bound
    (T : Finset ℤ) (hT : T.Nonempty) (P : Finset ℕ) (hP : P.Nonempty) (b : ℕ)
    (hb : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      (P.filter fun p : ℕ => (p : ℤ) ∣ (x - y)).card ≤ b) :
    (P.card : ℝ) * (Real.log T.card
        - Real.log (1 + (b : ℝ) * ((T.card : ℝ) - 1) / (P.card : ℝ)))
      ≤ ∑ p ∈ P, Real.log ((T.image fun x : ℤ => (x : ZMod p)).card) := by
  classical
  have hs1 : 0 < T.card := Finset.card_pos.mpr hT
  have hs1' : 1 ≤ T.card := hs1
  have hsR : (1 : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hs1
  have hPpos : (0 : ℝ) < (P.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hP
  have hEpos : ∀ p ∈ P, (0 : ℝ) < (orderedCollisionCount T p : ℝ) := by
    intro p _
    have h := lt_of_lt_of_le hs1 (card_le_orderedCollisionCount T p)
    exact_mod_cast h
  have hEgeS : ∀ p ∈ P, (T.card : ℝ) ≤ (orderedCollisionCount T p : ℝ) := by
    intro p _
    exact_mod_cast card_le_orderedCollisionCount T p
  -- Step 1 (Cauchy–Schwarz per modulus, in log form):
  -- `log |T mod p| ≥ 2 log s − log E_p`.
  have hkey : ∀ p ∈ P,
      2 * Real.log T.card - Real.log (orderedCollisionCount T p)
        ≤ Real.log ((T.image fun x : ℤ => (x : ZMod p)).card) := by
    intro p hp
    have hcs : ((T.card : ℝ)) ^ 2
        ≤ ((T.image fun x : ℤ => (x : ZMod p)).card : ℝ)
          * (orderedCollisionCount T p : ℝ) := by
      exact_mod_cast sq_card_le_card_image_mul_orderedCollisionCount T p
    have hspos : (0 : ℝ) < (T.card : ℝ) := by linarith
    have hqpos : (0 : ℝ)
        < ((T.card : ℝ)) ^ 2 / (orderedCollisionCount T p : ℝ) :=
      div_pos (by positivity) (hEpos p hp)
    have hdle : ((T.card : ℝ)) ^ 2 / (orderedCollisionCount T p : ℝ)
        ≤ ((T.image fun x : ℤ => (x : ZMod p)).card : ℝ) :=
      (div_le_iff₀ (hEpos p hp)).mpr hcs
    have hlog := Real.log_le_log hqpos hdle
    rw [Real.log_div (by positivity) (ne_of_gt (hEpos p hp)),
      Real.log_pow] at hlog
    push_cast at hlog
    linarith
  -- Sum Step 1 over the moduli.
  have hsum1 : (P.card : ℝ) * (2 * Real.log T.card)
      - ∑ p ∈ P, Real.log (orderedCollisionCount T p)
      ≤ ∑ p ∈ P, Real.log ((T.image fun x : ℤ => (x : ZMod p)).card) := by
    have h := Finset.sum_le_sum hkey
    rwa [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
  -- Step 2 (Jensen for `log`, via the tangent line at the mean `M`):
  -- `∑_p log E_p ≤ |P| · log M` where `M = (∑_p E_p)/|P|`.
  set M : ℝ := (∑ p ∈ P, (orderedCollisionCount T p : ℝ)) / P.card with hM
  have hPM : (P.card : ℝ) * M = ∑ p ∈ P, (orderedCollisionCount T p : ℝ) := by
    rw [hM]
    field_simp
  have hMS : (T.card : ℝ) ≤ M := by
    rw [hM, le_div_iff₀ hPpos]
    calc (T.card : ℝ) * (P.card : ℝ) = ∑ _p ∈ P, (T.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ p ∈ P, (orderedCollisionCount T p : ℝ) := Finset.sum_le_sum hEgeS
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (by linarith) hMS
  have hjensen : ∑ p ∈ P, Real.log (orderedCollisionCount T p)
      ≤ (P.card : ℝ) * Real.log M := by
    have hterm : ∀ p ∈ P, Real.log (orderedCollisionCount T p)
        ≤ Real.log M + ((orderedCollisionCount T p : ℝ) - M) / M := by
      intro p hp
      have h := Real.log_le_sub_one_of_pos (div_pos (hEpos p hp) hMpos)
      rw [Real.log_div (ne_of_gt (hEpos p hp)) (ne_of_gt hMpos)] at h
      have h2 : ((orderedCollisionCount T p : ℝ) - M) / M
          = (orderedCollisionCount T p : ℝ) / M - 1 := by
        field_simp
      linarith
    have hsum := Finset.sum_le_sum hterm
    have hzero : ∑ p ∈ P, (((orderedCollisionCount T p : ℝ) - M) / M) = 0 := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, ← hPM]
      simp
    rwa [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hzero,
      add_zero] at hsum
  -- Step 3: bound the mean, `M ≤ s · (1 + b(s−1)/|P|)`.
  have hb1 : (0 : ℝ) ≤ (b : ℝ) * ((T.card : ℝ) - 1) / (P.card : ℝ) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg b) (by linarith)) hPpos.le
  have hMle : M ≤ (T.card : ℝ)
      * (1 + (b : ℝ) * ((T.card : ℝ) - 1) / (P.card : ℝ)) := by
    rw [hM, div_le_iff₀ hPpos]
    have h := sum_orderedCollisionCount_le T P b hb
    have h' : ((∑ p ∈ P, orderedCollisionCount T p : ℕ) : ℝ)
        ≤ ((T.card * P.card + T.card * ((T.card - 1) * b) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast [Nat.cast_sub hs1'] at h'
    have hexp : (T.card : ℝ)
        * (1 + (b : ℝ) * ((T.card : ℝ) - 1) / (P.card : ℝ)) * (P.card : ℝ)
        = (T.card : ℝ) * (P.card : ℝ)
          + (T.card : ℝ) * (((T.card : ℝ) - 1) * (b : ℝ)) := by
      field_simp
    rw [hexp]
    linarith
  have hCpos : (0 : ℝ)
      < 1 + (b : ℝ) * ((T.card : ℝ) - 1) / (P.card : ℝ) := by linarith
  have hlogM : Real.log M ≤ Real.log T.card
      + Real.log (1 + (b : ℝ) * ((T.card : ℝ) - 1) / (P.card : ℝ)) := by
    have h := Real.log_le_log hMpos hMle
    rwa [Real.log_mul (ne_of_gt (by linarith : (0 : ℝ) < (T.card : ℝ)))
      (ne_of_gt hCpos)] at h
  -- Assemble: `∑ log|T mod p| ≥ 2|P|log s − |P|log M ≥ |P|(log s − log C)`.
  have hmul := mul_le_mul_of_nonneg_left hlogM hPpos.le
  linarith

/-- The "In particular" clause of `lem:average-collision`: a nonzero integer
`z` with `|z| ≤ W` is divisible by at most `log W / log p₀` distinct primes
exceeding `p₀ > 1`. This is how the paper computes the admissible collision
multiplicity `b` (there stated as `b = ⌊log W(T) / log p₀⌋`; the real-valued
bound here implies the floored one since the left side is an integer). -/
theorem card_filter_dvd_le_of_abs_le
    (z : ℤ) (hz : z ≠ 0) (W : ℝ) (hW : |(z : ℝ)| ≤ W) (p0 : ℝ) (hp0 : 1 < p0)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hbig : ∀ p ∈ P, p0 < (p : ℝ)) :
    ((P.filter fun p : ℕ => (p : ℤ) ∣ z).card : ℝ)
      ≤ Real.log W / Real.log p0 := by
  classical
  set Q : Finset ℕ := P.filter fun p : ℕ => (p : ℤ) ∣ z with hQdef
  have hQsub : Q ⊆ P := Finset.filter_subset _ _
  have hQprime : ∀ p ∈ Q, Nat.Prime p := fun p hp => hprime p (hQsub hp)
  have hQdvd : ∀ p ∈ Q, (p : ℤ) ∣ z := fun p hp => by
    rw [hQdef] at hp
    exact (Finset.mem_filter.mp hp).2
  -- The distinct primes of `Q` are pairwise coprime, so their product
  -- divides `z` and is therefore at most `|z|`.
  have hcop : (↑Q : Set ℕ).Pairwise (IsCoprime on fun p : ℕ => (p : ℤ)) := by
    intro p hp q hq hpq
    exact Nat.Coprime.isCoprime
      ((Nat.coprime_primes (hQprime p hp) (hQprime q hq)).mpr hpq)
  have hproddvd : (∏ p ∈ Q, (p : ℤ)) ∣ z := Finset.prod_dvd_of_coprime hcop hQdvd
  have hprodle : (∏ p ∈ Q, (p : ℤ)) ≤ |z| :=
    Int.le_of_dvd (abs_pos.mpr hz) ((dvd_abs _ _).mpr hproddvd)
  have hp0pos : (0 : ℝ) < p0 := lt_trans one_pos hp0
  -- Each prime in `Q` exceeds `p0`, so `p0 ^ |Q| ≤ ∏ Q ≤ |z| ≤ W`.
  have hpowle : p0 ^ Q.card ≤ W := by
    have h1 : p0 ^ Q.card ≤ ∏ p ∈ Q, (p : ℝ) := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod (fun p _ => hp0pos.le)
        (fun p hp => (hbig p (hQsub hp)).le)
    have h2 : (∏ p ∈ Q, (p : ℝ)) ≤ |(z : ℝ)| := by
      calc ∏ p ∈ Q, (p : ℝ) = ((∏ p ∈ Q, (p : ℤ) : ℤ) : ℝ) := by push_cast; rfl
        _ ≤ ((|z| : ℤ) : ℝ) := by exact_mod_cast hprodle
        _ = |(z : ℝ)| := by push_cast; rfl
    linarith
  -- Take logarithms.
  have hlogp0pos : (0 : ℝ) < Real.log p0 := Real.log_pos hp0
  rw [le_div_iff₀ hlogp0pos]
  calc ((Q.card : ℕ) : ℝ) * Real.log p0 = Real.log (p0 ^ Q.card) := by
        rw [Real.log_pow]
    _ ≤ Real.log W := Real.log_le_log (pow_pos hp0pos _) hpowle

end Erdos320
