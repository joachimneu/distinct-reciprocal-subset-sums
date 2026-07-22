-- Import only the Mathlib modules actually used, not all of `Mathlib`: loading
-- the whole library on every compile is what makes builds take minutes. Keep
-- this list minimal so type-checking a touched file stays fast.
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Erdős Problem #320 — the number of distinct reciprocal subset sums

This file fixes the load-bearing definitions for the formalization. For a
positive integer `N`,
```
𝓔_N = { ∑_{n ∈ A} 1/n : A ⊆ {1, …, N} },   S(N) = |𝓔_N|,
```
i.e. `𝓔_N` is the set of distinct-denominator Egyptian fractions whose
denominators are at most `N` (together with the empty sum `0`), and `S(N)` is
how many distinct such rationals there are.

The manuscript being formalized proves a
full asymptotic for `log S(N)` with a positive, continuous, **nonconstant**
iterated-logarithmic phase `Φ`. That asymptotic — the paper's `thm:main` — is
stated and proved in `Erdos320/Main.lean` (`erdos320_theorem_1_1`); it is
deliberately not stated here, since stating it faithfully requires the
iterated logarithm `log_j`, the phase `Φ`, and the `o(1/log₃ N)` uniformity
built in later files. This file provides only the definitions and honestly
proven basic facts below.

Everything here matches the manuscript's conventions, including the empty-sum
convention `S(0) = 1`.
-/

namespace Erdos320

open Finset

/-- `reciprocalSubsetSumSet N` is the finite set
`𝓔_N = { ∑_{n ∈ A} 1/n : A ⊆ {1, …, N} } ⊆ ℚ` of distinct reciprocal subset
sums whose denominators lie in `{1, …, N}`. The empty subset contributes the
sum `0`. -/
def reciprocalSubsetSumSet (N : ℕ) : Finset ℚ :=
  (Icc 1 N).powerset.image fun (A : Finset ℕ) => ∑ n ∈ A, (1 : ℚ) / (n : ℚ)

/-- `S N` is the paper's counting function `S(N) = |𝓔_N|` (`eq:EN-SN-intro`):
the number of distinct reciprocal subset sums with denominators at most `N`. -/
def S (N : ℕ) : ℕ := (reciprocalSubsetSumSet N).card

/-- The empty subset witnesses that the sum `0` is always a reciprocal subset
sum. -/
theorem zero_mem_reciprocalSubsetSumSet (N : ℕ) :
    (0 : ℚ) ∈ reciprocalSubsetSumSet N := by
  simp only [reciprocalSubsetSumSet, mem_image]
  exact ⟨∅, empty_mem_powerset _, by simp⟩

theorem reciprocalSubsetSumSet_nonempty (N : ℕ) :
    (reciprocalSubsetSumSet N).Nonempty :=
  ⟨0, zero_mem_reciprocalSubsetSumSet N⟩

/-- There is always at least one reciprocal subset sum (the empty sum `0`), so
`S N ≥ 1`. In particular `S` never vanishes, matching `S(0) = 1`. -/
theorem one_le_S (N : ℕ) : 1 ≤ S N :=
  card_pos.mpr (reciprocalSubsetSumSet_nonempty N)

/-- The empty-sum convention: `S(0) = 1`, since the only subset of the empty
denominator range is `∅`, whose sum is `0`. -/
theorem S_zero : S 0 = 1 := by
  have hset : reciprocalSubsetSumSet 0 = {0} := by
    have hIcc : Icc 1 0 = (∅ : Finset ℕ) := by decide
    simp only [reciprocalSubsetSumSet, hIcc, powerset_empty, image_singleton,
      sum_empty]
  show (reciprocalSubsetSumSet 0).card = 1
  rw [hset, card_singleton]

/-- Enlarging the denominator range can only add reciprocal subset sums. -/
theorem reciprocalSubsetSumSet_subset_of_le {M N : ℕ} (h : M ≤ N) :
    reciprocalSubsetSumSet M ⊆ reciprocalSubsetSumSet N :=
  image_subset_image (powerset_mono.mpr (Icc_subset_Icc_right h))

/-- `S` is monotone: more available denominators cannot decrease the count of
distinct reciprocal subset sums. -/
theorem S_mono : Monotone S := fun _ _ h =>
  card_le_card (reciprocalSubsetSumSet_subset_of_le h)

/-- The normalized logarithmic count `F(N) = (log N / N) · log S(N)` that the
manuscript's certificates work with. (For `N = 0` this is `0`, since
`Real.log 0 = 0` in Mathlib; the certificates only use `N ≥ 1`.) -/
noncomputable def F (N : ℕ) : ℝ := (Real.log N / N) * Real.log (S N)

end Erdos320
