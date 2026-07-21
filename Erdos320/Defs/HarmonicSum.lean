import Erdos320.Defs.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The harmonic sum `H_N` as the maximal reciprocal subset sum

`H_N = ∑_{n≤N} 1/n` (a rational here, since the manuscript's subset sums are
exact rationals).  It is the largest element of `𝓔_N`, which is what makes
`S` strictly increasing (`H_N ∈ 𝓔_N \ 𝓔_{N-1}`) and bounds every fibre of
the large-prime decomposition (`prop:large-prime-decomposition`).
-/

namespace Erdos320

open Finset

/-- `harmonicSum N = H_N = ∑_{n=1}^N 1/n : ℚ`, the full reciprocal sum.  This is
Mathlib's `harmonic N` (see `harmonicSum_eq_sum_Icc` for the paper's `∑ 1/n`
form); we keep the paper-facing name `H_N` rather than re-deriving the object. -/
def harmonicSum (N : ℕ) : ℚ := harmonic N

/-- `harmonicSum` in the paper's explicit form `∑_{n=1}^N 1/n` (Mathlib's
`harmonic` is indexed by `(↑n)⁻¹`; here we spell it as `1/n`). -/
theorem harmonicSum_eq_sum_Icc (N : ℕ) :
    harmonicSum N = ∑ n ∈ Icc 1 N, (1 : ℚ) / n := by
  rw [harmonicSum, harmonic_eq_sum_Icc]
  exact Finset.sum_congr rfl fun n _ => (one_div (n : ℚ)).symm

/-- `H_N` is itself a reciprocal subset sum (take `A = {1,…,N}`). -/
theorem harmonicSum_mem_reciprocalSubsetSumSet (N : ℕ) :
    harmonicSum N ∈ reciprocalSubsetSumSet N := by
  simp only [reciprocalSubsetSumSet, mem_image]
  exact ⟨Icc 1 N, mem_powerset_self _, (harmonicSum_eq_sum_Icc N).symm⟩

/-- Every reciprocal subset sum with denominators `≤ N` is between `0`
and `H_N`. -/
theorem mem_reciprocalSubsetSumSet_bounds {N : ℕ} {x : ℚ}
    (hx : x ∈ reciprocalSubsetSumSet N) : 0 ≤ x ∧ x ≤ harmonicSum N := by
  simp only [reciprocalSubsetSumSet, mem_image] at hx
  obtain ⟨A, hA, rfl⟩ := hx
  rw [mem_powerset] at hA
  rw [harmonicSum_eq_sum_Icc]
  constructor
  · exact Finset.sum_nonneg fun n _ => by positivity
  · apply Finset.sum_le_sum_of_subset_of_nonneg hA
    intro n _ _
    positivity

end Erdos320
