import Erdos320.Defs.HarmonicSum
import Erdos320.Defs.LogCount
import Erdos320.Defs.Averaging

/-!
# Elementary facts about `S`, `g`, and the threshold index `m_*`

The manuscript's elementary toolkit for the counting function
`S(N) = |𝓔_N|` and its logarithm `g(N) = log S(N)`:

* strict monotonicity of `S` and `g` (paper §4, after eq. `B-def`:
  "`g` is strictly increasing: `H_N ∈ 𝓔_N` but `H_N ∉ 𝓔_{N-1}`");
* the trivial bounds `N + 1 ≤ S(N) ≤ 2^N`, hence
  `log(N+1) ≤ g(N) ≤ N log 2` — the upper bound is the paper's ubiquitous
  "`g(m) ≤ m log 2`" (used in `lem:B-slopes`, `lem:elementary-threshold`,
  `lem:threshold`, …), and the lower bound makes `g` unbounded;
* the one-step doubling bound `S(N+1) ≤ 2·S(N)` (each subset of
  `{1,…,N+1}` either avoids `N+1` or contains it);
* the basic API for the threshold index
  `m_*(X) = min{m ≥ 1 : g(m) > X}` (eq. `threshold-index-def`), which is a
  `Nat.sInf` in `Erdos320/Defs/Averaging.lean`.  Unboundedness of `g` makes
  the defining set nonempty, and monotonicity of `g` makes the set upward
  closed, so the `sInf` characterizations below are clean; downstream files
  should use these lemmas rather than unfolding `mStar`.
-/

namespace Erdos320

open Finset

/-! ## The harmonic sum is strictly increasing -/

/-- `H_N` is strictly increasing in `N`: passing from `N` to `N + 1` adds the
positive term `1/(N+1)`.  This is the engine behind the paper's remark (§4)
that `g` is strictly increasing. -/
theorem harmonicSum_strictMono : StrictMono harmonicSum := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hstep : harmonicSum (n + 1) = harmonicSum n + 1 / ((n : ℚ) + 1) := by
    rw [harmonicSum_eq_sum_Icc, harmonicSum_eq_sum_Icc,
      Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]
    push_cast
    ring
  have hpos : (0 : ℚ) < 1 / ((n : ℚ) + 1) := by positivity
  rw [hstep]
  linarith

/-- `H_k ∈ 𝓔_N` whenever `k ≤ N` (take `A = {1,…,k} ⊆ {1,…,N}`). -/
theorem harmonicSum_mem_reciprocalSubsetSumSet_of_le {k N : ℕ} (h : k ≤ N) :
    harmonicSum k ∈ reciprocalSubsetSumSet N :=
  reciprocalSubsetSumSet_subset_of_le h (harmonicSum_mem_reciprocalSubsetSumSet k)

/-! ## Strict monotonicity and the trivial bounds for `S` -/

/-- `S N > 0` — convenience restatement of `one_le_S`. -/
theorem S_pos (N : ℕ) : 0 < S N := one_le_S N

/-- `S` is strictly increasing.  Paper §4 (after eq. `B-def`): "`g` is strictly
increasing: `H_N ∈ 𝓔_N` but `H_N ∉ 𝓔_{N-1}`" — here in the equivalent
successor form: `𝓔_N ⊊ 𝓔_{N+1}` because `H_{N+1} ∈ 𝓔_{N+1}` exceeds the
maximum `H_N` of `𝓔_N`. -/
theorem S_strictMono : StrictMono S := by
  apply strictMono_nat_of_lt_succ
  intro n
  apply Finset.card_lt_card
  rw [Finset.ssubset_def]
  refine ⟨reciprocalSubsetSumSet_subset_of_le (Nat.le_succ n), fun hsub => ?_⟩
  have hmem : harmonicSum (n + 1) ∈ reciprocalSubsetSumSet n :=
    hsub (harmonicSum_mem_reciprocalSubsetSumSet (n + 1))
  have hle := (mem_reciprocalSubsetSumSet_bounds hmem).2
  exact absurd hle (not_le.mpr (harmonicSum_strictMono (Nat.lt_succ_self n)))

/-- The trivial upper bound `S(N) ≤ 2^N`: `𝓔_N` is the image of the `2^N`
formal subset sums (paper §1: "There are `2^N` formal subset sums, but many
collide"). -/
theorem S_le_two_pow (N : ℕ) : S N ≤ 2 ^ N := by
  calc S N ≤ (Icc 1 N).powerset.card := Finset.card_image_le
    _ = 2 ^ N := by rw [Finset.card_powerset, Nat.card_Icc, Nat.add_sub_cancel]

/-- The one-step doubling bound `S(N+1) ≤ 2·S(N)`: every subset of
`{1,…,N+1}` either avoids `N+1` (contributing an element of `𝓔_N`) or
contains it (contributing an element of `𝓔_N` shifted by `1/(N+1)`).  This is
the subadditivity behind the paper's `g(m) ≤ m log 2` bookkeeping. -/
theorem S_succ_le_two_mul (N : ℕ) : S (N + 1) ≤ 2 * S N := by
  have hsub : reciprocalSubsetSumSet (N + 1) ⊆
      reciprocalSubsetSumSet N ∪
        (reciprocalSubsetSumSet N).image
          (fun x : ℚ => x + 1 / ((N + 1 : ℕ) : ℚ)) := by
    intro x hx
    simp only [reciprocalSubsetSumSet, Finset.mem_image, Finset.mem_powerset] at hx
    obtain ⟨A, hA, rfl⟩ := hx
    by_cases hNmem : N + 1 ∈ A
    · -- `A` contains `N+1`: split off the last term.
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨∑ n ∈ A.erase (N + 1), (1 : ℚ) / n, ?_, ?_⟩
      · simp only [reciprocalSubsetSumSet, Finset.mem_image, Finset.mem_powerset]
        refine ⟨A.erase (N + 1), ?_, rfl⟩
        intro a ha
        have haA := hA (Finset.mem_of_mem_erase ha)
        have hane := Finset.ne_of_mem_erase ha
        rw [Finset.mem_Icc] at haA ⊢
        omega
      · exact Finset.sum_erase_add A _ hNmem
    · -- `A` avoids `N+1`, so `A ⊆ {1,…,N}`.
      apply Finset.mem_union_left
      simp only [reciprocalSubsetSumSet, Finset.mem_image, Finset.mem_powerset]
      refine ⟨A, ?_, rfl⟩
      intro a ha
      have haA := hA ha
      have hane : a ≠ N + 1 := fun h => hNmem (h ▸ ha)
      rw [Finset.mem_Icc] at haA ⊢
      omega
  calc S (N + 1)
      ≤ (reciprocalSubsetSumSet N ∪
          (reciprocalSubsetSumSet N).image
            (fun x : ℚ => x + 1 / ((N + 1 : ℕ) : ℚ))).card :=
        Finset.card_le_card hsub
    _ ≤ (reciprocalSubsetSumSet N).card
          + ((reciprocalSubsetSumSet N).image
              (fun x : ℚ => x + 1 / ((N + 1 : ℕ) : ℚ))).card :=
        Finset.card_union_le _ _
    _ ≤ S N + S N := Nat.add_le_add le_rfl Finset.card_image_le
    _ = 2 * S N := (Nat.two_mul (S N)).symm

/-- The trivial lower bound `N + 1 ≤ S(N)`: the partial sums
`H_0 < H_1 < ⋯ < H_N` are `N + 1` distinct elements of `𝓔_N`.  This makes
`g` unbounded, which the paper uses implicitly whenever the threshold index
`m_*(X)` (eq. `threshold-index-def`) is asserted to exist. -/
theorem add_one_le_S (N : ℕ) : N + 1 ≤ S N := by
  have hsub : (Finset.range (N + 1)).image harmonicSum ⊆ reciprocalSubsetSumSet N := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact harmonicSum_mem_reciprocalSubsetSumSet_of_le (Nat.lt_succ_iff.mp hk)
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ harmonicSum_strictMono.injective,
    Finset.card_range] at hcard

/-! ## Strict monotonicity and the trivial bounds for `g` -/

/-- `g` is strictly increasing (paper §4, after eq. `B-def`). -/
theorem g_strictMono : StrictMono g := fun M N h =>
  Real.log_lt_log (by exact_mod_cast one_le_S M) (by exact_mod_cast S_strictMono h)

/-- The paper's ubiquitous trivial bound `g(m) ≤ m log 2` (used in
`lem:B-slopes`, `lem:elementary-threshold`, `lem:threshold`, and the
certificate section), from `S(m) ≤ 2^m`. -/
theorem g_le_mul_log_two (m : ℕ) : g m ≤ m * Real.log 2 := by
  have hle : g m ≤ Real.log ((2 : ℝ) ^ m) :=
    Real.log_le_log (by exact_mod_cast one_le_S m)
      (by exact_mod_cast S_le_two_pow m)
  rwa [Real.log_pow] at hle

/-- The trivial logarithmic lower bound `log(N+1) ≤ g(N)`, from
`N + 1 ≤ S(N)`.  It shows `g` is unbounded. -/
theorem log_add_one_le_g (N : ℕ) : Real.log (N + 1) ≤ g N := by
  apply Real.log_le_log (by positivity)
  exact_mod_cast add_one_le_S N

/-- `g(N) → ∞`: the logarithmic count is unbounded (needed for the threshold
index `m_*` of eq. `threshold-index-def` to be well defined). -/
theorem g_tendsto_atTop : Filter.Tendsto g Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono log_add_one_le_g
  exact Real.tendsto_log_atTop.comp
    (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-- Every real threshold `X` is eventually exceeded by `g`: the defining set
of `m_*(X)` (eq. `threshold-index-def`) is nonempty. -/
theorem exists_g_gt (X : ℝ) : ∃ m, X < g m := by
  obtain ⟨m, hm⟩ := (g_tendsto_atTop.eventually_gt_atTop X).exists
  exact ⟨m, hm⟩

/-! ## API for the threshold index `m_*`

`mStar X = sInf {m | X < g m}` (eq. `threshold-index-def`).  The defining set
is nonempty (`exists_g_gt`) and upward closed (`g_mono`), so the `sInf` is a
genuine minimum with clean order characterizations. -/

/-- The threshold index does its job: `g(m_*(X)) > X`
(eq. `threshold-index-def`, existence direction). -/
theorem lt_g_mStar (X : ℝ) : X < g (mStar X) := by
  have hne : {m : ℕ | X < g m}.Nonempty := exists_g_gt X
  exact Nat.sInf_mem hne

/-- Minimality of the threshold index: below `m_*(X)` the count is still
`≤ X` (eq. `threshold-index-def`, minimality direction). -/
theorem g_le_of_lt_mStar {X : ℝ} {m : ℕ} (h : m < mStar X) : g m ≤ X := by
  by_contra hcon
  push Not at hcon
  exact absurd (Nat.sInf_le hcon) (not_le.mpr h)

/-- Any witness `X < g(m)` bounds the threshold index: `m_*(X) ≤ m`. -/
theorem mStar_le_of_lt_g {X : ℝ} {m : ℕ} (h : X < g m) : mStar X ≤ m :=
  Nat.sInf_le h

/-- `m < m_*(X) ↔ g(m) ≤ X`: the complete order characterization of `m_*`
from below (the defining set of eq. `threshold-index-def` is upward closed
because `g` is monotone). -/
theorem lt_mStar_iff {X : ℝ} {m : ℕ} : m < mStar X ↔ g m ≤ X := by
  constructor
  · exact g_le_of_lt_mStar
  · intro h
    by_contra hcon
    push Not at hcon
    exact absurd (le_trans (g_mono hcon) h) (not_le.mpr (lt_g_mStar X))

/-- `g(m) ≤ X` pushes the threshold index strictly past `m`. -/
theorem le_mStar_of_g_le {X : ℝ} {m : ℕ} (h : g m ≤ X) : m + 1 ≤ mStar X :=
  lt_mStar_iff.mpr h

/-- For `X ≥ 0` the threshold index is at least `1`, so the paper's `m ≥ 1`
constraint in eq. `threshold-index-def` is automatic (`g(0) = 0 ≤ X`
disqualifies `m = 0`). -/
theorem mStar_pos {X : ℝ} (hX : 0 ≤ X) : 0 < mStar X :=
  le_mStar_of_g_le (g_zero.le.trans hX)

/-- Just below the threshold index the count is still `≤ X`:
`g(m_*(X) − 1) ≤ X` (for `X ≥ 0`, so that `m_*(X) − 1` is a genuine
predecessor).  This is the bracketing `g(m_*−1) ≤ X < g(m_*)` the paper reads
off from eq. `threshold-index-def`. -/
theorem g_mStar_sub_one_le {X : ℝ} (hX : 0 ≤ X) : g (mStar X - 1) ≤ X :=
  g_le_of_lt_mStar (Nat.sub_lt (mStar_pos hX) one_pos)

/-- `m_*` is monotone in the threshold `X`. -/
theorem mStar_mono : Monotone mStar := fun _X Y h =>
  mStar_le_of_lt_g (lt_of_le_of_lt h (lt_g_mStar Y))

/-- At a breakpoint the threshold index steps: `m_*(g(N)) = N + 1`.  This is
the paper's picture of `𝓑` (`lem:B-slopes`, `eq:B-prime` right-derivative
form): at the breakpoint `X = g(N)`, `𝓑₊'(g(N)) = 1/m_*(g(N)) = 1/(N+1)`. -/
theorem mStar_g (N : ℕ) : mStar (g N) = N + 1 := by
  apply le_antisymm
  · exact mStar_le_of_lt_g (g_strictMono (Nat.lt_succ_self N))
  · exact le_mStar_of_g_le le_rfl

end Erdos320
