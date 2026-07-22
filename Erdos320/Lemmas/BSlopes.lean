import Erdos320.Lemmas.SBasic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Concavity and slopes of `𝓑` (paper `lem:B-slopes`)

The manuscript's Lemma "Concavity and slopes" (`lem:B-slopes`) asserts that
```
𝓑(X) = ∑_{m ≥ 1} min(g(m), X) / (m(m+1))
```
is increasing, concave, and locally absolutely continuous, with the
right-derivative identity `𝓑₊'(X) = 1/m_*(X)` for every `X ≥ 1`
(`eq:B-prime`; the ordinary derivative away from the breakpoints `X = g(m)`)
and the left slope `1/N` at the breakpoint `X = g(N)` (the right slope
`1/(N+1)` follows via `m_*(g(N)) = N+1`).

This file formalizes the lemma in the increment/chord form the downstream
arguments (`lem:exact-recurrence`, `lem:threshold`, `lem:breakpoint-chords`)
actually consume:

* `B_mono`, `B_lipschitz` — `𝓑` is increasing and `1`-Lipschitz;
* `B_sub_eq_tsum` — the exact termwise increment formula;
* `B_sub_le_div_mStar`, `B_sub_ge_of_g_le` — the chord
  bracket `(Y−X)/m_*(Y) ≤ 𝓑(Y) − 𝓑(X) ≤ (Y−X)/m_*(X)` (the paper's
  `𝓑' = 1/m_*` in integrated form; the lower bound is sharpened to `1/k`
  whenever `Y ≤ g(m)` for all `m ≥ k`);
* `B_chord_up`, `B_chord_down` — the one-sided breakpoint slopes `1/(N+1)`
  and `1/N` at `X = g(N)`, as chord inequalities (the paper states only the
  left slope explicitly; the right slope comes from `eq:B-prime`);
* `B_locally_affine`, `hasDerivAt_B` — away from the breakpoints, `𝓑` is
  locally affine with slope exactly `1/m_*(X)` (eq. `B-prime`);
* `breakpoints_countable` — the exceptional set `{X : ∃ m, g(m) = X}` is
  countable (the paper's "Away from the points `X = g(m)`" excludes only a
  countable set).

The engine is the paper's telescoping identity
`∑_{m ≥ k} 1/(m(m+1)) = 1/k`, formalized as `hasSum_weightTail` /
`tsum_weightTail` for the truncated weights `weightTail k`.
-/

namespace Erdos320

open Filter

/-! ## The truncated telescoping weights

The paper computes `𝓑'(X) = ∑_{g(m) > X} 1/(m(m+1))`, a *tail* of the weight
series, and telescopes it to `1/m_*(X)`.  We package the tail starting at
paper-index `k` (i.e. the terms with `m ≥ k`, in this file's shifted indexing
`m + 1 ≥ k`) as an explicitly truncated weight sequence. -/

/-- The weight `1/((m+1)(m+2))` of the `m`-th term of `𝓑` (paper index
`m + 1`), truncated to the tail `m + 1 ≥ k`: the terms whose paper index is
at least `k` keep their weight, all earlier terms get weight `0`.  This is
the summand of the paper's telescoping tail `∑_{m ≥ k} 1/(m(m+1))`
(`lem:B-slopes`). -/
noncomputable def weightTail (k m : ℕ) : ℝ :=
  if k ≤ m + 1 then 1 / ((m + 1 : ℝ) * (m + 2 : ℝ)) else 0

theorem weightTail_nonneg (k m : ℕ) : 0 ≤ weightTail k m := by
  rw [weightTail]
  split_ifs
  · positivity
  · exact le_rfl

theorem weightTail_le_weight (k m : ℕ) :
    weightTail k m ≤ 1 / ((m + 1 : ℝ) * (m + 2 : ℝ)) := by
  rw [weightTail]
  split_ifs
  · exact le_rfl
  · positivity

theorem summable_weightTail (k : ℕ) : Summable (weightTail k) :=
  Summable.of_nonneg_of_le (weightTail_nonneg k) (weightTail_le_weight k)
    summable_weight

/-- The paper's telescoping identity `∑_{m ≥ k} 1/(m(m+1)) = 1/k` for `k ≥ 1`
(`lem:B-slopes`: "the sum telescopes to `1/m_*(X)`"), in `HasSum` form for the
truncated weights. -/
theorem hasSum_weightTail {k : ℕ} (hk : 1 ≤ k) :
    HasSum (weightTail k) (1 / (k : ℝ)) := by
  rw [(summable_weightTail k).hasSum_iff_tendsto_nat]
  -- The telescoping comparison function: `f m = 1/(m+1)` past the truncation
  -- point, frozen at the initial value `1/k` before it.
  set f : ℕ → ℝ := fun m => if k ≤ m + 1 then 1 / (m + 1 : ℝ) else 1 / k with hf
  have hterm : ∀ m : ℕ, weightTail k m = f m - f (m + 1) := by
    intro m
    simp only [hf]
    rw [weightTail]
    push_cast
    split_ifs with h1 h2 h2
    · have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
      have hm2' : ((m : ℝ) + 1 + 1) ≠ 0 := by positivity
      field_simp
      ring
    · exact absurd (h1.trans (Nat.le_succ (m + 1))) h2
    · have hkm : k = m + 2 := by omega
      subst hkm
      push_cast
      ring
    · rw [sub_self]
  have hpartial : ∀ n : ℕ, ∑ m ∈ Finset.range n, weightTail k m = f 0 - f n := by
    intro n
    rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_range_sub' f n]
  have hf0 : f 0 = 1 / (k : ℝ) := by
    simp only [hf]
    split_ifs with h
    · have hk1 : k = 1 := by omega
      subst hk1
      norm_num
    · rfl
  have htendf : Tendsto f atTop (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop k] with n hn
    simp only [hf]
    rw [if_pos (by omega : k ≤ n + 1)]
  have hconst : Tendsto (fun n : ℕ => 1 / (k : ℝ) - f n) atTop
      (nhds (1 / (k : ℝ))) := by
    simpa using tendsto_const_nhds.sub htendf
  exact hconst.congr fun n => by rw [hpartial n, hf0]

/-- `∑_{m ≥ k} 1/(m(m+1)) = 1/k` for `k ≥ 1` (`lem:B-slopes`), in `tsum`
form. -/
theorem tsum_weightTail {k : ℕ} (hk : 1 ≤ k) :
    ∑' m : ℕ, weightTail k m = 1 / (k : ℝ) :=
  (hasSum_weightTail hk).tsum_eq

/-- The full weight series sums to `1` (the case `k = 1` of the telescoping
identity): `∑_{m ≥ 1} 1/(m(m+1)) = 1`.  This is what makes the weights of
`𝓑` a probability distribution and `𝓑` `1`-Lipschitz (`lem:B-slopes`). -/
theorem tsum_weight_eq_one :
    ∑' m : ℕ, 1 / ((m + 1 : ℝ) * (m + 2 : ℝ)) = 1 := by
  have h := tsum_weightTail (k := 1) le_rfl
  rw [Nat.cast_one, div_one] at h
  calc ∑' m : ℕ, 1 / ((m + 1 : ℝ) * (m + 2 : ℝ))
      = ∑' m : ℕ, weightTail 1 m :=
        tsum_congr fun m => by rw [weightTail, if_pos (Nat.le_add_left 1 m)]
    _ = 1 := h

/-! ## Monotonicity and the exact increment formula -/

/-- `𝓑` is increasing (`lem:B-slopes`: "The function `𝓑` is increasing"). -/
theorem B_mono : Monotone B := by
  intro X Y hXY
  refine Summable.tsum_le_tsum (fun m => ?_) (summable_BTerm X) (summable_BTerm Y)
  rw [BTerm, BTerm]
  exact div_le_div_of_nonneg_right (min_le_min le_rfl hXY) (by positivity)

/-- The exact termwise increment formula for `𝓑` (`lem:B-slopes`, the
workhorse behind "termwise differentiation in eq. `B-def`"): the increment of
`𝓑` is the weighted sum of the increments of the clamped terms
`min(g(m), ·)`.  No order hypothesis on `X`, `Y` is needed. -/
theorem B_sub_eq_tsum (X Y : ℝ) :
    B Y - B X
      = ∑' m : ℕ, (min (g (m + 1)) Y - min (g (m + 1)) X)
          / ((m + 1 : ℝ) * (m + 2 : ℝ)) := by
  rw [B, B, ← Summable.tsum_sub (summable_BTerm Y) (summable_BTerm X)]
  exact tsum_congr fun m => by rw [BTerm, BTerm, div_sub_div_same]

/-- The increment summand of `B_sub_eq_tsum` is summable (difference of two
summable clamped series). -/
theorem summable_min_sub_min_div (X Y : ℝ) :
    Summable fun m : ℕ =>
      (min (g (m + 1)) Y - min (g (m + 1)) X) / ((m + 1 : ℝ) * (m + 2 : ℝ)) := by
  refine ((summable_BTerm Y).sub (summable_BTerm X)).congr fun m => ?_
  rw [BTerm, BTerm, div_sub_div_same]

/-- `𝓑` is `1`-Lipschitz — the quantitative form of "locally absolutely
continuous" in `lem:B-slopes`: each term moves by at most
`|Y − X|/((m+1)(m+2))` and the weights sum to `1`
(`tsum_weight_eq_one`). -/
theorem B_lipschitz (X Y : ℝ) : |B Y - B X| ≤ |Y - X| := by
  have habs : ∀ m : ℕ,
      |(min (g (m + 1)) Y - min (g (m + 1)) X) / ((m + 1 : ℝ) * (m + 2 : ℝ))|
        ≤ |Y - X| * (1 / ((m + 1 : ℝ) * (m + 2 : ℝ))) := by
    intro m
    have hpos : (0 : ℝ) < (m + 1 : ℝ) * (m + 2 : ℝ) := by positivity
    rw [abs_div, abs_of_pos hpos, mul_one_div]
    refine div_le_div_of_nonneg_right ?_ hpos.le
    have h := abs_min_sub_min_le_max (g (m + 1)) Y (g (m + 1)) X
    rwa [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at h
  have hsum := summable_min_sub_min_div X Y
  rw [B_sub_eq_tsum]
  calc |∑' m : ℕ, (min (g (m + 1)) Y - min (g (m + 1)) X)
          / ((m + 1 : ℝ) * (m + 2 : ℝ))|
      ≤ ∑' m : ℕ, |(min (g (m + 1)) Y - min (g (m + 1)) X)
          / ((m + 1 : ℝ) * (m + 2 : ℝ))| := by
        have hnorm : Summable fun m : ℕ =>
            ‖(min (g (m + 1)) Y - min (g (m + 1)) X)
              / ((m + 1 : ℝ) * (m + 2 : ℝ))‖ := by
          simpa only [Real.norm_eq_abs] using hsum.abs
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, |Y - X| * (1 / ((m + 1 : ℝ) * (m + 2 : ℝ))) :=
        Summable.tsum_le_tsum habs hsum.abs (summable_weight.mul_left _)
    _ = |Y - X| * ∑' m : ℕ, 1 / ((m + 1 : ℝ) * (m + 2 : ℝ)) := tsum_mul_left
    _ = |Y - X| := by rw [tsum_weight_eq_one, mul_one]

/-! ## The chord bracket `(Y−X)/m_*(Y) ≤ 𝓑(Y) − 𝓑(X) ≤ (Y−X)/m_*(X)`

This is the integrated form of `𝓑'(X) = 1/m_*(X)` (eq. `B-prime` of
`lem:B-slopes`), the form consumed by `lem:exact-recurrence`,
`lem:threshold`, and `lem:breakpoint-chords`. -/

/-- Upper chord bound (`lem:B-slopes`, concavity side): for `0 ≤ X ≤ Y`,
`𝓑(Y) − 𝓑(X) ≤ (Y − X)/m_*(X)`.  Terms with paper index below `m_*(X)` are
clamped at `g(m) ≤ X` and do not move; the remaining tail moves by at most
`Y − X` per unit weight and telescopes to `1/m_*(X)`. -/
theorem B_sub_le_div_mStar {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) :
    B Y - B X ≤ (Y - X) / (mStar X : ℝ) := by
  have hYX : 0 ≤ Y - X := sub_nonneg.mpr hXY
  rw [B_sub_eq_tsum]
  have hle : ∀ m : ℕ,
      (min (g (m + 1)) Y - min (g (m + 1)) X) / ((m + 1 : ℝ) * (m + 2 : ℝ))
        ≤ (Y - X) * weightTail (mStar X) m := by
    intro m
    rw [weightTail]
    split_ifs with h
    · rw [mul_one_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have h0 := abs_min_sub_min_le_max (g (m + 1)) Y (g (m + 1)) X
      rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at h0
      calc min (g (m + 1)) Y - min (g (m + 1)) X
          ≤ |Y - X| := le_trans (le_abs_self _) h0
        _ = Y - X := abs_of_nonneg hYX
    · have hg : g (m + 1) ≤ X := g_le_of_lt_mStar (not_le.mp h)
      rw [min_eq_left hg, min_eq_left (hg.trans hXY), sub_self, zero_div,
        mul_zero]
  calc (∑' m : ℕ, (min (g (m + 1)) Y - min (g (m + 1)) X)
          / ((m + 1 : ℝ) * (m + 2 : ℝ)))
      ≤ ∑' m : ℕ, (Y - X) * weightTail (mStar X) m :=
        Summable.tsum_le_tsum hle (summable_min_sub_min_div X Y)
          ((summable_weightTail _).mul_left _)
    _ = (Y - X) * ∑' m : ℕ, weightTail (mStar X) m := tsum_mul_left
    _ = (Y - X) / (mStar X : ℝ) := by
        rw [tsum_weightTail (mStar_pos hX), mul_one_div]

/-- Sharpened lower chord bound (`lem:B-slopes`, used for the *left* slope
at a breakpoint): if every `g(m)` with paper index `m ≥ k` is at least
`Y`, then all those terms move in full and
`(Y − X)/k ≤ 𝓑(Y) − 𝓑(X)`. -/
theorem B_sub_ge_of_g_le {X Y : ℝ} {k : ℕ} (hk : 1 ≤ k) (hXY : X ≤ Y)
    (hgY : ∀ m, k ≤ m → Y ≤ g m) :
    (Y - X) / (k : ℝ) ≤ B Y - B X := by
  rw [B_sub_eq_tsum]
  have hge : ∀ m : ℕ, (Y - X) * weightTail k m
      ≤ (min (g (m + 1)) Y - min (g (m + 1)) X)
          / ((m + 1 : ℝ) * (m + 2 : ℝ)) := by
    intro m
    rw [weightTail]
    split_ifs with h
    · have hYg : Y ≤ g (m + 1) := hgY (m + 1) h
      rw [min_eq_right hYg, min_eq_right (hXY.trans hYg), mul_one_div]
    · rw [mul_zero]
      exact div_nonneg (sub_nonneg.mpr (min_le_min le_rfl hXY)) (by positivity)
  calc (Y - X) / (k : ℝ)
      = (Y - X) * ∑' m : ℕ, weightTail k m := by
        rw [tsum_weightTail hk, mul_one_div]
    _ = ∑' m : ℕ, (Y - X) * weightTail k m := tsum_mul_left.symm
    _ ≤ ∑' m : ℕ, (min (g (m + 1)) Y - min (g (m + 1)) X)
          / ((m + 1 : ℝ) * (m + 2 : ℝ)) :=
        Summable.tsum_le_tsum hge ((summable_weightTail k).mul_left _)
          (summable_min_sub_min_div X Y)

/-! ## Breakpoint chords: the one-sided slopes `1/(N+1)` and `1/N` at `X = g(N)`

`lem:B-slopes`: "At every breakpoint `X = g(N) ≥ 1` the left derivative is `1/N`."
The right slope `1/(N+1)` is `eq:B-prime` at `X = g(N)` (`m_*(g(N)) = N+1`).
Here in the chord form consumed by `lem:breakpoint-chords`. -/

/-- Right (up) chord at the breakpoint `X = g(N)`: the slope just above a
breakpoint is at most `1/(N+1)` (`eq:B-prime` right derivative at
`X = g(N)`), because `m_*(g(N)) = N + 1`. -/
theorem B_chord_up (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    B (g N + δ) - B (g N) ≤ δ / ((N : ℝ) + 1) := by
  have h := B_sub_le_div_mStar (g_nonneg N) (le_add_of_nonneg_right hδ)
  rw [mStar_g, add_sub_cancel_left] at h
  exact_mod_cast h

/-- Left (down) chord at the breakpoint `X = g(N)`: the slope just below a
breakpoint is at least `1/N` (`lem:B-slopes`, left derivative), because every
`g(m)` with `m ≥ N` is at least `g(N)`, so all those terms move in full. -/
theorem B_chord_down (N : ℕ) (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 ≤ δ) :
    δ / (N : ℝ) ≤ B (g N) - B (g N - δ) := by
  have h := B_sub_ge_of_g_le hN (sub_le_self (g N) hδ) fun _ hm => g_mono hm
  rwa [sub_sub_cancel] at h

/-! ## Local affineness and the derivative away from breakpoints -/

/-- Away from the breakpoints, `𝓑` is locally *affine* with slope exactly
`1/m_*(X)` (eq. `B-prime` of `lem:B-slopes`, in exact local form, consumed by
`lem:exact-recurrence`): on a small interval around a non-breakpoint `X > 0`,
every clamped term `min(g(m), ·)` is either frozen (paper index `< m_*(X)`)
or moves linearly (paper index `≥ m_*(X)`). -/
theorem B_locally_affine {X : ℝ} (h0 : 0 < X) (hgX : ∀ m, g m ≠ X) :
    ∃ ε > 0, ∀ Y ∈ Set.Ioo (X - ε) (X + ε),
      B Y - B X = (Y - X) / (mStar X : ℝ) := by
  have hk1 : 1 ≤ mStar X := mStar_pos h0.le
  have hlow : g (mStar X - 1) < X :=
    lt_of_le_of_ne (g_mStar_sub_one_le h0.le) (hgX _)
  have hhigh : X < g (mStar X) := lt_g_mStar X
  refine ⟨min (X - g (mStar X - 1)) (g (mStar X) - X),
    lt_min (by linarith) (by linarith), fun Y hY => ?_⟩
  obtain ⟨hY1, hY2⟩ := Set.mem_Ioo.mp hY
  have hεl : min (X - g (mStar X - 1)) (g (mStar X) - X)
      ≤ X - g (mStar X - 1) := min_le_left _ _
  have hεr : min (X - g (mStar X - 1)) (g (mStar X) - X)
      ≤ g (mStar X) - X := min_le_right _ _
  have hgm1Y : g (mStar X - 1) < Y := by linarith
  have hYg : Y < g (mStar X) := by linarith
  rw [B_sub_eq_tsum]
  have hterm : ∀ m : ℕ,
      (min (g (m + 1)) Y - min (g (m + 1)) X) / ((m + 1 : ℝ) * (m + 2 : ℝ))
        = (Y - X) * weightTail (mStar X) m := by
    intro m
    rw [weightTail]
    split_ifs with h
    · have hg : g (mStar X) ≤ g (m + 1) := g_mono h
      rw [min_eq_right (hYg.le.trans hg), min_eq_right (hhigh.le.trans hg),
        mul_one_div]
    · have hle : m + 1 ≤ mStar X - 1 := by omega
      have hg : g (m + 1) ≤ g (mStar X - 1) := g_mono hle
      rw [min_eq_left (hg.trans hgm1Y.le), min_eq_left (hg.trans hlow.le),
        sub_self, zero_div, mul_zero]
  rw [tsum_congr hterm, tsum_mul_left, tsum_weightTail hk1, mul_one_div]

/-- Eq. `B-prime` of `lem:B-slopes`: except at the breakpoints `X = g(m)`,
`𝓑` is differentiable with `𝓑'(X) = 1/m_*(X)`. -/
theorem hasDerivAt_B {X : ℝ} (h0 : 0 < X) (hgX : ∀ m, g m ≠ X) :
    HasDerivAt B (1 / (mStar X : ℝ)) X := by
  obtain ⟨ε, hε, haff⟩ := B_locally_affine h0 hgX
  have haffine : HasDerivAt (fun Y : ℝ => B X + (Y - X) / (mStar X : ℝ))
      (1 / (mStar X : ℝ)) X :=
    (((hasDerivAt_id X).sub_const X).div_const (mStar X : ℝ)).const_add (B X)
  refine haffine.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (by linarith : X - ε < X)
    (by linarith : X < X + ε)] with Y hY
  have h := haff Y hY
  linarith

/-- The exceptional set of `lem:B-slopes` ("Away from the points `X = g(m)`")
is countable: it is the range of `g`. -/
theorem breakpoints_countable : Set.Countable {X : ℝ | ∃ m, g m = X} :=
  Set.countable_range g

end Erdos320
