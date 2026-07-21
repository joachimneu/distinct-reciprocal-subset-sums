import Erdos320.Defs.StoppingDepth
import Erdos320.Lemmas.Phase
import Erdos320.Lemmas.IteratedExpBounds

/-!
# The stopping-depth bridge and the asymptotic half of `thm:main`

This file proves the *asymptotic* conjunct of the paper's main theorem
(`thm:main`, eq. `main`): with `h(N) = stoppingDepth N` and
`u_N = phaseCoordinate N`,
```
log S(N) = (N / log N) · (∏_{j=3}^{h(N)} log_j N) · Φ(u_N) · (1 + 1/log₃N + o(1/log₃N)),
```
with the `o(1/log₃N)` realized explicitly as `O(1/(log₃N · log₄N))`
(`main_asymptotic`), together with the paper's uniformity display
eq. `main-uniformity`, both in ε-form (`main_uniformity`) and as a
`Filter.Tendsto` over `atTop` (`main_uniformity_tendsto`).  The proof is the
paper's: instantiate `prop:phase` (`phase_asymptotic`) at `r = h(N)`,
`u = u_N`, so that `E_r(u) = N`, `D_r(u) = ∏_{j=3}^{h(N)} log_j N`,
`E_{r-3}(u) = log₃N`, and `F(N) = (log N / N)·log S(N)`.  The nonconstancy
conjunct of `thm:main` is handled elsewhere (`lem:breakpoint-chords` /
`prop:nonconstant`).

## Why `stoppingDepth` quantifies its predicate downward

Under Mathlib's junk convention `Real.log x = Real.log |x|` for `x < 0`
(`Real.log_neg_eq_log`), the naive predicate `1 ≤ iteratedLog j N` is *not*
downward closed and can resurrect at junk depths beyond the paper's `h(N)`
(numerically, e.g. `N = 10⁷` has `log₃N ≈ 1.022`, `log₄N ≈ 0.022`,
`log₅N ≈ −3.81`, `log₆N = log|log₅N| ≈ 1.337 ≥ 1`), with bad windows at
every scale — an unconditional `thm:main` over a `Nat.findGreatest` of that
predicate would be false.  `Defs/StoppingDepth.lean` therefore quantifies
the predicate downward (`∀ k ≤ j, 1 ≤ log_k N`), which matches the paper's
first-crossing depth exactly; `main_stoppingDepth_spec` below recovers the
downward property unconditionally (for `N ≥ 1`), so all theorems in this
file are unconditional.
-/

namespace Erdos320

/-! ## Composition and cancellation for iterated logarithms -/

/-- Splitting an iterated logarithm: `log_{a+b} x = log_a (log_b x)`. -/
theorem main_iteratedLog_add (a b : ℕ) (x : ℝ) :
    iteratedLog (a + b) x = iteratedLog a (iteratedLog b x) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show a + 1 + b = a + b + 1 by omega, iteratedLog_succ, ih,
      ← iteratedLog_succ]

/-- `E` inverts `iteratedLog` from the left, *provided all intermediate
iterates are positive* (with Mathlib's junk value `log x = log |x|` for
`x ≤ 0`, positivity of every intermediate iterate is genuinely needed):
`E_j(log_j x) = x`. -/
theorem main_E_iteratedLog_cancel {j : ℕ} {x : ℝ}
    (hpos : ∀ k < j, 0 < iteratedLog k x) :
    E j (iteratedLog j x) = x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj : 0 < iteratedLog j x := hpos j (Nat.lt_succ_self j)
    rw [iteratedLog_succ, ← E_comp j 1]
    show E j (Real.exp (E 0 (Real.log (iteratedLog j x)))) = x
    rw [E_zero, Real.exp_log hj]
    exact ih fun k hk => hpos k (hk.trans (Nat.lt_succ_self j))


/-- Partial cancellation: for `k ≤ j`, re-exponentiating the deep iterate
`log_j x` back up `j - k` times recovers the shallow iterate `log_k x`,
provided the iterates strictly between stay positive. -/
theorem main_iteratedLog_sub_cancel {j k : ℕ} {x : ℝ} (hkj : k ≤ j)
    (hpos : ∀ m, k ≤ m → m < j → 0 < iteratedLog m x) :
    E (j - k) (iteratedLog j x) = iteratedLog k x := by
  have hsplit : iteratedLog j x = iteratedLog (j - k) (iteratedLog k x) := by
    rw [← main_iteratedLog_add]
    congr 1
    omega
  rw [hsplit]
  exact main_E_iteratedLog_cancel fun m hm => by
    rw [← main_iteratedLog_add]
    exact hpos (m + k) (Nat.le_add_left k m) (by omega)

/-- If all iterated logarithms of `x` down to depth `j` are `≥ 1`, then
`x ≥ E_j(1)` (the quantitative content of "`log_j x ≥ 1` forces `x` huge"). -/
theorem main_E_le_of_forall_one_le_iteratedLog {j : ℕ} {x : ℝ}
    (h : ∀ k ≤ j, 1 ≤ iteratedLog k x) : E j 1 ≤ x := by
  have hcancel : E j (iteratedLog j x) = x :=
    main_E_iteratedLog_cancel fun k hk => lt_of_lt_of_le one_pos (h k hk.le)
  calc E j 1 ≤ E j (iteratedLog j x) := E_mono j (h j le_rfl)
    _ = x := hcancel

/-- Crude but explicit growth of the tower: `E_j(1) ≥ j + 1`. -/
theorem main_succ_le_E_one (j : ℕ) : (j : ℝ) + 1 ≤ E j 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := E_add_one_le_E_succ j 1
    push_cast
    linarith

/-- Monotone transfer *into* iterated logarithms: `E_j(c) ≤ x` forces
`c ≤ log_j x` (no positivity hypothesis on `c` is needed: the chain of
comparisons passes through genuine exponentials). -/
theorem main_le_iteratedLog_of_E_le (j : ℕ) {c x : ℝ} (h : E j c ≤ x) :
    c ≤ iteratedLog j x := by
  induction j generalizing x with
  | zero => exact h
  | succ j ih =>
    rw [iteratedLog_succ_outer]
    refine ih ?_
    have h' : Real.exp (E j c) ≤ x := by rw [← E_succ]; exact h
    have hlog := Real.log_le_log (Real.exp_pos _) h'
    rwa [Real.log_exp] at hlog

/-! ## Basic `stoppingDepth` facts -/

open Classical in
/-- **The defining property of the stopping depth, unconditionally** (for
`N ≥ 1`): every iterated logarithm down to depth `stoppingDepth N` is `≥ 1`.
This is `Nat.findGreatest_spec` anchored at depth `0`, where the
downward-quantified predicate reads `1 ≤ N`.  (With the downward-quantified
predicate of `Defs/StoppingDepth.lean` this needs no further hypothesis —
see the module docstring.) -/
theorem main_stoppingDepth_spec {N : ℕ} (hN : 1 ≤ N) :
    ∀ j ≤ stoppingDepth N, 1 ≤ iteratedLog j (N : ℝ) := by
  have h0 : ∀ k ≤ 0, (1 : ℝ) ≤ iteratedLog k (N : ℝ) := by
    intro k hk
    rw [Nat.le_zero.mp hk, iteratedLog_zero]
    exact_mod_cast hN
  unfold stoppingDepth
  exact Nat.findGreatest_spec
    (P := fun j => ∀ k ≤ j, (1 : ℝ) ≤ iteratedLog k (N : ℝ))
    (Nat.zero_le N) h0

/-- `1 ≤ u_N` for every `N ≥ 1`: the lower half of eq. `h-def-intro`'s
`u_N ∈ [1, e)`. -/
theorem main_one_le_phaseCoordinate {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ phaseCoordinate N :=
  main_stoppingDepth_spec hN (stoppingDepth N) le_rfl

/-- `stoppingDepth` is at least any depth `r ≤ N` at which the
downward-quantified predicate holds (`Nat.le_findGreatest`). -/
theorem main_le_stoppingDepth {N r : ℕ} (hrN : r ≤ N)
    (hr : ∀ k ≤ r, 1 ≤ iteratedLog k (N : ℝ)) : r ≤ stoppingDepth N := by
  unfold stoppingDepth
  exact Nat.le_findGreatest hrN hr

/-- Maximality of `stoppingDepth` (`Nat.findGreatest_is_greatest`): at every
depth strictly beyond it (within the search bound) some iterate drops
below `1`. -/
theorem main_not_forall_one_le_of_stoppingDepth_lt {N k : ℕ}
    (hk : stoppingDepth N < k) (hkN : k ≤ N) :
    ¬∀ m ≤ k, 1 ≤ iteratedLog m (N : ℝ) := by
  unfold stoppingDepth at hk
  exact Nat.findGreatest_is_greatest hk hkN

/-- **Largeness forces depth** (unconditional): `E_r(1) ≤ N` gives
`r ≤ stoppingDepth N`.  This is how theorems trade an explicit tower
threshold `N₀ = ⌈E_r(1)⌉` for a depth lower bound. -/
theorem main_stoppingDepth_ge {r N : ℕ} (hE : E r 1 ≤ (N : ℝ)) :
    r ≤ stoppingDepth N := by
  have h1 : ∀ k ≤ r, 1 ≤ iteratedLog k (N : ℝ) := fun k hk =>
    main_le_iteratedLog_of_E_le k (le_trans (E_mono_depth le_rfl hk) hE)
  have h2 := main_succ_le_E_one r
  have hrN : r ≤ N := by
    have h3 : (r : ℝ) < (N : ℝ) := by linarith
    exact_mod_cast h3.le
  exact main_le_stoppingDepth hrN h1

/-! ## The bridge -/

/-- **The stopping-depth bridge** (`thm:main`'s "`N = E_r(u)`" with
`r = h(N)`, `u = u_N`): re-exponentiating the phase coordinate recovers `N`
exactly. -/
theorem main_E_stoppingDepth {N : ℕ} (hN : 1 ≤ N) :
    E (stoppingDepth N) (phaseCoordinate N) = (N : ℝ) :=
  main_E_iteratedLog_cancel fun k hk =>
    lt_of_lt_of_le one_pos (main_stoppingDepth_spec hN k hk.le)

/-- `E_{h(N)-k}(u_N) = log_k N` for every `k ≤ h(N)` — in particular
(`thm:main`'s proof) `E_{h(N)-3}(u_N) = log₃N` (`k = 3`) and
`E_{h(N)-4}(u_N) = log₄N` (`k = 4`). -/
theorem main_E_sub_eq_iteratedLog {N : ℕ} (hN : 1 ≤ N) {k : ℕ}
    (hk : k ≤ stoppingDepth N) :
    E (stoppingDepth N - k) (phaseCoordinate N) = iteratedLog k (N : ℝ) :=
  main_iteratedLog_sub_cancel hk fun m _ hm =>
    lt_of_lt_of_le one_pos (main_stoppingDepth_spec hN m hm.le)

/-- The stopping depth sits strictly inside the `Nat.findGreatest` search
bound: `h(N) + 1 ≤ N` (because `N ≥ E_{h(N)}(1) ≥ h(N) + 1`), so maximality
genuinely applies at depth `h(N) + 1`. -/
theorem main_stoppingDepth_add_one_le {N : ℕ} (hN : 1 ≤ N) :
    stoppingDepth N + 1 ≤ N := by
  have h1 : E (stoppingDepth N) 1 ≤ (N : ℝ) :=
    main_E_le_of_forall_one_le_iteratedLog (main_stoppingDepth_spec hN)
  have h2 := main_succ_le_E_one (stoppingDepth N)
  have h3 : ((stoppingDepth N : ℝ)) + 1 ≤ (N : ℝ) := le_trans h2 h1
  exact_mod_cast h3

/-- The upper half of eq. `h-def-intro`'s `u_N ∈ [1, e)`: `u_N < e` for all
`N ≥ 1` (else `log u_N ≥ 1` would extend the downward-closed predicate to
depth `h(N) + 1`, contradicting maximality). -/
theorem main_phaseCoordinate_lt_exp_one {N : ℕ} (hN : 1 ≤ N) :
    phaseCoordinate N < Real.exp 1 := by
  rcases le_or_gt (Real.exp 1) (phaseCoordinate N) with h | h
  · exfalso
    have hspec := main_stoppingDepth_spec hN
    have hlog : 1 ≤ iteratedLog (stoppingDepth N + 1) (N : ℝ) := by
      rw [iteratedLog_succ]
      have h1 := Real.log_le_log (Real.exp_pos 1) h
      rwa [Real.log_exp] at h1
    have hall : ∀ m ≤ stoppingDepth N + 1, 1 ≤ iteratedLog m (N : ℝ) := by
      intro m hm
      rcases Nat.eq_or_lt_of_le hm with hm' | hm'
      · rw [hm']
        exact hlog
      · exact hspec m (by omega)
    exact main_not_forall_one_le_of_stoppingDepth_lt (Nat.lt_succ_self _)
      (main_stoppingDepth_add_one_le hN) hall
  · exact h

/-- The phase coordinate lies in the phase interval: `u_N ∈ [1, e]` (in fact
`u_N < e`), the membership required by `prop:phase`. -/
theorem main_phaseCoordinate_mem_Icc {N : ℕ} (hN : 1 ≤ N) :
    phaseCoordinate N ∈ Set.Icc (1 : ℝ) (Real.exp 1) :=
  ⟨main_one_le_phaseCoordinate hN, (main_phaseCoordinate_lt_exp_one hN).le⟩

/-- **The product bridge** (`thm:main`'s proof:
"`D_r(u) = ∏_{j=3}^{h(N)} log_j N`"): the normalizing product
`D_{h(N)}(u_N) = ∏_{j ∈ range(h(N)-2)} E_j(u_N)` is exactly the paper's
iterated-logarithm product, via the reindexing `j ↦ h(N) - j`. -/
theorem main_D_eq_prod_iteratedLog {N : ℕ} (hN : 1 ≤ N)
    (h3 : 3 ≤ stoppingDepth N) :
    D (stoppingDepth N) (phaseCoordinate N)
      = ∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ) := by
  unfold D
  refine Finset.prod_nbij' (fun j => stoppingDepth N - j)
    (fun m => stoppingDepth N - m) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Icc]
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_range]
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    have h := main_E_sub_eq_iteratedLog hN
      (k := stoppingDepth N - a) (Nat.sub_le _ _)
    rw [show stoppingDepth N - (stoppingDepth N - a) = a by omega] at h
    exact h

/-! ## Scaling helpers (pure real algebra) -/

/-- Scaling an absolute-value bound by the factor `M` when `M · W = 1`:
from `|W·g − X| ≤ Z` conclude `|g − M·X| ≤ M·Z`.  Used with
`M = N/log N`, `W = log N/N` to convert the `F(N)`-normalized `prop:phase`
bound into a bound on `log S(N)` itself. -/
theorem main_abs_mul_shift {g W X Z M : ℝ} (hM : 0 ≤ M) (hWM : M * W = 1)
    (h : |W * g - X| ≤ Z) : |g - M * X| ≤ M * Z := by
  have hg : g - M * X = M * (W * g - X) := by
    rw [mul_sub, ← mul_assoc, hWM, one_mul]
  rw [hg, abs_mul, abs_of_nonneg hM]
  exact mul_le_mul_of_nonneg_left h hM

/-- Normalized-error transfer (pure algebra behind eq. `main-uniformity`):
from the absolute bound `|g − M·(P·Φ·(1 + 1/a))| ≤ C·M·P/(a·b)` and
`C/(b·Φ) ≤ ε`, conclude `a·|g/(M·P·Φ) − 1 − 1/a| ≤ ε`. -/
theorem main_normalized_error_le {g M P Φ a b C ε : ℝ}
    (hM : 0 < M) (hP : 0 < P) (hΦ : 0 < Φ) (ha : 1 ≤ a) (hb : 0 < b)
    (hkey : |g - M * (P * Φ * (1 + 1 / a))| ≤ C * M * P / (a * b))
    (hbound : C / (b * Φ) ≤ ε) :
    a * |g / (M * P * Φ) - 1 - 1 / a| ≤ ε := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hT : 0 < M * P * Φ := mul_pos (mul_pos hM hP) hΦ
  have hquot : g / (M * P * Φ) - 1 - 1 / a
      = (g - M * (P * Φ * (1 + 1 / a))) / (M * P * Φ) := by
    field_simp
    ring
  rw [hquot, abs_div, abs_of_pos hT]
  calc a * (|g - M * (P * Φ * (1 + 1 / a))| / (M * P * Φ))
      ≤ a * (C * M * P / (a * b) / (M * P * Φ)) := by gcongr
    _ = C / (b * Φ) := by
        field_simp
    _ ≤ ε := hbound

/-! ## `thm:main`, asymptotic half -/

/-- **The asymptotic half of `thm:main` (eq. `main`), with explicit uniform
error** — the paper's `o(1/log₃N)` realized as `O(1/(log₃N·log₄N))`: there
are `C ≥ 0` and a threshold `N₀` (of tower shape `⌈E_{max(r₁,8)}(1)⌉`, where
`r₁` is the onset depth of `prop:phase`) such that for all `N ≥ N₀`,
```
|log S(N) − (N/log N)·(∏_{j=3}^{h(N)} log_j N)·Φ(u_N)·(1 + 1/log₃N)|
    ≤ C·(N/log N)·(∏_{j=3}^{h(N)} log_j N)/(log₃N·log₄N).
```
Proof: `prop:phase` (`phase_asymptotic`) at `r = h(N)`, `u = u_N`, using the
bridge `E_{h(N)}(u_N) = N`, `D_{h(N)}(u_N) = ∏_{j=3}^{h(N)} log_j N`,
`E_{h(N)-3}(u_N) = log₃N`, `E_{h(N)-4}(u_N) = log₄N`, and
`D_{r-2} = D_r/(E_{r-3}E_{r-4})` (`q_eq_D_ratio`), all scaled by
`N/log N > 0` via `F(N) = (log N/N)·log S(N)`. -/
theorem main_asymptotic :
    ∃ (C : ℝ) (N₀ : ℕ), 0 ≤ C ∧
      ∀ N : ℕ, N₀ ≤ N →
        |Real.log (S N)
            - ((N : ℝ) / Real.log N)
              * ((∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ))
                * phasePhi (phaseCoordinate N)
                * (1 + 1 / iteratedLog 3 (N : ℝ)))|
          ≤ C * ((N : ℝ) / Real.log N)
              * (∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ))
              / (iteratedLog 3 (N : ℝ) * iteratedLog 4 (N : ℝ)) := by
  obtain ⟨C, r₁, hC, hphase⟩ := phase_asymptotic
  refine ⟨C, ⌈E (max r₁ 8) 1⌉₊, hC, fun N hN => ?_⟩
  have hEN : E (max r₁ 8) 1 ≤ (N : ℝ) := Nat.ceil_le.mp hN
  -- size facts
  have h9 : (9 : ℝ) ≤ (N : ℝ) := by
    have hs := main_succ_le_E_one (max r₁ 8)
    have h8 : (8 : ℕ) ≤ max r₁ 8 := le_max_right _ _
    have h8' : (8 : ℝ) ≤ ((max r₁ 8 : ℕ) : ℝ) := by exact_mod_cast h8
    linarith
  have hN1 : 1 ≤ N := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast h1
  have hrbig : max r₁ 8 ≤ stoppingDepth N := main_stoppingDepth_ge hEN
  have hr8 : 8 ≤ stoppingDepth N := le_trans (le_max_right _ _) hrbig
  have hr₁ : r₁ ≤ stoppingDepth N := le_trans (le_max_left _ _) hrbig
  have huIcc : phaseCoordinate N ∈ Set.Icc (1 : ℝ) (Real.exp 1) :=
    main_phaseCoordinate_mem_Icc hN1
  have hu1 : (1 : ℝ) ≤ phaseCoordinate N := huIcc.1
  have hu0 : (0 : ℝ) < phaseCoordinate N := lt_of_lt_of_le one_pos hu1
  -- the bridge
  have hEr : E (stoppingDepth N) (phaseCoordinate N) = (N : ℝ) :=
    main_E_stoppingDepth hN1
  have hprod : D (stoppingDepth N) (phaseCoordinate N)
      = ∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ) :=
    main_D_eq_prod_iteratedLog hN1 (by omega)
  have h3 : E (stoppingDepth N - 3) (phaseCoordinate N)
      = iteratedLog 3 (N : ℝ) := main_E_sub_eq_iteratedLog hN1 (by omega)
  have h4 : E (stoppingDepth N - 4) (phaseCoordinate N)
      = iteratedLog 4 (N : ℝ) := main_E_sub_eq_iteratedLog hN1 (by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hnL : (0 : ℝ) < (N : ℝ) / Real.log (N : ℝ) := div_pos hNpos hlogN
  have hDr : (0 : ℝ) < D (stoppingDepth N) (phaseCoordinate N) := D_pos hu0 _
  -- prop:phase at (h(N), u_N), rewritten to N via the bridge
  have hkey := hphase (stoppingDepth N) hr₁ (phaseCoordinate N) huIcc
  have hFdef : F N = Real.log (N : ℝ) / (N : ℝ) * Real.log ((S N : ℝ)) := rfl
  rw [hEr, FReal_natCast, hFdef] at hkey
  -- error-scale identity: D_{r-2} = D_r / (E_{r-3}·E_{r-4})
  have hDq : D (stoppingDepth N) (phaseCoordinate N)
        * q (stoppingDepth N) (phaseCoordinate N)
      = D (stoppingDepth N - 2) (phaseCoordinate N) := by
    rw [q_eq_D_ratio hu0 (show 5 ≤ stoppingDepth N by omega), mul_comm,
      div_mul_cancel₀ _ hDr.ne']
  have hqdef : q (stoppingDepth N) (phaseCoordinate N)
      = 1 / (E (stoppingDepth N - 3) (phaseCoordinate N)
          * E (stoppingDepth N - 4) (phaseCoordinate N)) := rfl
  have hRHSeq : C * ((N : ℝ) / Real.log (N : ℝ))
        * D (stoppingDepth N) (phaseCoordinate N)
        / (E (stoppingDepth N - 3) (phaseCoordinate N)
          * E (stoppingDepth N - 4) (phaseCoordinate N))
      = ((N : ℝ) / Real.log (N : ℝ))
        * (C * D (stoppingDepth N - 2) (phaseCoordinate N)) := by
    rw [← hDq, hqdef]
    ring
  have hWM : ((N : ℝ) / Real.log (N : ℝ)) * (Real.log (N : ℝ) / (N : ℝ)) = 1 := by
    rw [div_mul_div_comm, mul_comm (N : ℝ) (Real.log (N : ℝ))]
    exact div_self (mul_ne_zero hlogN.ne' hNpos.ne')
  rw [← hprod, ← h3, ← h4, hRHSeq]
  exact main_abs_mul_shift hnL.le hWM hkey

/-! ## `thm:main`, the uniformity display eq. `main-uniformity` -/

/-- **Eq. `main-uniformity` of `thm:main` in ε-form**: for every `ε > 0`
there is a threshold `N₀` beyond which
```
log₃N · |log S(N)/(𝓜(N)·Φ(u_N)) − 1 − 1/log₃N| ≤ ε,
```
where `𝓜(N) = (N/log N)·∏_{j=3}^{h(N)} log_j N`.  (The paper's `limsup = 0`
display is the `Filter.Tendsto` phrasing of exactly this ε-statement; see
`main_uniformity_tendsto`.)  Proof: divide `main_asymptotic` by
`𝓜(N)·Φ(u_N) > 0`, bound `Φ(u_N)` below by the minimum of the continuous
positive `Φ` on the compact `[1, e]`, and let `log₄N → ∞`. -/
theorem main_uniformity {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      iteratedLog 3 (N : ℝ)
          * |Real.log (S N)
              / (((N : ℝ) / Real.log N)
                * (∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ))
                * phasePhi (phaseCoordinate N))
            - 1 - 1 / iteratedLog 3 (N : ℝ)|
        ≤ ε := by
  obtain ⟨C, N₀, -, hmain⟩ := main_asymptotic
  obtain ⟨u₀, hu₀mem, hu₀min⟩ :=
    (isCompact_Icc (a := (1 : ℝ)) (b := Real.exp 1)).exists_isMinOn
      (Set.nonempty_Icc.mpr (by linarith [Real.add_one_le_exp (1 : ℝ)]))
      phasePhi_continuousOn
  have hφ₀ : 0 < phasePhi u₀ := phasePhi_pos u₀ hu₀mem
  refine ⟨max N₀ ⌈E 4 (max 1 (C / (phasePhi u₀ * ε)))⌉₊, fun N hN => ?_⟩
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hE4N : E 4 (max 1 (C / (phasePhi u₀ * ε))) ≤ (N : ℝ) :=
    Nat.ceil_le.mp (le_trans (le_max_right _ _) hN)
  have hbK' : max 1 (C / (phasePhi u₀ * ε)) ≤ iteratedLog 4 (N : ℝ) :=
    main_le_iteratedLog_of_E_le 4 hE4N
  have hb1 : (1 : ℝ) ≤ iteratedLog 4 (N : ℝ) := le_trans (le_max_left _ _) hbK'
  have hb0 : (0 : ℝ) < iteratedLog 4 (N : ℝ) := lt_of_lt_of_le one_pos hb1
  have hbK : C / (phasePhi u₀ * ε) ≤ iteratedLog 4 (N : ℝ) :=
    le_trans (le_max_right _ _) hbK'
  -- size facts
  have h5 : (5 : ℝ) ≤ (N : ℝ) := by
    have h51 : (4 : ℝ) + 1 ≤ E 4 1 := by exact_mod_cast main_succ_le_E_one 4
    have h52 : E 4 1 ≤ E 4 (max 1 (C / (phasePhi u₀ * ε))) :=
      E_mono 4 (le_max_left _ _)
    linarith
  have hN1 : 1 ≤ N := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast h1
  -- bridge facts (positivity of the normalizer)
  have hsd3 : 3 ≤ stoppingDepth N :=
    main_stoppingDepth_ge (le_trans
      (le_trans (E_lt_E_succ 3 1).le (E_mono 4 (le_max_left _ _))) hE4N)
  have huIcc : phaseCoordinate N ∈ Set.Icc (1 : ℝ) (Real.exp 1) :=
    main_phaseCoordinate_mem_Icc hN1
  have hu1 : (1 : ℝ) ≤ phaseCoordinate N := huIcc.1
  have hu0 : (0 : ℝ) < phaseCoordinate N := lt_of_lt_of_le one_pos hu1
  have hΦu : 0 < phasePhi (phaseCoordinate N) := phasePhi_pos _ huIcc
  have hφ₀le : phasePhi u₀ ≤ phasePhi (phaseCoordinate N) :=
    (isMinOn_iff.mp hu₀min) _ huIcc
  have hprod : D (stoppingDepth N) (phaseCoordinate N)
      = ∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ) :=
    main_D_eq_prod_iteratedLog hN1 hsd3
  have hPpos : 0 < ∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ) := by
    rw [← hprod]
    exact D_pos hu0 _
  have h3 : E (stoppingDepth N - 3) (phaseCoordinate N)
      = iteratedLog 3 (N : ℝ) := main_E_sub_eq_iteratedLog hN1 hsd3
  have ha1 : (1 : ℝ) ≤ iteratedLog 3 (N : ℝ) := by
    rw [← h3]
    exact one_le_E_of_one_le hu1 _
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hnL : (0 : ℝ) < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (by linarith) hlogN
  -- the tail bound `C/(log₄N · Φ(u_N)) ≤ ε`
  have hbound : C / (iteratedLog 4 (N : ℝ) * phasePhi (phaseCoordinate N)) ≤ ε := by
    rw [div_le_iff₀ (mul_pos hb0 hΦu)]
    have hφε : (0 : ℝ) < phasePhi u₀ * ε := mul_pos hφ₀ hε
    have h1 : C ≤ iteratedLog 4 (N : ℝ) * (phasePhi u₀ * ε) := by
      have h2 := mul_le_mul_of_nonneg_right hbK hφε.le
      rwa [div_mul_cancel₀ _ hφε.ne'] at h2
    nlinarith [mul_nonneg (mul_nonneg hb0.le hε.le) (sub_nonneg.mpr hφ₀le)]
  exact main_normalized_error_le hnL hPpos hΦu ha1 hb0 (hmain N hN₀) hbound

/-- **Eq. `main-uniformity` of `thm:main`, `Tendsto` form**: the paper's
`limsup_{N ≥ T} → 0` display, phrased as convergence along `atTop` of the
`log₃N`-scaled normalized error.  Immediate from the ε-form
(`main_uniformity`) via `Metric.tendsto_atTop`, using `log₃N ≥ 1` (from
`N ≥ E₃(1)`) to drop the outer absolute value. -/
theorem main_uniformity_tendsto :
    Filter.Tendsto (fun N : ℕ =>
        iteratedLog 3 (N : ℝ)
          * |Real.log (S N)
              / (((N : ℝ) / Real.log N)
                * (∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ))
                * phasePhi (phaseCoordinate N))
            - 1 - 1 / iteratedLog 3 (N : ℝ)|)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := main_uniformity (half_pos hε)
  refine ⟨max N₀ ⌈E 3 1⌉₊, fun N hN => ?_⟩
  have h1 := hN₀ N (le_trans (le_max_left _ _) hN)
  have ha1 : (1 : ℝ) ≤ iteratedLog 3 (N : ℝ) :=
    main_le_iteratedLog_of_E_le 3
      (Nat.ceil_le.mp (le_trans (le_max_right _ _) hN))
  simp only [Real.dist_eq, sub_zero]
  rw [abs_of_nonneg (mul_nonneg (le_trans zero_le_one ha1) (abs_nonneg _))]
  exact lt_of_le_of_lt h1 (half_lt_self hε)

/-! ## `thm:main`, the normalized explicit-error display eq. `main-uniform-error` -/

/-- Normalized explicit-error transfer (pure algebra behind eq.
`main-uniform-error`): from the absolute bound
`|g − M·(P·Φ·(1 + 1/a))| ≤ C·M·P/(a·b)` and `C/Φ ≤ C'`, conclude
`|g/(M·P·Φ) − 1 − 1/a| ≤ C'/(a·b)`. -/
theorem main_uniform_error_transfer {g M P Φ a b C C' : ℝ}
    (hM : 0 < M) (hP : 0 < P) (hΦ : 0 < Φ) (ha : 0 < a) (hb : 0 < b)
    (hkey : |g - M * (P * Φ * (1 + 1 / a))| ≤ C * M * P / (a * b))
    (hbound : C / Φ ≤ C') :
    |g / (M * P * Φ) - 1 - 1 / a| ≤ C' / (a * b) := by
  have hT : 0 < M * P * Φ := mul_pos (mul_pos hM hP) hΦ
  have hquot : g / (M * P * Φ) - 1 - 1 / a
      = (g - M * (P * Φ * (1 + 1 / a))) / (M * P * Φ) := by
    field_simp
    ring
  rw [hquot, abs_div, abs_of_pos hT]
  calc |g - M * (P * Φ * (1 + 1 / a))| / (M * P * Φ)
      ≤ C * M * P / (a * b) / (M * P * Φ) := by gcongr
    _ = (C / Φ) / (a * b) := by field_simp
    _ ≤ C' / (a * b) := by gcongr

/-- **Eq. `main-uniform-error` of `thm:main`**: the paper's
*normalized* explicit-error display.  There are constants `C_asym > 0` and
`N_asym` such that for every integer `N ≥ N_asym`,
```
|log S(N)/(𝓜(N)·Φ(u_N)) − 1 − 1/log₃N| ≤ C_asym/(log₃N·log₄N),
```
where `𝓜(N) = (N/log N)·∏_{j=3}^{h(N)} log_j N`.  Proof: divide the absolute
bound `main_asymptotic` by `𝓜(N)·Φ(u_N) > 0` and bound `1/Φ(u_N)` above by
`1/Φ(u₀)`, where `Φ(u₀)` is the minimum of the continuous positive `Φ` on the
compact `[1, e]` (so `C_asym = C/Φ(u₀) + 1 > 0`). -/
theorem main_uniform_error :
    ∃ (C : ℝ) (N₀ : ℕ), 0 < C ∧
      ∀ N : ℕ, N₀ ≤ N →
        |Real.log (S N)
            / (((N : ℝ) / Real.log N)
              * (∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ))
              * phasePhi (phaseCoordinate N))
          - 1 - 1 / iteratedLog 3 (N : ℝ)|
        ≤ C / (iteratedLog 3 (N : ℝ) * iteratedLog 4 (N : ℝ)) := by
  obtain ⟨C, N₀, hC, hmain⟩ := main_asymptotic
  obtain ⟨u₀, hu₀mem, hu₀min⟩ :=
    (isCompact_Icc (a := (1 : ℝ)) (b := Real.exp 1)).exists_isMinOn
      (Set.nonempty_Icc.mpr (by linarith [Real.add_one_le_exp (1 : ℝ)]))
      phasePhi_continuousOn
  have hφ₀ : 0 < phasePhi u₀ := phasePhi_pos u₀ hu₀mem
  refine ⟨C / phasePhi u₀ + 1, max N₀ ⌈E 4 1⌉₊,
    add_pos_of_nonneg_of_pos (div_nonneg hC hφ₀.le) one_pos, fun N hN => ?_⟩
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hE4N : E 4 1 ≤ (N : ℝ) :=
    Nat.ceil_le.mp (le_trans (le_max_right _ _) hN)
  -- size facts
  have h5 : (5 : ℝ) ≤ (N : ℝ) := by
    have h51 : (4 : ℝ) + 1 ≤ E 4 1 := by exact_mod_cast main_succ_le_E_one 4
    linarith
  have hN1 : 1 ≤ N := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast h1
  have hsd4 : 4 ≤ stoppingDepth N := main_stoppingDepth_ge hE4N
  -- bridge facts (positivity of the normalizer)
  have huIcc : phaseCoordinate N ∈ Set.Icc (1 : ℝ) (Real.exp 1) :=
    main_phaseCoordinate_mem_Icc hN1
  have hu0 : (0 : ℝ) < phaseCoordinate N := lt_of_lt_of_le one_pos huIcc.1
  have hΦu : 0 < phasePhi (phaseCoordinate N) := phasePhi_pos _ huIcc
  have hφ₀le : phasePhi u₀ ≤ phasePhi (phaseCoordinate N) :=
    (isMinOn_iff.mp hu₀min) _ huIcc
  have hprod : D (stoppingDepth N) (phaseCoordinate N)
      = ∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ) :=
    main_D_eq_prod_iteratedLog hN1 (by omega)
  have hPpos : 0 < ∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ) := by
    rw [← hprod]
    exact D_pos hu0 _
  have ha0 : (0 : ℝ) < iteratedLog 3 (N : ℝ) :=
    lt_of_lt_of_le one_pos (main_le_iteratedLog_of_E_le 3
      (le_trans (E_lt_E_succ 3 1).le hE4N))
  have hb0 : (0 : ℝ) < iteratedLog 4 (N : ℝ) :=
    lt_of_lt_of_le one_pos (main_le_iteratedLog_of_E_le 4 hE4N)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hnL : (0 : ℝ) < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (by linarith) hlogN
  -- the constant bound `C/Φ(u_N) ≤ C/Φ(u₀) + 1`
  have hbound : C / phasePhi (phaseCoordinate N) ≤ C / phasePhi u₀ + 1 := by
    have h1 : C / phasePhi (phaseCoordinate N) ≤ C / phasePhi u₀ := by gcongr
    linarith
  exact main_uniform_error_transfer hnL hPpos hΦu ha0 hb0 (hmain N hN₀) hbound

end Erdos320
