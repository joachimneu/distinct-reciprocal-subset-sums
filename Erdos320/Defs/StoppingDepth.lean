import Erdos320.Defs.IteratedExp

/-!
# Iterated logarithms, the stopping depth `h(N)`, and the phase coordinate `u_N`

The manuscript's eq. `h-def-intro`: for sufficiently large `N`,
```
log_j : j-fold iterated natural logarithm,
h(N) = max { j ≥ 3 : log_k N ≥ 1 for every 3 ≤ k ≤ j },
u_N = log_{h(N)} N ∈ [1, e).
```
**Definitional care.**  Over partial reals (where `log` is undefined below
`0`) the downward quantification is redundant and one may write
`max { j ≥ 3 : log_j N ≥ 1 }`.  Mathlib's `Real.log`, however, is total
(`log x = log |x|`), so the naive predicate `1 ≤ iteratedLog j N` can
*resurrect* at junk depths beyond the intended `h(N)` (e.g. after
`log_{h+2} N ≤ −e`); `stoppingDepth` therefore quantifies the predicate
downward (`∀ k ≤ j, 1 ≤ log_k N`), the paper's first-crossing depth
(eq. `h-def-intro`).  The bound `h N ≤ N` used in `Nat.findGreatest` is
harmless: `log_j N ≥ 1` (all the way down) forces `N ≥ E_j(1) ≥ j` (proved
where needed).

For `N` below `⌊E_3(1)⌋ = 3814279` the paper's `h(N)` is undefined; the
`Nat.findGreatest` convention then returns a small junk value, and every
theorem using `h` carries an explicit largeness hypothesis.
-/

namespace Erdos320

/-- `iteratedLog j x`: the `j`-fold iterated natural logarithm `log_j x`
(with Mathlib's total `Real.log` convention `log x = log |x|`, `log 0 = 0`). -/
noncomputable def iteratedLog : ℕ → ℝ → ℝ
  | 0, x => x
  | j + 1, x => Real.log (iteratedLog j x)

@[simp] theorem iteratedLog_zero (x : ℝ) : iteratedLog 0 x = x := rfl

theorem iteratedLog_succ (j : ℕ) (x : ℝ) :
    iteratedLog (j + 1) x = Real.log (iteratedLog j x) := rfl

/-- Peeling the *innermost* logarithm instead of the outermost:
`log_{j+1} x = log_j (log x)`. -/
theorem iteratedLog_succ_outer (j : ℕ) (x : ℝ) :
    iteratedLog (j + 1) x = iteratedLog j (Real.log x) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih => rw [iteratedLog_succ (j + 1) x, ih x, ← iteratedLog_succ]

open Classical in
/-- The stopping depth
`h(N) = max{j ≥ 3 : log_k N ≥ 1 for every 3 ≤ k ≤ j}` (eq. `h-def-intro`),
formalized with the predicate quantified downward (`∀ k ≤ j`) so that
Mathlib's `log |x|` convention cannot resurrect it at junk depths — see the
module docstring.  Junk value for `N < E₃(1)`. -/
noncomputable def stoppingDepth (N : ℕ) : ℕ :=
  Nat.findGreatest (fun j => ∀ k ≤ j, 1 ≤ iteratedLog k (N : ℝ)) N

/-- The terminal phase coordinate `u_N = log_{h(N)} N` (eq. `h-def-intro`). -/
noncomputable def phaseCoordinate (N : ℕ) : ℝ :=
  iteratedLog (stoppingDepth N) (N : ℝ)

end Erdos320
