import Erdos320.Defs.Basic

/-!
# The logarithmic count `g` and the real-argument normalized count `FReal`

The manuscript works with
```
g(N) = log S(N),        F(x) = (log x / x) · g(⌊x⌋)   (x ≥ 2),
```
writing `g(x) = g(⌊x⌋)` for real arguments (set up at the start of
§ `sec:overview`).  `Erdos320.F` (in `Basic.lean`) is
the natural-argument specialization; `FReal` here is the paper's real-argument
version, and `FReal_natCast` links the two.
-/

namespace Erdos320

/-- `g N = log S(N)`: the manuscript's logarithmic count. -/
noncomputable def g (N : ℕ) : ℝ := Real.log (S N)

theorem g_nonneg (N : ℕ) : 0 ≤ g N :=
  Real.log_nonneg (by exact_mod_cast one_le_S N)

theorem g_zero : g 0 = 0 := by simp [g, S_zero]

/-- `g` is monotone, since `S` is. -/
theorem g_mono : Monotone g := fun M N h => by
  have hM : (0 : ℝ) < S M := by exact_mod_cast one_le_S M
  exact Real.log_le_log hM (by exact_mod_cast S_mono h)

/-- The paper's real-argument normalized logarithmic count
`F(x) = (log x / x) · g(⌊x⌋)`.  The paper uses it for `x ≥ 2`; for `x < 1` it
vanishes, since `⌊x⌋₊ = 0` forces `g(⌊x⌋₊) = g(0) = 0`. -/
noncomputable def FReal (x : ℝ) : ℝ := (Real.log x / x) * g ⌊x⌋₊

/-- On natural arguments, `FReal` is the normalized count `F` of
`Erdos320.Defs.Basic`. -/
theorem FReal_natCast (N : ℕ) : FReal N = F N := by
  simp [FReal, F, g, Nat.floor_natCast]

end Erdos320
