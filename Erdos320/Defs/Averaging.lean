import Erdos320.Defs.LogCount
import Erdos320.Defs.IteratedExp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries

/-!
# The concave averaging function `𝓑`, the threshold index `m_*`, and the
# averaging/recurrence errors `𝓡`, `ρ`

The manuscript's averaging objects (§ `sec:averaging-relation`) together with
their exponential-scale forms (§ `sec:exponential-iteration`,
§ `sec:breakpoint-chords`):
```
𝓑(X)   = ∑_{m ≥ 1} min(g(m), X) / (m(m+1))            (eq. B-def)
m_*(X) = min { m ≥ 1 : g(m) > X }                       (eq. threshold-index-def)
𝓡(X)   = F(e^X) − 𝓑(X)                                  (eq. averaging-relation)
ρ(x)   = x·e^x / m_*(e^x) − 𝓑(x)                        (before eq. threshold-displacement)
H̄_r(u) = 𝓑(E_{r-1}(u))                                  (eq. Hbar)
ρ_r(u) = E_r(u)E_{r-1}(u)/m_*(E_r(u)) − 𝓑(E_{r-1}(u))   (eq. a-rho)
```
`B` is written as a `tsum` over `m : ℕ` shifted by one, so the summation
index set is the paper's `m ≥ 1`.

Note `m_*` is a `Nat.sInf`: it takes the junk value `0` when no `m` has
`g(m) > X`, i.e. never for real use since `g` is unbounded (proved in
`Lemmas/SBasic.lean`).
-/

namespace Erdos320

/-- The summand of `𝓑(X)`: `min(g(m+1), X) / ((m+1)(m+2))`, i.e. the paper's
`m`th term with `m ≥ 1` reindexed to `m : ℕ`. -/
noncomputable def BTerm (X : ℝ) (m : ℕ) : ℝ :=
  min (g (m + 1)) X / ((m + 1 : ℝ) * (m + 2 : ℝ))

/-- The manuscript's concave average `𝓑(X) = ∑_{m≥1} min(g(m), X)/(m(m+1))`
(eq. `B-def`). -/
noncomputable def B (X : ℝ) : ℝ := ∑' m : ℕ, BTerm X m

/-- Every term of `𝓑(X)` is bounded by the corresponding term of the
telescoping series `|X| · ∑ 1/((m+1)(m+2))`. -/
theorem abs_BTerm_le (X : ℝ) (m : ℕ) :
    |BTerm X m| ≤ |X| / ((m + 1 : ℝ) * (m + 2 : ℝ)) := by
  have hpos : (0 : ℝ) < (m + 1 : ℝ) * (m + 2 : ℝ) := by positivity
  rw [BTerm, abs_div, abs_of_pos hpos]
  apply div_le_div_of_nonneg_right ?_ hpos.le
  rcases le_or_gt (g (m + 1)) X with h | h
  · rw [min_eq_left h, abs_of_nonneg (g_nonneg _)]
    exact le_trans h (le_abs_self X)
  · rw [min_eq_right h.le]

/-- The weight series `∑_m 1/((m+1)(m+2))` is summable (compare with the
`p`-series for `p = 2`). -/
theorem summable_weight : Summable fun m : ℕ => 1 / ((m + 1 : ℝ) * (m + 2 : ℝ)) := by
  have hp : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    have h2 := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    have h1 := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h2
    apply h1.congr
    intro n
    push_cast
    ring
  apply Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hp
  have h2 : ((m : ℝ) + 1) ^ 2 ≤ (m + 1 : ℝ) * (m + 2 : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  exact one_div_le_one_div_of_le (by positivity) h2

/-- The series defining `𝓑(X)` converges (locally uniformly in fact; here we
record plain summability). -/
theorem summable_BTerm (X : ℝ) : Summable (BTerm X) := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun m => abs_nonneg _) (abs_BTerm_le X)
  apply (summable_weight.mul_left |X|).congr
  intro m
  rw [mul_one_div]

/-- The manuscript's threshold index
`m_*(X) = min{m ≥ 1 : g(m) > X}` (eq. `threshold-index-def`).  Since
`g(0) = 0 ≤ g(m)` and `X` is only of interest when `X ≥ 0`, the `m ≥ 1`
constraint is automatic. -/
noncomputable def mStar (X : ℝ) : ℕ := sInf {m : ℕ | X < g m}

/-- The averaging-relation error
`𝓡(X) = F(e^X) − 𝓑(X)` (eq. `averaging-relation`). -/
noncomputable def averagingError (X : ℝ) : ℝ := FReal (Real.exp X) - B X

/-- The depth-independent recurrence error
`ρ(x) = x·e^x/m_*(e^x) − 𝓑(x)` (§ `sec:breakpoint-chords`, before
eq. `threshold-displacement`). -/
noncomputable def rho (x : ℝ) : ℝ :=
  x * Real.exp x / (mStar (Real.exp x) : ℝ) - B x

/-- `H̄_r(u) = 𝓑(E_{r-1}(u))`: the averaged value at depth `r` (eq. `Hbar`). -/
noncomputable def Hbar (r : ℕ) (u : ℝ) : ℝ := B (E (r - 1) u)

/-- `ρ_r(u)`: the recurrence error at depth `r` (eq. `a-rho`); by
`E (r-1+1) = exp ∘ E (r-1)` it equals `rho (E (r-1) u)` for `r ≥ 1`
(see `rhoDepth_eq_rho`). -/
noncomputable def rhoDepth (r : ℕ) (u : ℝ) : ℝ := rho (E (r - 1) u)

/-- For `r ≥ 1`, `ρ_r(u)` unfolds to the paper's
`E_r E_{r-1} / m_*(E_r) − 𝓑(E_{r-1})` (eq. `a-rho`). -/
theorem rhoDepth_eq {r : ℕ} (hr : 1 ≤ r) (u : ℝ) :
    rhoDepth r u
      = E r u * E (r - 1) u / (mStar (E r u) : ℝ) - B (E (r - 1) u) := by
  have hE : Real.exp (E (r - 1) u) = E r u := by
    conv_rhs => rw [show r = (r - 1) + 1 by omega]
    rw [E_succ]
  rw [rhoDepth, rho, hE, mul_comm]

/-- The endpoint identity `H̄_r(e) = H̄_{r+1}(1)` (eq. `endpoint-matching`). -/
theorem Hbar_exp_one {r : ℕ} (hr : 1 ≤ r) : Hbar r (Real.exp 1) = Hbar (r + 1) 1 := by
  rw [Hbar, Hbar, E_exp_one, show r - 1 + 1 = r + 1 - 1 by omega]

end Erdos320
