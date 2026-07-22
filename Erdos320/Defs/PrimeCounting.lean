import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Prime-counting objects: `π` on real arguments, `Li`, and Chebyshev `ϑ`

These are the objects in which the manuscript's two external
prime-distribution inputs are stated (see `Erdos320/Assumptions.lean`):

* eq. `FKS-pi` (Fiori–Kadiri–Swidinsky, Corollary 22):
  `|π(t) − Li(t)| ≤ 9.2211·t·√(log t)·exp(−0.8476·√(log t))` for `t ≥ 2`;
* eq. `theta-explicit` (Dusart): `|ϑ(t) − t| ≤ 0.006788·t/log t` for
  `t ≥ 89 967 803` — the *proved theorem* `dusart_theta_approx`
  (`Lemmas/ShellCountDusart.lean`), derived from the axiom `dusart_theta_k3`
  (Dusart 2018 Thm 4.2, `k = 3` row `|ϑ(t)−t| ≤ t/(log t)³`, `t ≥ 89 967 803`).

`π` reuses Mathlib's `Nat.primeCounting`; `Li(x) = ∫_2^x dt/log t` and
`ϑ(x) = ∑_{p ≤ x} log p` follow the manuscript's conventions (set out just
before eq. `FKS-pi` in § `sec:averaging-relation`).
-/

namespace Erdos320

/-- The prime-counting function on real arguments:
`π(x)` = number of primes `≤ x`. -/
noncomputable def primePi (x : ℝ) : ℕ := Nat.primeCounting ⌊x⌋₊

/-- The logarithmic integral `Li(x) = ∫_2^x dt / log t` (the manuscript's
convention, § `sec:averaging-relation`). -/
noncomputable def Li (x : ℝ) : ℝ := ∫ t in (2:ℝ)..x, 1 / Real.log t

/-- The Chebyshev function `ϑ(x) = ∑_{p ≤ x} log p` (sum over primes). -/
noncomputable def chebyshevTheta (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, Real.log p

/-- The project's `chebyshevTheta` agrees with Mathlib's `Chebyshev.theta`: both
sum `log p` over primes `p ≤ ⌊x⌋₊`.  The only nominal difference is that the
project's index set `Finset.Iic ⌊x⌋₊` includes `0` where Mathlib's `Finset.Ioc 0
⌊x⌋₊` does not, but the prime filter drops `0` on both sides, so the sums are
equal.  This bridge lets downstream files inherit Mathlib's Chebyshev bounds. -/
theorem chebyshevTheta_eq_theta (x : ℝ) : chebyshevTheta x = Chebyshev.theta x := by
  rw [chebyshevTheta, Chebyshev.theta]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc, and_congr_left_iff]
  intro hp
  exact ⟨fun hle => ⟨hp.pos, hle⟩, fun h => h.2⟩

end Erdos320
