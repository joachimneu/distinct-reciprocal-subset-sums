import Erdos320.Lemmas.IterationLocalization

/-!
# The iteration setting of `lem:iteration-endpoint-matching`, packaged

The paper's iteration lemma (§5) quantifies over sequences `Y_r` with
endpoint matching and the recurrence `Y_{r+1}' = a_r(Y_r + η_r)`.  This file
fixes that hypothesis package as a structure, so the two halves of the
contraction argument (and the eventual instantiation `Y_r = H̄_r` in
`prop:phase`) all speak the same language.

Conventions (matching `IterationLocalization`):
* the phase interval is `[1, e] = Set.Icc 1 (Real.exp 1)`;
* the recurrence is taken in integral form from the left endpoint `1`
  (equivalent to the paper's a.e. ODE for the absolutely continuous
  functions we instantiate with);
* `|η_r| ≤ K·E_{r-2}²/E_{r-1}` is the paper's eq. `rho-small`-shaped forcing
  bound with an explicit constant `K`.
-/

namespace Erdos320

/-- The hypothesis package of `lem:iteration-endpoint-matching`: from depth
`r₀` on, `Y r` is positive, monotone, continuous on `[1, e]`, matches
endpoints across depths, and satisfies the integral recurrence
`Y_{r+1}(u) − Y_{r+1}(1) = ∫_1^u a_r (Y_r + η_r)` with forcing bounded by
`K·E_{r-2}²/E_{r-1}`. -/
structure IterationData where
  /-- The iterated sequence (paper: `Y_r`; instantiated with `H̄_r`). -/
  Y : ℕ → ℝ → ℝ
  /-- The forcing terms (paper: `η_r`; instantiated with `ρ_r`). -/
  η : ℕ → ℝ → ℝ
  /-- The forcing constant in `|η_r| ≤ K·E_{r-2}²/E_{r-1}`. -/
  K : ℝ
  /-- The starting depth (`8 ≤ r₀` keeps every index of the localization
  toolkit in range). -/
  r₀ : ℕ
  r₀_ge : 8 ≤ r₀
  K_nonneg : 0 ≤ K
  Y_pos : ∀ r, r₀ ≤ r → ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), 0 < Y r u
  Y_mono : ∀ r, r₀ ≤ r → MonotoneOn (Y r) (Set.Icc (1 : ℝ) (Real.exp 1))
  Y_cont : ∀ r, r₀ ≤ r → ContinuousOn (Y r) (Set.Icc (1 : ℝ) (Real.exp 1))
  Y_endpoint : ∀ r, r₀ ≤ r → Y r (Real.exp 1) = Y (r + 1) 1
  Y_transport : ∀ r, r₀ ≤ r → ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1),
    Y (r + 1) u - Y (r + 1) 1 = ∫ t in (1 : ℝ)..u, a r t * (Y r t + η r t)
  η_bound : ∀ r, r₀ ≤ r → ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1),
    |η r t| ≤ K * (E (r - 2) t ^ 2 / E (r - 1) t)
  η_integrable : ∀ r, r₀ ≤ r →
    IntervalIntegrable (fun t => a r t * η r t) MeasureTheory.volume 1 (Real.exp 1)

namespace IterationData

/-- The normalized iterates `K_r = Y_r/J_r` (paper's `K_r`). -/
noncomputable def Knorm (d : IterationData) (r : ℕ) (u : ℝ) : ℝ :=
  d.Y r u / J r u

theorem Knorm_endpoint (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r)
    (hr3 : 3 ≤ r) : d.Knorm r (Real.exp 1) = d.Knorm (r + 1) 1 := by
  unfold Knorm
  rw [d.Y_endpoint r hr, J_exp_one hr3]

theorem Knorm_pos (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r)
    {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) : 0 < d.Knorm r u :=
  div_pos (d.Y_pos r hr u hu) (J_pos (by linarith [hu.1]) r)

end IterationData

end Erdos320
