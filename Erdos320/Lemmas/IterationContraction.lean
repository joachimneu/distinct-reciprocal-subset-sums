import Erdos320.Lemmas.IterationOneStep

/-!
# Contraction, limit, and endpoint matching for the iteration lemma

The closing half of the manuscript's iteration lemma
(`lem:iteration-endpoint-matching`): starting from the one-step estimates of
`Erdos320.Lemmas.IterationOneStep`, run the coupled `(λ_r, s_r, d_r)`
recursion, obtain the uniform bounds eq. `K-bound`–eq. `K-cauchy`, construct
the limit profile `Ψ` (here `IterationData.iterationLimit`), and prove the
conclusion eq. `iteration-endpoint-conclusion`.

For `d : IterationData` (the hypothesis package of the lemma) and the
right-derivative form `hYder` of the recurrence:

* **eq. `K-bound`**: `IterationData.exists_Knorm_uniform_bound` — a uniform
  `M` with `|K_r| ≤ M` for all `r ≥ r₀`, from the sup recursion
  `‖K_{r+1}‖_∞ ≤ ‖K_r‖_∞ + K·q_r(1)` and geometric summability of `q_r(1)`
  (`M = M₀ + 2·K·q_{r₀}(1)` with `M₀` the compactness bound at depth `r₀`).
* **eq. `K-cauchy`** (with eq. `K-derivative`, eq. `K-endpoint-jump` internal):
  `IterationData.exists_Knorm_uniform_diff_bound` — a uniform `C` with
  `|K_{r+1}(u) − K_r(u)| ≤ C·q_r(u)` for all `r ≥ r₀ + 1`.  The paper's
  contraction functional is `λ_r + Γ·s_r` with `Γ = 4C₁`; here the explicit
  one-step constants give `λ_{r+1} + 4s_{r+1} ≤ 42M + 13K + 56ε_rλ_r + 2s_r`
  with `ε_r = 1/E_{r-5}(1) ≤ 1/112`, hence
  `W_{r+1} ≤ (42M + 13K) + W_r/2` for `W_r = λ_r + 4s_r`, so
  `W_r ≤ W := max (W_{r₀+1}) (2(42M + 13K))` for ever, and
  `C = 6M + K + 2W`.
* **The limit `Ψ`**: `IterationData.iterationLimit` (a named `def`, via
  `Filter.limUnder`), with `IterationData.tendsto_Knorm_iterationLimit`
  (pointwise convergence, by completeness from the geometric Cauchy bound)
  and the tail estimate `IterationData.abs_Knorm_sub_iterationLimit_le`
  (`|K_r(u) − Ψ(u)| ≤ 2C·q_r(u)` for `r ≥ r₀ + 1` — the error asserted in
  eq. `iteration-endpoint-conclusion`).
* **Properties of `Ψ`**: `IterationData.iterationLimit_continuousOn` (uniform
  convergence of the continuous `K_r`), `IterationData.iterationLimit_endpoint`
  (`Ψ(1) = Ψ(e)`, from the exact matching `K_{r+1}(1) = K_r(e)`), and
  `IterationData.iterationLimit_pos` (positivity).
* **The packaged lemma**: `IterationData.iteration_endpoint_matching`, the
  existential statement of `lem:iteration-endpoint-matching` as consumed by
  `prop:phase`.

Paper vs. Lean:

* The paper's positivity argument ("Fixing one base depth, we see that every
  later `Y_r` is bounded below by the positive minimum at that depth.  The
  absolute bound on `η_r` may therefore be rewritten as the relative bound
  `|η_r| ≪ Y_r E_{r-2}²/E_{r-1}`") is realized through
  `IterationData.Y_le_Y_succ` (the paper's pointwise depth monotonicity
  `Y_{r+1}(u) ≥ Y_{r+1}(1) = Y_r(e) ≥ Y_r(u)`, from
  `Y_mono` + `Y_endpoint`), the fixed positive floor `y₀ = Y_{r₀}(1)`
  (`IterationData.Y_base_le`), and the one-step minimum recursion
  `min K_{r+1} ≥ (1 − κ·q_r(1))·min K_r` with the explicit
  `κ = K/y₀ + 6` (`IterationData.Knorm_min_step`,
  `IterationData.Knorm_min_step_normalized`) — the paper's factor
  `(1 − C₂q_r(1) − C₂E_{r-2}(1)²/E_{r-1}(1))` with the super-exponential
  term absorbed into `q_r(1)` via `E_sq_ratio_le_q_one`.  The base depth is
  chosen by the Archimedean property from `q_one_tendsto_zero` (the paper's
  "from any sufficiently large fixed base depth").
* The one-step endpoint bound (`Knorm_endpoint_step`) is
  `s_{r+1} ≤ 6M + K + 7ε_rλ_r` — the paper's eq. `scalar-endpoint-bound`
  `s_{r+1} ≤ C₁(1 + M + ε_r λ_r)` with explicit constants.  It carries no
  `s_r`-dependence: the endpoint atom of the decomposition vanishes
  identically at `u = e` (see `Knorm_endpoint_step` in
  `Erdos320.Lemmas.IterationOneStep`).
* All constants are explicit; no Vinogradov symbols survive.
-/

namespace Erdos320

open MeasureTheory

/-! ## Decay helpers for the gap `q r 1` and the iterate `E` -/

/-- The endpoint gaps vanish: `q r 1 → 0` as `r → ∞` (geometric decay
`q_{r+1}(1) ≤ q_r(1)/2` via `q_succ_le_half`).  This is what lets the
positivity argument pick a base depth with prescribed smallness
(the paper's "from any sufficiently large fixed base depth"). -/
theorem q_one_tendsto_zero :
    Filter.Tendsto (fun r : ℕ => q r 1) Filter.atTop (nhds 0) := by
  have hgeom : Filter.Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k * q 4 1)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (q 4 1)
  have hshift : Filter.Tendsto (fun k : ℕ => q (k + 4) 1) Filter.atTop (nhds 0) :=
    squeeze_zero (fun k => (q_pos one_pos _).le)
      (fun k => by rw [Nat.add_comm k 4]; exact q_add_le_geometric le_rfl le_rfl k)
      hgeom
  exact (Filter.tendsto_add_atTop_iff_nat 4).mp hshift

/-- `112 ≤ E_{r-5}(1)` for `r ≥ 8` (via `E₃(1) > 3.8·10⁶` and depth
monotonicity): the numeric input that makes `ε_r = 1/E_{r-5}(1) ≤ 1/112`,
which is all the contraction needs (`56·ε_r ≤ 1/2`). -/
theorem E_sub_five_one_ge {r : ℕ} (hr : 8 ≤ r) : (112 : ℝ) ≤ E (r - 5) 1 := by
  have h3 : E 3 1 ≤ E (r - 5) 1 :=
    E_mono_depth (le_refl (1 : ℝ)) (show 3 ≤ r - 5 by omega)
  linarith [E_three_one_gt]

/-- The forcing scale is dominated by the endpoint gap: for `r ≥ 6` and
`t ≥ 1`, `E_{r-2}(t)²/E_{r-1}(t) ≤ q_r(1)` (the super-exponential smallness
behind eq. `forcing-localization`, here in the pointwise form the positivity
recursion needs to convert the absolute `η`-bound into a relative one). -/
theorem E_sq_ratio_le_q_one {r : ℕ} (hr : 6 ≤ r) {t : ℝ} (ht : 1 ≤ t) :
    E (r - 2) t ^ 2 / E (r - 1) t ≤ q r 1 := by
  have hE20t : (20 : ℝ) ≤ E (r - 2) t := twenty_le_E (by omega) ht
  have h1 : E (r - 2) t ^ 2 / E (r - 1) t ≤ Real.exp (-(E (r - 2) t) / 2) := by
    have h := E_sq_div_le (u := t) (j := r - 2) hE20t
    rwa [show r - 2 + 1 = r - 1 by omega] at h
  have h2 : Real.exp (-(E (r - 2) t) / 2) ≤ Real.exp (-(E (r - 2) 1) / 2) :=
    Real.exp_le_exp.mpr (by linarith [E_mono (r - 2) ht])
  have hT20 : (20 : ℝ) ≤ E (r - 2) 1 := twenty_le_E (by omega) le_rfl
  have hU1 : (1 : ℝ) ≤ E (r - 3) 1 := one_le_E_of_one_le le_rfl (r - 3)
  have hUT : E (r - 3) 1 ≤ E (r - 2) 1 := by
    have h := (E_lt_E_succ (r - 3) 1).le
    rwa [show r - 3 + 1 = r - 2 by omega] at h
  have h3 : Real.exp (-(E (r - 2) 1) / 2) ≤ 1 / (E (r - 2) 1 * E (r - 3) 1) := by
    have hsq : E (r - 2) 1 ^ 2 ≤ Real.exp (E (r - 2) 1 / 2) := sq_le_exp_half hT20
    have hTU_pos : (0 : ℝ) < E (r - 2) 1 * E (r - 3) 1 :=
      mul_pos (by linarith) (by linarith)
    have hle : E (r - 2) 1 * E (r - 3) 1 ≤ Real.exp (E (r - 2) 1 / 2) := by
      nlinarith
    rw [show -(E (r - 2) 1) / 2 = -(E (r - 2) 1 / 2) by ring, Real.exp_neg,
      inv_eq_one_div]
    exact one_div_le_one_div_of_le hTU_pos hle
  have h4 : (1 : ℝ) / (E (r - 2) 1 * E (r - 3) 1) = q (r + 1) 1 := by
    unfold q
    rw [show r + 1 - 3 = r - 2 by omega, show r + 1 - 4 = r - 3 by omega]
  have h5 : q (r + 1) 1 ≤ q r 1 := by
    have h := q_succ_le_half (le_refl (1 : ℝ)) (show 4 ≤ r by omega)
    linarith [q_pos one_pos r]
  linarith

namespace IterationData

/-! ## Step A: the uniform sup bound (eq. `K-bound`) -/

/-- **eq. `K-bound`** (paper: "there is a fixed `M` such that
`‖K_r‖_∞ ≤ M` at every sufficiently large depth" — here at *every* depth
`r ≥ r₀`): the base bound `M₀` exists by compactness, and the sup recursion
`Knorm_sup_step` adds at most `K·q_{r₀+n}(1) ≤ K·(1/2)ⁿq_{r₀}(1)` per step,
summing to `M = M₀ + 2·K·q_{r₀}(1)`. -/
theorem exists_Knorm_uniform_bound (d : IterationData) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r, d.r₀ ≤ r →
      ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1), |d.Knorm r t| ≤ M := by
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨le_rfl, h1e⟩
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (d.Knorm_continuousOn le_rfl)
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 1 h1mem)
  have hKq₀ : 0 ≤ d.K * q d.r₀ 1 :=
    mul_nonneg d.K_nonneg (q_pos one_pos d.r₀).le
  have hstep : ∀ n : ℕ, ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      |d.Knorm (d.r₀ + n) t|
        ≤ M₀ + 2 * (d.K * q d.r₀ 1) * (1 - (1 / 2 : ℝ) ^ n) := by
    intro n
    induction n with
    | zero =>
        intro t ht
        have h := hM₀ t ht
        rw [Real.norm_eq_abs] at h
        simpa using h
    | succ n ih =>
        intro t ht
        have hsup := d.Knorm_sup_step (show d.r₀ ≤ d.r₀ + n by omega)
          (M₀ + 2 * (d.K * q d.r₀ 1) * (1 - (1 / 2 : ℝ) ^ n)) ih ht
        have hqgeo : q (d.r₀ + n) 1 ≤ (1 / 2 : ℝ) ^ n * q d.r₀ 1 := by
          have h8 := d.r₀_ge
          exact q_add_le_geometric le_rfl (by omega) n
        have hKq : d.K * q (d.r₀ + n) 1 ≤ d.K * ((1 / 2 : ℝ) ^ n * q d.r₀ 1) :=
          mul_le_mul_of_nonneg_left hqgeo d.K_nonneg
        have harith : M₀ + 2 * (d.K * q d.r₀ 1) * (1 - (1 / 2 : ℝ) ^ n)
            + d.K * ((1 / 2 : ℝ) ^ n * q d.r₀ 1)
            = M₀ + 2 * (d.K * q d.r₀ 1) * (1 - (1 / 2 : ℝ) ^ (n + 1)) := by
          ring
        rw [show d.r₀ + (n + 1) = d.r₀ + n + 1 by omega]
        linarith
  refine ⟨M₀ + 2 * (d.K * q d.r₀ 1), by linarith, fun r hr t ht => ?_⟩
  have h := hstep (r - d.r₀) t ht
  rw [Nat.add_sub_cancel' hr] at h
  have hpow : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (r - d.r₀) := by positivity
  nlinarith

/-! ## Steps B and C: base constants and the coupled contraction
(eq. `K-derivative`, eq. `K-endpoint-jump`, eq. `K-cauchy`) -/

/-- **eq. `K-cauchy`** with a single uniform constant: there is `C ≥ 0` with
`|K_{r+1}(u) − K_r(u)| ≤ C·q_r(u)` for every `r ≥ r₀ + 1` and `u ∈ [1, e]`.

This is the paper's closing contraction: base constants `λ_{r₀+1}`,
`s_{r₀+1}` exist by compactness (`d_{r₀}` from the sup of the continuous
difference over the compact phase interval, then one Lipschitz step), and
the coupled recursion `λ_{r+1} ≤ 18M + 9K + 28ε_rλ_r + 2s_r`,
`s_{r+1} ≤ 6M + K + 7ε_rλ_r` contracts the functional `W_r = λ_r + 4s_r`
(the paper's `λ_r + Γs_r`, `Γ = 4C₁`) because `ε_r ≤ 1/112`.  The resulting
uniform constant is `C = 6M + K + 2W` with
`W = max (λ_{r₀+1} + 4s_{r₀+1}) (2(42M + 13K))`. -/
theorem exists_Knorm_uniform_diff_bound (d : IterationData)
    (hYder : ∀ r, d.r₀ ≤ r → ∀ x ∈ Set.Ico (1 : ℝ) (Real.exp 1),
      HasDerivWithinAt (d.Y (r + 1)) (a r x * (d.Y r x + d.η r x))
        (Set.Ioi x) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, d.r₀ + 1 ≤ r →
      ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1),
        |d.Knorm (r + 1) u - d.Knorm r u| ≤ C * q r u := by
  have h8 := d.r₀_ge
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨le_rfl, h1e⟩
  obtain ⟨M, hM0, hM⟩ := d.exists_Knorm_uniform_bound
  -- base difference constant `d_{r₀}` by compactness
  have hdBase : ∃ dB : ℝ, 0 ≤ dB ∧ ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      |d.Knorm (d.r₀ + 1) t - d.Knorm d.r₀ t| ≤ dB * q d.r₀ t := by
    obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((d.Knorm_continuousOn (show d.r₀ ≤ d.r₀ + 1 by omega)).sub
        (d.Knorm_continuousOn le_rfl))
    have hC₀0 : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ 1 h1mem)
    have hqe_pos : 0 < q d.r₀ (Real.exp 1) := q_pos (Real.exp_pos 1) d.r₀
    refine ⟨C₀ / q d.r₀ (Real.exp 1), div_nonneg hC₀0 hqe_pos.le,
      fun t ht => ?_⟩
    have h1 : |d.Knorm (d.r₀ + 1) t - d.Knorm d.r₀ t| ≤ C₀ := by
      have h := hC₀ t ht
      rwa [Real.norm_eq_abs] at h
    have h2 : q d.r₀ (Real.exp 1) ≤ q d.r₀ t :=
      q_antitoneOn d.r₀ (Set.mem_Ici.mpr ht.1) (Set.mem_Ici.mpr h1e) ht.2
    have h3 : C₀ = C₀ / q d.r₀ (Real.exp 1) * q d.r₀ (Real.exp 1) :=
      (div_mul_cancel₀ C₀ hqe_pos.ne').symm
    have h4 : C₀ / q d.r₀ (Real.exp 1) * q d.r₀ (Real.exp 1)
        ≤ C₀ / q d.r₀ (Real.exp 1) * q d.r₀ t :=
      mul_le_mul_of_nonneg_left h2 (div_nonneg hC₀0 hqe_pos.le)
    linarith
  obtain ⟨dB, hdB0, hdB⟩ := hdBase
  -- base Lipschitz constant `λ_{r₀+1}` by one Lipschitz step
  have hlamBase : ∃ lam : ℝ, 0 ≤ lam ∧
      ∀ x ∈ Set.Icc (1 : ℝ) (Real.exp 1),
        ∀ y ∈ Set.Icc (1 : ℝ) (Real.exp 1), y ≤ x →
          |d.Knorm (d.r₀ + 1) x - d.Knorm (d.r₀ + 1) y|
            ≤ lam * ∫ t in y..x, D (d.r₀ + 1 - 3) t := by
    refine ⟨2 * dB + 6 * M + 7 * d.K, by linarith [d.K_nonneg],
      fun x hx y hy hyx => ?_⟩
    rw [show d.r₀ + 1 - 3 = d.r₀ - 2 by omega]
    exact d.Knorm_lipschitz_step le_rfl M dB (hM d.r₀ le_rfl) hdB
      (hYder d.r₀ le_rfl) hx hy hyx
  obtain ⟨lamB, hlamB0, hlamB⟩ := hlamBase
  -- base endpoint constant `s_{r₀+1}` (any finite normalizer works)
  have hsBase : ∃ s : ℝ, 0 ≤ s ∧
      |d.Knorm (d.r₀ + 1) (Real.exp 1) - d.Knorm (d.r₀ + 1) 1|
        ≤ s * q (d.r₀ + 1) 1 := by
    refine ⟨|d.Knorm (d.r₀ + 1) (Real.exp 1) - d.Knorm (d.r₀ + 1) 1|
        / q (d.r₀ + 1) 1,
      div_nonneg (abs_nonneg _) (q_pos one_pos _).le, ?_⟩
    rw [div_mul_cancel₀ _ (q_pos one_pos (d.r₀ + 1)).ne']
  obtain ⟨sB, hsB0, hsB⟩ := hsBase
  -- the contraction bound `W` on the functional `λ_r + 4s_r`
  have hW1 : lamB + 4 * sB ≤ max (lamB + 4 * sB) (2 * (42 * M + 13 * d.K)) :=
    le_max_left _ _
  have hW2 : 2 * (42 * M + 13 * d.K)
      ≤ max (lamB + 4 * sB) (2 * (42 * M + 13 * d.K)) := le_max_right _ _
  have hW0 : 0 ≤ max (lamB + 4 * sB) (2 * (42 * M + 13 * d.K)) :=
    le_trans (by linarith [d.K_nonneg]) hW2
  -- the coupled recursion, from depth `r₀ + 1` onward
  have hmain : ∀ n : ℕ, ∃ lam s : ℝ, 0 ≤ lam ∧ 0 ≤ s ∧
      lam + 4 * s ≤ max (lamB + 4 * sB) (2 * (42 * M + 13 * d.K)) ∧
      (∀ x ∈ Set.Icc (1 : ℝ) (Real.exp 1),
        ∀ y ∈ Set.Icc (1 : ℝ) (Real.exp 1), y ≤ x →
          |d.Knorm (d.r₀ + 1 + n) x - d.Knorm (d.r₀ + 1 + n) y|
            ≤ lam * ∫ t in y..x, D (d.r₀ + 1 + n - 3) t) ∧
      |d.Knorm (d.r₀ + 1 + n) (Real.exp 1) - d.Knorm (d.r₀ + 1 + n) 1|
        ≤ s * q (d.r₀ + 1 + n) 1 := by
    intro n
    induction n with
    | zero =>
        exact ⟨lamB, sB, hlamB0, hsB0, hW1, by simpa using hlamB,
          by simpa using hsB⟩
    | succ n ih =>
        obtain ⟨lam, s, hlam0, hs0, hWn, hlam, hs⟩ := ih
        rw [show d.r₀ + 1 + (n + 1) = d.r₀ + 1 + n + 1 by omega]
        have hr₀r : d.r₀ ≤ d.r₀ + 1 + n := by omega
        have hE112 : (112 : ℝ) ≤ E (d.r₀ + 1 + n - 5) 1 :=
          E_sub_five_one_ge (by omega)
        have hEpos : (0 : ℝ) < E (d.r₀ + 1 + n - 5) 1 := by linarith
        have hMr := hM (d.r₀ + 1 + n) hr₀r
        -- one Cauchy step (eq. `scalar-cauchy-bound`)
        have hdr : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1),
            |d.Knorm (d.r₀ + 1 + n + 1) t - d.Knorm (d.r₀ + 1 + n) t|
              ≤ (6 * M + d.K + 14 * lam / E (d.r₀ + 1 + n - 5) 1 + s)
                  * q (d.r₀ + 1 + n) t :=
          fun t ht => d.Knorm_diff_step hr₀r M lam s hMr hlam hs ht
        -- one endpoint step (eq. `scalar-endpoint-bound`)
        have hs' := d.Knorm_endpoint_step hr₀r M lam hMr hlam
        -- one Lipschitz step (eq. `scalar-derivative-bound`)
        have hlam' : ∀ x ∈ Set.Icc (1 : ℝ) (Real.exp 1),
            ∀ y ∈ Set.Icc (1 : ℝ) (Real.exp 1), y ≤ x →
              |d.Knorm (d.r₀ + 1 + n + 1) x - d.Knorm (d.r₀ + 1 + n + 1) y|
                ≤ (2 * (6 * M + d.K + 14 * lam / E (d.r₀ + 1 + n - 5) 1 + s)
                    + 6 * M + 7 * d.K)
                  * ∫ t in y..x, D (d.r₀ + 1 + n + 1 - 3) t := by
          intro x hx y hy hyx
          rw [show d.r₀ + 1 + n + 1 - 3 = d.r₀ + 1 + n - 2 by omega]
          exact d.Knorm_lipschitz_step hr₀r M
            (6 * M + d.K + 14 * lam / E (d.r₀ + 1 + n - 5) 1 + s) hMr hdr
            (hYder _ hr₀r) hx hy hyx
        -- absorb `ε_r = 1/E_{r-5}(1) ≤ 1/112` into the contraction
        have hdiv14 : 14 * lam / E (d.r₀ + 1 + n - 5) 1 ≤ lam / 8 := by
          rw [div_le_div_iff₀ hEpos (by norm_num : (0 : ℝ) < 8)]
          nlinarith [mul_le_mul_of_nonneg_left hE112 hlam0]
        have hdiv7 : 7 * lam / E (d.r₀ + 1 + n - 5) 1 ≤ lam / 16 := by
          rw [div_le_div_iff₀ hEpos (by norm_num : (0 : ℝ) < 16)]
          nlinarith [mul_le_mul_of_nonneg_left hE112 hlam0]
        have hdiv14nn : 0 ≤ 14 * lam / E (d.r₀ + 1 + n - 5) 1 :=
          div_nonneg (by linarith) hEpos.le
        have hdiv7nn : 0 ≤ 7 * lam / E (d.r₀ + 1 + n - 5) 1 :=
          div_nonneg (by linarith) hEpos.le
        refine ⟨2 * (6 * M + d.K + 14 * lam / E (d.r₀ + 1 + n - 5) 1 + s)
            + 6 * M + 7 * d.K,
          6 * M + d.K + 7 * lam / E (d.r₀ + 1 + n - 5) 1,
          by linarith [d.K_nonneg], by linarith [d.K_nonneg], ?_, hlam', hs'⟩
        linarith [d.K_nonneg]
  -- extract the uniform Cauchy constant
  refine ⟨6 * M + d.K + 2 * max (lamB + 4 * sB) (2 * (42 * M + 13 * d.K)),
    by linarith [d.K_nonneg], fun r hr u hu => ?_⟩
  obtain ⟨lam, s, hlam0, hs0, hWn, hlam, hs⟩ := hmain (r - (d.r₀ + 1))
  rw [Nat.add_sub_cancel' hr] at hlam hs
  have hr₀r : d.r₀ ≤ r := by omega
  have hE112 : (112 : ℝ) ≤ E (r - 5) 1 := E_sub_five_one_ge (by omega)
  have hEpos : (0 : ℝ) < E (r - 5) 1 := by linarith
  have hstep := d.Knorm_diff_step hr₀r M lam s (hM r hr₀r) hlam hs hu
  have hdiv : 14 * lam / E (r - 5) 1 ≤ lam := by
    rw [div_le_iff₀ hEpos]
    nlinarith [mul_le_mul_of_nonneg_left hE112 hlam0]
  have hq := q_pos (lt_of_lt_of_le one_pos hu.1) r
  have hcoef : 6 * M + d.K + 14 * lam / E (r - 5) 1 + s
      ≤ 6 * M + d.K + 2 * max (lamB + 4 * sB) (2 * (42 * M + 13 * d.K)) := by
    linarith
  exact hstep.trans (mul_le_mul_of_nonneg_right hcoef hq.le)

/-! ## Step D: the limit `Ψ` and its tail bound -/

/-- The limit profile `Ψ` of `lem:iteration-endpoint-matching`: the pointwise
limit of the normalized iterates `K_r = Y_r/J_r` along `r → ∞`.  On the phase
interval and under the recurrence hypothesis `hYder` this is an honest limit
(`tendsto_Knorm_iterationLimit`) with geometric tail
(`abs_Knorm_sub_iterationLimit_le`). -/
noncomputable def iterationLimit (d : IterationData) : ℝ → ℝ := fun u =>
  Filter.limUnder Filter.atTop fun r => d.Knorm r u

/-- Pointwise convergence `K_r(u) → Ψ(u)` on `[1, e]`: the sequence is Cauchy
by the uniform difference bound and geometric decay of `q_r(u)`, and `ℝ` is
complete. -/
theorem tendsto_Knorm_iterationLimit (d : IterationData)
    (hYder : ∀ r, d.r₀ ≤ r → ∀ x ∈ Set.Ico (1 : ℝ) (Real.exp 1),
      HasDerivWithinAt (d.Y (r + 1)) (a r x * (d.Y r x + d.η r x))
        (Set.Ioi x) x)
    {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    Filter.Tendsto (fun r => d.Knorm r u) Filter.atTop
      (nhds (d.iterationLimit u)) := by
  have h8 := d.r₀_ge
  obtain ⟨C, hC0, hC⟩ := d.exists_Knorm_uniform_diff_bound hYder
  have hu1 : (1 : ℝ) ≤ u := hu.1
  have hcauchy : CauchySeq fun n : ℕ => d.Knorm (n + (d.r₀ + 1)) u := by
    apply cauchySeq_of_le_geometric (1 / 2 : ℝ) (C * q (d.r₀ + 1) u)
      (by norm_num)
    intro n
    rw [Real.dist_eq]
    show |d.Knorm (n + (d.r₀ + 1)) u - d.Knorm (n + 1 + (d.r₀ + 1)) u|
      ≤ C * q (d.r₀ + 1) u * (1 / 2) ^ n
    have hd := hC (n + (d.r₀ + 1)) (by omega) u hu
    have hgeo : q (n + (d.r₀ + 1)) u ≤ (1 / 2 : ℝ) ^ n * q (d.r₀ + 1) u := by
      rw [Nat.add_comm n (d.r₀ + 1)]
      exact q_add_le_geometric hu1 (by omega) n
    calc |d.Knorm (n + (d.r₀ + 1)) u - d.Knorm (n + 1 + (d.r₀ + 1)) u|
        = |d.Knorm (n + (d.r₀ + 1) + 1) u - d.Knorm (n + (d.r₀ + 1)) u| := by
          rw [show n + 1 + (d.r₀ + 1) = n + (d.r₀ + 1) + 1 by omega,
            abs_sub_comm]
      _ ≤ C * q (n + (d.r₀ + 1)) u := hd
      _ ≤ C * ((1 / 2 : ℝ) ^ n * q (d.r₀ + 1) u) :=
          mul_le_mul_of_nonneg_left hgeo hC0
      _ = C * q (d.r₀ + 1) u * (1 / 2) ^ n := by ring
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have htendsto : Filter.Tendsto (fun r => d.Knorm r u) Filter.atTop
      (nhds L) := (Filter.tendsto_add_atTop_iff_nat (d.r₀ + 1)).mp hL
  have hlim : d.iterationLimit u = L := htendsto.limUnder_eq
  rw [hlim]
  exact htendsto

/-- **The error term of eq. `iteration-endpoint-conclusion`**: a uniform
`C ≥ 0` and a depth `r₁ = r₀ + 1` with `|K_r(u) − Ψ(u)| ≤ C·q_r(u)` for all
`r ≥ r₁`, `u ∈ [1, e]` (the paper's `|K_r(u) − Ψ(u)| ≪ q_r(u)`, from
`∑_{s ≥ r} q_s(u) ≤ 2q_r(u)`). -/
theorem abs_Knorm_sub_iterationLimit_le (d : IterationData)
    (hYder : ∀ r, d.r₀ ≤ r → ∀ x ∈ Set.Ico (1 : ℝ) (Real.exp 1),
      HasDerivWithinAt (d.Y (r + 1)) (a r x * (d.Y r x + d.η r x))
        (Set.Ioi x) x) :
    ∃ (C : ℝ) (r₁ : ℕ), 0 ≤ C ∧ ∀ r, r₁ ≤ r →
      ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1),
        |d.Knorm r u - d.iterationLimit u| ≤ C * q r u := by
  have h8 := d.r₀_ge
  obtain ⟨C, hC0, hC⟩ := d.exists_Knorm_uniform_diff_bound hYder
  refine ⟨2 * C, d.r₀ + 1, by linarith, fun r hr u hu => ?_⟩
  have hu1 : (1 : ℝ) ≤ u := hu.1
  have hqpos := q_pos (lt_of_lt_of_le one_pos hu1) r
  -- telescoping: partial increments sum geometrically below `2C·q_r(u)`
  have htel : ∀ k : ℕ, |d.Knorm (k + r) u - d.Knorm r u|
      ≤ C * (2 - 2 * (1 / 2 : ℝ) ^ k) * q r u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hdiff := hC (k + r) (by omega) u hu
        have hgeo : q (k + r) u ≤ (1 / 2 : ℝ) ^ k * q r u := by
          rw [Nat.add_comm k r]
          exact q_add_le_geometric hu1 (by omega) k
        have htri : |d.Knorm (k + 1 + r) u - d.Knorm r u|
            ≤ |d.Knorm (k + r + 1) u - d.Knorm (k + r) u|
              + |d.Knorm (k + r) u - d.Knorm r u| := by
          rw [show k + 1 + r = k + r + 1 by omega]
          exact abs_sub_le _ _ _
        have hCq : |d.Knorm (k + r + 1) u - d.Knorm (k + r) u|
            ≤ C * ((1 / 2 : ℝ) ^ k * q r u) :=
          hdiff.trans (mul_le_mul_of_nonneg_left hgeo hC0)
        have harith : C * ((1 / 2 : ℝ) ^ k * q r u)
            + C * (2 - 2 * (1 / 2 : ℝ) ^ k) * q r u
            = C * (2 - 2 * (1 / 2 : ℝ) ^ (k + 1)) * q r u := by
          ring
        linarith
  have htel2 : ∀ k : ℕ, |d.Knorm (k + r) u - d.Knorm r u| ≤ 2 * C * q r u := by
    intro k
    have h := htel k
    have hx : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    nlinarith [mul_nonneg (mul_nonneg hC0 hx) hqpos.le]
  -- pass to the limit along `k → ∞`
  have htendsto := d.tendsto_Knorm_iterationLimit hYder hu
  have hshift : Filter.Tendsto (fun k : ℕ => d.Knorm (k + r) u) Filter.atTop
      (nhds (d.iterationLimit u)) :=
    (Filter.tendsto_add_atTop_iff_nat r).mpr htendsto
  have habs : Filter.Tendsto (fun k : ℕ => |d.Knorm (k + r) u - d.Knorm r u|)
      Filter.atTop (nhds (|d.iterationLimit u - d.Knorm r u|)) :=
    (hshift.sub_const _).abs
  have hle : |d.iterationLimit u - d.Knorm r u| ≤ 2 * C * q r u :=
    le_of_tendsto habs (Filter.Eventually.of_forall htel2)
  rw [abs_sub_comm]
  exact hle

/-! ## Step E: continuity, endpoint matching, positivity of `Ψ` -/

/-- `Ψ` is continuous on `[1, e]`: the convergence `K_r → Ψ` is *uniform*
(the tail bound is dominated by `C·q_r(1) → 0`), and each `K_r` is
continuous. -/
theorem iterationLimit_continuousOn (d : IterationData)
    (hYder : ∀ r, d.r₀ ≤ r → ∀ x ∈ Set.Ico (1 : ℝ) (Real.exp 1),
      HasDerivWithinAt (d.Y (r + 1)) (a r x * (d.Y r x + d.η r x))
        (Set.Ioi x) x) :
    ContinuousOn d.iterationLimit (Set.Icc 1 (Real.exp 1)) := by
  obtain ⟨C, r₁, hC0, htail⟩ := d.abs_Knorm_sub_iterationLimit_le hYder
  have huniform : TendstoUniformlyOn (fun r u => d.Knorm r u)
      d.iterationLimit Filter.atTop (Set.Icc 1 (Real.exp 1)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hq0 : Filter.Tendsto (fun r : ℕ => C * q r 1) Filter.atTop
        (nhds 0) := by
      simpa using q_one_tendsto_zero.const_mul C
    filter_upwards [hq0.eventually_lt_const hε, Filter.eventually_ge_atTop r₁]
      with r hrq hrr₁
    intro u hu
    have hu1 : (1 : ℝ) ≤ u := hu.1
    have hmono : q r u ≤ q r 1 :=
      q_antitoneOn r (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu1) hu1
    have hbound : |d.Knorm r u - d.iterationLimit u| ≤ C * q r 1 :=
      (htail r hrr₁ u hu).trans (mul_le_mul_of_nonneg_left hmono hC0)
    rw [Real.dist_eq]
    calc |d.iterationLimit u - d.Knorm r u|
        = |d.Knorm r u - d.iterationLimit u| := abs_sub_comm _ _
      _ ≤ C * q r 1 := hbound
      _ < ε := hrq
  exact huniform.continuousOn
    (Filter.eventually_atTop.mpr
      ⟨d.r₀, fun r hr => d.Knorm_continuousOn hr⟩).frequently

/-- **Endpoint matching** `Ψ(1) = Ψ(e)`: the exact relation
`K_{r+1}(1) = K_r(e)` (`Knorm_endpoint`) interleaves the two endpoint
sequences, so their limits agree. -/
theorem iterationLimit_endpoint (d : IterationData)
    (hYder : ∀ r, d.r₀ ≤ r → ∀ x ∈ Set.Ico (1 : ℝ) (Real.exp 1),
      HasDerivWithinAt (d.Y (r + 1)) (a r x * (d.Y r x + d.η r x))
        (Set.Ioi x) x) :
    d.iterationLimit 1 = d.iterationLimit (Real.exp 1) := by
  have h8 := d.r₀_ge
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1 := d.tendsto_Knorm_iterationLimit hYder (u := 1) ⟨le_rfl, h1e⟩
  have he := d.tendsto_Knorm_iterationLimit hYder (u := Real.exp 1)
    ⟨h1e, le_rfl⟩
  have hshift : Filter.Tendsto (fun r : ℕ => d.Knorm (r + 1) 1)
      Filter.atTop (nhds (d.iterationLimit 1)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr h1
  have hcongr : (fun r : ℕ => d.Knorm (r + 1) 1)
      =ᶠ[Filter.atTop] fun r : ℕ => d.Knorm r (Real.exp 1) := by
    filter_upwards [Filter.eventually_ge_atTop d.r₀] with r hr
    exact (d.Knorm_endpoint hr (by omega)).symm
  exact tendsto_nhds_unique (hshift.congr' hcongr) he

/-- Pointwise monotonicity of `Y` in the depth (the paper's "the minima of
the increasing `Y_r` are nondecreasing from one scale to the next"):
`Y_r(u) ≤ Y_{r+1}(u)` on `[1, e]`, since
`Y_{r+1}(u) ≥ Y_{r+1}(1) = Y_r(e) ≥ Y_r(u)`. -/
theorem Y_le_Y_succ (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r) {u : ℝ}
    (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) : d.Y r u ≤ d.Y (r + 1) u := by
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨le_rfl, h1e⟩
  have hemem : Real.exp 1 ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨h1e, le_rfl⟩
  calc d.Y r u ≤ d.Y r (Real.exp 1) := d.Y_mono r hr hu hemem hu.2
    _ = d.Y (r + 1) 1 := d.Y_endpoint r hr
    _ ≤ d.Y (r + 1) u := d.Y_mono (r + 1) (by omega) h1mem hu hu.1

/-- The fixed positive floor for `Y`: `Y_{r₀}(1) ≤ Y_r(t)` for every
`r ≥ r₀` and `t ∈ [1, e]` (depth monotonicity at the left endpoint, then
phase monotonicity).  This is what turns the absolute `η`-bound into a
relative one (the paper's "Fixing one base depth, we see that every later
`Y_r` is bounded below by the positive minimum at that depth"). -/
theorem Y_base_le (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r) {t : ℝ}
    (ht : t ∈ Set.Icc (1 : ℝ) (Real.exp 1)) : d.Y d.r₀ 1 ≤ d.Y r t := by
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨le_rfl, h1e⟩
  have hbase : ∀ n : ℕ, d.r₀ ≤ n → d.Y d.r₀ 1 ≤ d.Y n 1 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact ih.trans (d.Y_le_Y_succ hn h1mem)
  exact (hbase r hr).trans (d.Y_mono r hr h1mem ht ht.1)

/-- **One-step minimum recursion** (the lower-bound counterpart of
`Knorm_sup_step`, paper: `min K_{r+1} ≥ (1 − C₂q_r(1) − C₂E_{r-2}(1)²/
E_{r-1}(1))·min K_r`): given a positive floor `y₀ ≤ Y_r` on `[1, e]` and a
lower bound `m ≥ 0` for `K_r`, the transport identity gives
`K_{r+1}(u) ≥ (1 − K·q_r(1)/y₀)·((1 − 6q_r(1))·m)` — the relative forcing
loss `c = K·q_r(1)/y₀` (via `E_sq_ratio_le_q_one`) and the missing-mass loss
`6q_r(1)` (via `missing_mass_le`), both explicit. -/
theorem Knorm_min_step (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r)
    {m y₀ : ℝ} (hm0 : 0 ≤ m) (hy₀ : 0 < y₀)
    (hy : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1), y₀ ≤ d.Y r t)
    (hm : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1), m ≤ d.Knorm r t)
    (hc : d.K * q r 1 / y₀ ≤ 1)
    {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    (1 - d.K * q r 1 / y₀) * ((1 - 6 * q r 1) * m) ≤ d.Knorm (r + 1) u := by
  have h8 : 8 ≤ r := d.r₀_ge.trans hr
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨le_rfl, h1e⟩
  have hemem : Real.exp 1 ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨h1e, le_rfl⟩
  have hu1 : (1 : ℝ) ≤ u := hu.1
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
  have hJu : (0 : ℝ) < J (r + 1) u := J_pos hu0 (r + 1)
  have hJ1 : (0 : ℝ) < J (r + 1) 1 := J_pos one_pos (r + 1)
  have hc0 : 0 ≤ d.K * q r 1 / y₀ :=
    div_nonneg (mul_nonneg d.K_nonneg (q_pos one_pos r).le) hy₀.le
  -- the relative forcing bound `|η_r| ≤ c·Y_r`
  have hrel : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      |d.η r t| ≤ d.K * q r 1 / y₀ * d.Y r t := by
    intro t ht
    have h1 : |d.η r t| ≤ d.K * (E (r - 2) t ^ 2 / E (r - 1) t) :=
      d.η_bound r hr t ht
    have h2 : E (r - 2) t ^ 2 / E (r - 1) t ≤ q r 1 :=
      E_sq_ratio_le_q_one (by omega) ht.1
    have h3 : d.K * (E (r - 2) t ^ 2 / E (r - 1) t) ≤ d.K * q r 1 :=
      mul_le_mul_of_nonneg_left h2 d.K_nonneg
    have h4 : d.K * q r 1 = d.K * q r 1 / y₀ * y₀ :=
      (div_mul_cancel₀ _ hy₀.ne').symm
    have h5 : d.K * q r 1 / y₀ * y₀ ≤ d.K * q r 1 / y₀ * d.Y r t :=
      mul_le_mul_of_nonneg_left (hy t ht) hc0
    linarith
  -- integrability plumbing
  have haJ_int : IntervalIntegrable (fun t => a r t * J r t) volume 1 u :=
    ((continuous_a r).mul (continuous_J r)).intervalIntegrable 1 u
  have hsubIcc := uIcc_subset_phaseInterval h1mem hu
  have haJK_int : IntervalIntegrable
      (fun t => a r t * J r t * d.Knorm r t) volume 1 u :=
    (((continuous_a r).continuousOn.mul (continuous_J r).continuousOn).mul
      ((d.Knorm_continuousOn hr).mono hsubIcc)).intervalIntegrable
  have haη_int : IntervalIntegrable (fun t => a r t * d.η r t) volume 1 u :=
    d.aη_integrable hr h1mem hu
  -- (i) the forcing integral is at least `−c·∫ a_rJ_rK_r`
  have hIη : -(d.K * q r 1 / y₀ * ∫ t in (1 : ℝ)..u, a r t * J r t * d.Knorm r t)
      ≤ ∫ t in (1 : ℝ)..u, a r t * d.η r t := by
    have habs : |∫ t in (1 : ℝ)..u, a r t * d.η r t|
        ≤ ∫ t in (1 : ℝ)..u, |a r t * d.η r t| :=
      intervalIntegral.abs_integral_le_integral_abs hu1
    have hpt : ∀ t ∈ Set.Icc (1 : ℝ) u,
        |a r t * d.η r t|
          ≤ d.K * q r 1 / y₀ * (a r t * J r t * d.Knorm r t) := by
      intro t ht
      have htmem : t ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨ht.1, ht.2.trans hu.2⟩
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
      have hYJK : J r t * d.Knorm r t = d.Y r t := by
        show J r t * (d.Y r t / J r t) = d.Y r t
        rw [mul_comm, div_mul_cancel₀ _ (J_pos ht0 r).ne']
      rw [abs_mul, abs_of_pos (a_pos r t)]
      calc a r t * |d.η r t|
          ≤ a r t * (d.K * q r 1 / y₀ * d.Y r t) :=
            mul_le_mul_of_nonneg_left (hrel t htmem) (a_pos r t).le
        _ = d.K * q r 1 / y₀ * (a r t * (J r t * d.Knorm r t)) := by
            rw [hYJK]; ring
        _ = d.K * q r 1 / y₀ * (a r t * J r t * d.Knorm r t) := by ring
    have hint := intervalIntegral.integral_mono_on hu1 haη_int.abs
      (haJK_int.const_mul (d.K * q r 1 / y₀)) hpt
    rw [intervalIntegral.integral_const_mul] at hint
    have hneg := neg_abs_le (∫ t in (1 : ℝ)..u, a r t * d.η r t)
    linarith
  -- (ii) the mean of `K_r` under the transport measure is at least `m`
  have hIm : m * ∫ t in (1 : ℝ)..u, a r t * J r t
      ≤ ∫ t in (1 : ℝ)..u, a r t * J r t * d.Knorm r t := by
    have hpt : ∀ t ∈ Set.Icc (1 : ℝ) u,
        m * (a r t * J r t) ≤ a r t * J r t * d.Knorm r t := by
      intro t ht
      have htmem : t ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨ht.1, ht.2.trans hu.2⟩
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
      have haJ : (0 : ℝ) < a r t * J r t := mul_pos (a_pos r t) (J_pos ht0 r)
      nlinarith [mul_le_mul_of_nonneg_left (hm t htmem) haJ.le]
    have hint := intervalIntegral.integral_mono_on hu1
      (haJ_int.const_mul m) haJK_int hpt
    rwa [intervalIntegral.integral_const_mul] at hint
  -- (iii) the mass lower bound `J_{r+1}(1) + ∫a_rJ_r ≥ J_{r+1}(u)(1 − 6q_r(1))`
  have hmass_lower : J (r + 1) u * (1 - 6 * q r 1)
      ≤ J (r + 1) 1 + ∫ t in (1 : ℝ)..u, a r t * J r t := by
    have htr := J_transport (show 4 ≤ r by omega) u
    have haR_int : IntervalIntegrable (fun t => a r t * Rdefect r t)
        volume 1 u :=
      ((continuous_a r).mul
        (continuous_Rdefect (show 3 ≤ r by omega))).intervalIntegrable 1 u
    have hsp : (∫ t in (1 : ℝ)..u, a r t * (J r t + Rdefect r t))
        = (∫ t in (1 : ℝ)..u, a r t * J r t)
          + ∫ t in (1 : ℝ)..u, a r t * Rdefect r t := by
      rw [← intervalIntegral.integral_add haJ_int haR_int]
      exact intervalIntegral.integral_congr fun t _ => mul_add _ _ _
    have hmm := missing_mass_le (show 6 ≤ r by omega) hu1
    have hqmono : q r u ≤ q r 1 :=
      q_antitoneOn r (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu1) hu1
    have hprod : J (r + 1) u * q r u ≤ J (r + 1) u * q r 1 :=
      mul_le_mul_of_nonneg_left hqmono hJu.le
    linarith
  -- assemble
  have hIaJK_nonneg : 0 ≤ ∫ t in (1 : ℝ)..u, a r t * J r t * d.Knorm r t := by
    refine intervalIntegral.integral_nonneg hu1 fun t ht => ?_
    have htmem : t ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨ht.1, ht.2.trans hu.2⟩
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
    exact (mul_pos (mul_pos (a_pos r t) (J_pos ht0 r))
      (d.Knorm_pos hr htmem)).le
  have hKe : m ≤ d.Knorm r (Real.exp 1) := hm _ hemem
  have h1c : 0 ≤ 1 - d.K * q r 1 / y₀ := by linarith
  have hprod1 : J (r + 1) 1 * m ≤ J (r + 1) 1 * d.Knorm r (Real.exp 1) :=
    mul_le_mul_of_nonneg_left hKe hJ1.le
  have hprod2 : (1 - d.K * q r 1 / y₀)
        * (m * ∫ t in (1 : ℝ)..u, a r t * J r t)
      ≤ (1 - d.K * q r 1 / y₀)
        * ∫ t in (1 : ℝ)..u, a r t * J r t * d.Knorm r t :=
    mul_le_mul_of_nonneg_left hIm h1c
  have hprod3 : 0 ≤ d.K * q r 1 / y₀
      * ∫ t in (1 : ℝ)..u, a r t * J r t * d.Knorm r t :=
    mul_nonneg hc0 hIaJK_nonneg
  have hprod4 : 0 ≤ d.K * q r 1 / y₀ * m * J (r + 1) 1 :=
    mul_nonneg (mul_nonneg hc0 hm0) hJ1.le
  have hprod5 : (1 - d.K * q r 1 / y₀) * m * (J (r + 1) u * (1 - 6 * q r 1))
      ≤ (1 - d.K * q r 1 / y₀) * m
        * (J (r + 1) 1 + ∫ t in (1 : ℝ)..u, a r t * J r t) :=
    mul_le_mul_of_nonneg_left hmass_lower (mul_nonneg h1c hm0)
  rw [d.Knorm_transport hr hu, le_div_iff₀ hJu]
  linarith

/-- `Knorm_min_step`, normalized to a single loss coefficient
`κ ≥ K/Y_{r₀}(1) + 6`: `min K_{r+1} ≥ (1 − κ·q_r(1))·min K_r` (given
`κ·q_r(1) ≤ 1`).  This is the paper's positivity recursion with an explicit
`C₂`. -/
theorem Knorm_min_step_normalized (d : IterationData) {r : ℕ}
    (hr : d.r₀ ≤ r) {m κ : ℝ} (hm0 : 0 ≤ m)
    (hκK : d.K / d.Y d.r₀ 1 + 6 ≤ κ) (hκq : κ * q r 1 ≤ 1)
    (hm : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1), m ≤ d.Knorm r t)
    {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    (1 - κ * q r 1) * m ≤ d.Knorm (r + 1) u := by
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨le_rfl, h1e⟩
  have hy₀ : 0 < d.Y d.r₀ 1 := d.Y_pos d.r₀ le_rfl 1 h1mem
  have hq0 : 0 < q r 1 := q_pos one_pos r
  have hc0 : 0 ≤ d.K * q r 1 / d.Y d.r₀ 1 :=
    div_nonneg (mul_nonneg d.K_nonneg hq0.le) hy₀.le
  have hceq : d.K * q r 1 / d.Y d.r₀ 1 = d.K / d.Y d.r₀ 1 * q r 1 := by
    ring
  have hc_le : d.K * q r 1 / d.Y d.r₀ 1 ≤ (κ - 6) * q r 1 := by
    rw [hceq]
    exact mul_le_mul_of_nonneg_right (by linarith) hq0.le
  have hc1 : d.K * q r 1 / d.Y d.r₀ 1 ≤ 1 := by nlinarith
  have hstep := d.Knorm_min_step hr hm0 hy₀
    (fun t ht => d.Y_base_le hr ht) hm hc1 hu
  nlinarith [hstep,
    mul_nonneg hm0 (by nlinarith :
      (0 : ℝ) ≤ κ * q r 1 - d.K * q r 1 / d.Y d.r₀ 1 - 6 * q r 1),
    mul_nonneg (mul_nonneg hm0 hc0) hq0.le]

/-- **Positivity of `Ψ`** (paper: "The product of these factors is positive.
Thus `inf Ψ > 0`"): from a base depth `r₃ ≥ r₀` chosen (Archimedean, via
`q_one_tendsto_zero`) so that `κ·2q_{r₃}(1) ≤ 1/2`, the minimum recursion
keeps `K_{r₃+n} ≥ μ/2` for the compactness minimum `μ` of `K_{r₃}`, and the
lower bound survives the limit. -/
theorem iterationLimit_pos (d : IterationData)
    (hYder : ∀ r, d.r₀ ≤ r → ∀ x ∈ Set.Ico (1 : ℝ) (Real.exp 1),
      HasDerivWithinAt (d.Y (r + 1)) (a r x * (d.Y r x + d.η r x))
        (Set.Ioi x) x) :
    ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), 0 < d.iterationLimit u := by
  have h8 := d.r₀_ge
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨le_rfl, h1e⟩
  have hy₀ : 0 < d.Y d.r₀ 1 := d.Y_pos d.r₀ le_rfl 1 h1mem
  -- the loss coefficient `κ`
  obtain ⟨κ, hκ6, hκK⟩ : ∃ κ : ℝ, (6 : ℝ) ≤ κ ∧ d.K / d.Y d.r₀ 1 + 6 ≤ κ := by
    refine ⟨d.K / d.Y d.r₀ 1 + 6, ?_, le_rfl⟩
    have := div_nonneg d.K_nonneg hy₀.le
    linarith
  -- the base depth `r₃`: `q_{r₃}(1) < 1/(4κ)`
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (q_one_tendsto_zero.eventually_lt_const
      (show (0 : ℝ) < 1 / (4 * κ) by positivity))
  have hr₃r₀ : d.r₀ ≤ max N d.r₀ := le_max_right _ _
  have hq₃ : q (max N d.r₀) 1 < 1 / (4 * κ) := hN _ (le_max_left _ _)
  have hq₃pos : 0 < q (max N d.r₀) 1 := q_pos one_pos _
  have h2κq : κ * (2 * q (max N d.r₀) 1) ≤ 1 / 2 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * κ)] at hq₃
    nlinarith
  -- the compactness minimum `μ` of `K_{r₃}`
  obtain ⟨μ, hμpos, hμmin⟩ : ∃ μ : ℝ, 0 < μ ∧
      ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1), μ ≤ d.Knorm (max N d.r₀) t := by
    obtain ⟨x₀, hx₀mem, hx₀min⟩ := isCompact_Icc.exists_isMinOn
      (Set.nonempty_Icc.mpr h1e) (d.Knorm_continuousOn hr₃r₀)
    exact ⟨d.Knorm (max N d.r₀) x₀, d.Knorm_pos hr₃r₀ hx₀mem,
      fun t ht => isMinOn_iff.mp hx₀min t ht⟩
  -- the minimum recursion, with the explicit geometric loss budget
  have hrec : ∀ n : ℕ, ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      μ * (1 - κ * (2 * q (max N d.r₀) 1) * (1 - (1 / 2 : ℝ) ^ n))
        ≤ d.Knorm (max N d.r₀ + n) t := by
    intro n
    induction n with
    | zero =>
        intro t ht
        have h := hμmin t ht
        simpa using h
    | succ n ih =>
        intro t ht
        have hrn : d.r₀ ≤ max N d.r₀ + n := by omega
        have hqn_pos : 0 < q (max N d.r₀ + n) 1 := q_pos one_pos _
        have hqgeo : q (max N d.r₀ + n) 1
            ≤ (1 / 2 : ℝ) ^ n * q (max N d.r₀) 1 :=
          q_add_le_geometric le_rfl (by omega) n
        have hpow0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
        have hpow1 : (1 / 2 : ℝ) ^ n ≤ 1 :=
          pow_le_one₀ (by norm_num) (by norm_num)
        have hm0 : 0 ≤ μ * (1 - κ * (2 * q (max N d.r₀) 1)
            * (1 - (1 / 2 : ℝ) ^ n)) := by
          have hA0 : 0 ≤ κ * (2 * q (max N d.r₀) 1) :=
            mul_nonneg (by linarith) (by linarith)
          have hAx : κ * (2 * q (max N d.r₀) 1) * (1 - (1 / 2 : ℝ) ^ n)
              ≤ κ * (2 * q (max N d.r₀) 1) :=
            mul_le_of_le_one_right hA0 (by linarith)
          exact mul_nonneg hμpos.le (by linarith)
        have hκq : κ * q (max N d.r₀ + n) 1 ≤ 1 := by
          have h1 : κ * q (max N d.r₀ + n) 1
              ≤ κ * ((1 / 2 : ℝ) ^ n * q (max N d.r₀) 1) :=
            mul_le_mul_of_nonneg_left hqgeo (by linarith)
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ κ)
            hq₃pos.le) (by linarith : (0:ℝ) ≤ 1 - (1 / 2 : ℝ) ^ n)]
        have hstep := d.Knorm_min_step_normalized hrn hm0 hκK hκq ih ht
        rw [show max N d.r₀ + (n + 1) = max N d.r₀ + n + 1 by omega]
        refine le_trans ?_ hstep
        -- `m_{n+1} ≤ (1 − κ q_{r₃+n}(1))·m_n`
        rw [pow_succ]
        nlinarith [mul_nonneg (mul_nonneg hμpos.le (by linarith : (0:ℝ) ≤ κ))
            (by linarith [hqgeo] :
              (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n * q (max N d.r₀) 1
                - q (max N d.r₀ + n) 1),
          mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hμpos.le
            (by linarith : (0:ℝ) ≤ κ)) (by linarith : (0:ℝ) ≤ κ)) hqn_pos.le)
            hq₃pos.le) (by linarith : (0:ℝ) ≤ 1 - (1 / 2 : ℝ) ^ n)]
  -- the uniform positive floor `μ/2`
  have hlower : ∀ n : ℕ, ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      μ / 2 ≤ d.Knorm (max N d.r₀ + n) t := by
    intro n t ht
    have h := hrec n t ht
    have hpow0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
    have hA0 : 0 ≤ κ * (2 * q (max N d.r₀) 1) :=
      mul_nonneg (by linarith) (by linarith [hq₃pos])
    nlinarith [mul_nonneg hμpos.le (mul_nonneg hA0 hpow0),
      mul_nonneg hμpos.le (by linarith :
        (0 : ℝ) ≤ 1 / 2 - κ * (2 * q (max N d.r₀) 1))]
  -- pass to the limit
  intro u hu
  have htendsto := d.tendsto_Knorm_iterationLimit hYder hu
  have hge : μ / 2 ≤ d.iterationLimit u := by
    refine ge_of_tendsto htendsto ?_
    rw [Filter.eventually_atTop]
    refine ⟨max N d.r₀, fun r hr => ?_⟩
    have h := hlower (r - max N d.r₀) u hu
    rwa [Nat.add_sub_cancel' hr] at h
  linarith

/-! ## Step F: the packaged iteration lemma -/

/-- Paper **`lem:iteration-endpoint-matching`**
(eq. `iteration-endpoint-conclusion`): there is a positive continuous
`Ψ : [1, e] → (0, ∞)` with `Ψ(1) = Ψ(e)` such that, uniformly on `[1, e]`
and for all `r ≥ r₁ = r₀ + 1`, `|K_r(u) − Ψ(u)| ≤ C·q_r(u)` — i.e.
`Y_r(u) = J_r(u)(Ψ(u) + O(q_r(u)))` with `q_r = 1/(E_{r-3}E_{r-4})`, which
is the paper's error term `O(1/(E_{r-3}(u)E_{r-4}(u)))`.

The witness is the named `IterationData.iterationLimit`; prefer the def-based
API (`iterationLimit_continuousOn`, `iterationLimit_pos`,
`iterationLimit_endpoint`, `abs_Knorm_sub_iterationLimit_le`) downstream. -/
theorem iteration_endpoint_matching (d : IterationData)
    (hYder : ∀ r, d.r₀ ≤ r → ∀ x ∈ Set.Ico (1 : ℝ) (Real.exp 1),
      HasDerivWithinAt (d.Y (r + 1)) (a r x * (d.Y r x + d.η r x))
        (Set.Ioi x) x) :
    ∃ Ψ : ℝ → ℝ, ContinuousOn Ψ (Set.Icc 1 (Real.exp 1))
      ∧ (∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), 0 < Ψ u)
      ∧ Ψ 1 = Ψ (Real.exp 1)
      ∧ ∃ (C : ℝ) (r₁ : ℕ), 0 ≤ C ∧ ∀ r, r₁ ≤ r →
          ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1),
            |d.Knorm r u - Ψ u| ≤ C * q r u :=
  ⟨d.iterationLimit, d.iterationLimit_continuousOn hYder,
    d.iterationLimit_pos hYder, d.iterationLimit_endpoint hYder,
    d.abs_Knorm_sub_iterationLimit_le hYder⟩

end IterationData

end Erdos320
