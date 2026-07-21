import Erdos320.Lemmas.IterationData

/-!
# One-step estimates of the iteration lemma (`lem:iteration-endpoint-matching`)

The single-depth estimates from the proof of the manuscript's iteration lemma
(`lem:iteration-endpoint-matching`), in the `IterationData` setting: everything
the closing contraction argument needs to advance from depth `r` to depth
`r + 1`, with **explicit constants** in place of the paper's `C₀`, `C₁`.

For `d : IterationData` and `d.r₀ ≤ r` (so `8 ≤ r`), on the phase interval
`[1, e] = Set.Icc 1 (Real.exp 1)`:

* **Integrability plumbing**: `IterationData.aY_integrable`,
  `IterationData.aη_integrable`, `IterationData.Y_integrand_integrable` (the
  recurrence integrand `a_r(Y_r + η_r)` on any subinterval of `[1, e]`), the
  glued transport identity `IterationData.Y_transport_sub` between two interior
  phases, and `IterationData.Knorm_continuousOn`.
* **eq. `normalized-transport`**: `IterationData.Knorm_transport`, the exact
  identity `K_{r+1}(u) = (J_{r+1}(1)K_r(e) + ∫₁ᵘ a_rJ_rK_r + ∫₁ᵘ a_rη_r) / J_{r+1}(u)`.
* **Sup recursion** (paper: `‖K_{r+1}‖_∞ ≤ ‖K_r‖_∞ + C₀q_r(1)`):
  `IterationData.Knorm_sup_step`, with `C₀ = d.K` — the forcing constant
  itself, no enlargement.
* **eq. `scalar-cauchy-bound`**: `IterationData.Knorm_diff_step`,
  `d_r ≤ 6M + K + 14λ_r ε_r + s_r` with `ε_r = 1/E_{r-5}(1)` (the paper's
  `d_r ≤ C₁(1 + M + s_r + ε_r λ_r)` with all constants explicit).  The shared
  numerator estimate is `IterationData.Knorm_diff_core`; the Tonelli/Fubini
  step of the paper is replaced by an integration-by-parts argument
  (`integral_aJ_tail_le`, constant `7` from `integral_J_D_le`).
* **eq. `scalar-endpoint-bound`**: `IterationData.Knorm_endpoint_step`,
  `s_{r+1} ≤ 6M + K + 7λ_r ε_r` — the paper's
  `s_{r+1} ≤ C₁(1 + M + ε_r λ_r)` with all constants explicit.  As in the
  paper's proof (its display `α_r(e)(K_r(e) − K_r(e)) = 0`), at `u = e`
  the endpoint-atom term of the decomposition vanishes *identically*
  (`K_r(e) − K_r(u)|_{u=e} = 0`), so the bound carries no `s_r`-dependence.
* **eq. `scalar-derivative-bound`** (in integral/Lipschitz form):
  `IterationData.Knorm_lipschitz_step`,
  `|K_{r+1}(u) − K_{r+1}(v)| ≤ (2d_r + 6M + 7K)·∫ᵥᵘ D_{r-2}`, i.e.
  `λ_{r+1} ≤ 2d_r + 6M + 7K` (the paper's `λ_{r+1} ≤ C₁(d_r + 1 + M)`).
  Since the `IterationData` package records the recurrence only in integral
  form, the pointwise differentiation of `K_{r+1} = Y_{r+1}/J_{r+1}` needs the
  *right-derivative* form of the recurrence as an explicit hypothesis
  (`hYder`); the intended instantiation `Y_r = H̄_r` supplies it at **every**
  phase with no exceptional set (`hasDerivWithinAt_Hbar_succ_Ioi`), which is
  strictly stronger than the paper's "absolutely continuous with a.e.
  derivative".  The mean-value machinery is Mathlib's one-sided fencing
  theorem `image_norm_le_of_norm_deriv_right_le_deriv_boundary`.

Paper vs. Lean:

* All Vinogradov constants of the closing estimates are explicit:
  `C₀ = K`, and the `(d_r, λ_r, s_r)` recursion reads
  `d_r ≤ 6M + K + 14λ_r ε_r + s_r`, `λ_{r+1} ≤ 2d_r + 6M + 7K`,
  `s_{r+1} ≤ 6M + K + 7λ_r ε_r` — exactly the coupling shape the paper's
  contraction consumes (`ε_r → 0` geometric).
* The paper's Tonelli exchange in eq. `averaging-localization` is realized
  measure-free, by integration by parts against the primitive
  `Φ(t) = ∫₁ᵗ a_rJ_r` and the subprobability bound `Φ ≤ J_{r+1}` (`mass_le`).
-/

namespace Erdos320

open MeasureTheory

/-! ## Small interval and positivity helpers -/

/-- Any subinterval `[[v, u]]` with both endpoints in the phase interval
`[1, e]` stays inside it; feeds `ContinuousOn.intervalIntegrable` and
`IntervalIntegrable.mono_set` below. -/
theorem uIcc_subset_phaseInterval {v u : ℝ}
    (hv : v ∈ Set.Icc (1 : ℝ) (Real.exp 1))
    (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    Set.uIcc v u ⊆ Set.Icc (1 : ℝ) (Real.exp 1) := by
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  rw [← Set.uIcc_of_le h1e]
  exact Set.uIcc_subset_uIcc (by rwa [Set.uIcc_of_le h1e])
    (by rwa [Set.uIcc_of_le h1e])

/-- A Lipschitz-in-`∫D_j` constant on `[1, e]` is automatically nonnegative
(the weight `D_j` has strictly positive integral over `[1, e]`).  Extracts
the sign information implicit in the paper's `λ_r = ess sup |K_r'|/D_{r-3}`
and `s_r = |K_r(e) − K_r(1)|/q_r(1)` normalizations. -/
theorem nonneg_of_lipschitz_D_weight {f : ℝ → ℝ} {lam : ℝ} {j : ℕ}
    (hlam : ∀ x ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      ∀ y ∈ Set.Icc (1 : ℝ) (Real.exp 1), y ≤ x →
        |f x - f y| ≤ lam * ∫ t in y..x, D j t) : 0 ≤ lam := by
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hI : 0 < ∫ t in (1 : ℝ)..(Real.exp 1), D j t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_D j).intervalIntegrable 1 (Real.exp 1))
      (fun t ht => D_pos (lt_trans one_pos ht.1) j)
      (by linarith [Real.exp_one_gt_d9])
  have h := hlam (Real.exp 1) ⟨h1e, le_rfl⟩ 1 ⟨le_rfl, h1e⟩ h1e
  nlinarith [abs_nonneg (f (Real.exp 1) - f 1)]

/-- `a_r ≤ J_{r+1}` for `r ≥ 2`, `u ≥ 1` (via `a_r = D_{r+1}/u ≤ D_{r+1}`):
the crude comparison absorbing the `1/u` in the pointwise derivative bounds
of eq. `scalar-derivative-bound`. -/
theorem a_le_J_succ {r : ℕ} (hr : 2 ≤ r) {x : ℝ} (hx : 1 ≤ x) :
    a r x ≤ J (r + 1) x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have h1 : a r x = D (r + 1) x / x := a_eq_D_succ_div hx0.ne' hr
  have h2 : D (r + 1) x / x ≤ D (r + 1) x := div_le_self (D_pos hx0 _).le hx
  rw [h1]
  exact h2.trans (D_le_J hx0 (r + 1))

/-- `a_r J_r q_r ≤ 2 D_{r-2} J_{r+1}` for `r ≥ 5`, `u ≥ 1`: the pointwise
comparison behind the paper's `(a_rJ_r/J_{r+1})·q_r ≤ C₁D_rq_r = C₁D_{r-2}`
in the proof of eq. `scalar-derivative-bound` (uses `J_r ≤ 2D_r`,
`D_r q_r = D_{r-2}`, and `a_r ≤ J_{r+1}`). -/
theorem a_mul_J_mul_q_le {r : ℕ} (hr : 5 ≤ r) {x : ℝ} (hx : 1 ≤ x) :
    a r x * J r x * q r x ≤ 2 * (D (r - 2) x * J (r + 1) x) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hqD : q r x * D r x = D (r - 2) x := by
    rw [q_eq_D_ratio hx0 (by omega), div_mul_cancel₀ _ (D_pos hx0 r).ne']
  have haJ : a r x ≤ J (r + 1) x := a_le_J_succ (by omega) hx
  calc a r x * J r x * q r x
      ≤ a r x * (2 * D r x) * q r x := by
        have h := mul_le_mul_of_nonneg_left (J_le_two_D hx r) (a_pos r x).le
        exact mul_le_mul_of_nonneg_right h (q_pos hx0 r).le
    _ = 2 * (a r x * (q r x * D r x)) := by ring
    _ = 2 * (a r x * D (r - 2) x) := by rw [hqD]
    _ ≤ 2 * (D (r - 2) x * J (r + 1) x) := by
        have h := mul_le_mul_of_nonneg_right haJ (D_pos hx0 (r - 2)).le
        nlinarith

/-! ## The integration-by-parts replacement for the paper's Tonelli step -/

/-- **eq. `averaging-localization`, continuous localization term** (the
paper's Tonelli exchange, realized by integration by parts): for `r ≥ 6`
and `u ∈ [1, e]`,
`∫₁ᵘ a_r(t)J_r(t)·(∫ₜᵘ D_{r-3}) dt = ∫₁ᵘ (∫₁^σ a_rJ_r)·D_{r-3}(σ) dσ
  ≤ ∫₁ᵘ J_{r+1}·D_{r-3} ≤ 7·J_{r+1}(u)w_r(u)`,
using the primitive `Φ(t) = ∫₁ᵗ a_rJ_r ≤ J_{r+1}(t)` (`mass_le`) and
`integral_J_D_le`. -/
theorem integral_aJ_tail_le {r : ℕ} (hr : 6 ≤ r) {u : ℝ}
    (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    (∫ t in (1 : ℝ)..u, a r t * J r t * ∫ σ in t..u, D (r - 3) σ)
      ≤ 7 * (J (r + 1) u * w r u) := by
  -- derivatives of the two primitives
  have hGd : ∀ t : ℝ,
      HasDerivAt (fun x : ℝ => ∫ σ in x..u, D (r - 3) σ) (-(D (r - 3) t)) t := by
    intro t
    have h := (((continuous_D (r - 3)).integral_hasStrictDerivAt u t).hasDerivAt).fun_neg
    have hfun : (fun x : ℝ => -∫ σ in u..x, D (r - 3) σ)
        = fun x : ℝ => ∫ σ in x..u, D (r - 3) σ := by
      funext x
      rw [intervalIntegral.integral_symm u x]
    rwa [hfun] at h
  have hΦd : ∀ t : ℝ,
      HasDerivAt (fun x : ℝ => ∫ σ in (1 : ℝ)..x, a r σ * J r σ)
        (a r t * J r t) t := fun t =>
    (((continuous_a r).mul (continuous_J r)).integral_hasStrictDerivAt 1 t).hasDerivAt
  have hGcont : Continuous fun x : ℝ => ∫ σ in x..u, D (r - 3) σ :=
    continuous_iff_continuousAt.mpr fun t => (hGd t).continuousAt
  have hΦcont : Continuous fun x : ℝ => ∫ σ in (1 : ℝ)..x, a r σ * J r σ :=
    continuous_iff_continuousAt.mpr fun t => (hΦd t).continuousAt
  -- fundamental theorem of calculus for the product of the primitives
  have hint : Continuous fun t : ℝ =>
      a r t * J r t * (∫ σ in t..u, D (r - 3) σ)
        + (∫ σ in (1 : ℝ)..t, a r σ * J r σ) * -(D (r - 3) t) :=
    (((continuous_a r).mul (continuous_J r)).mul hGcont).add
      (hΦcont.mul (continuous_D (r - 3)).neg)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => (∫ σ in (1 : ℝ)..x, a r σ * J r σ) * ∫ σ in x..u, D (r - 3) σ)
    (fun t _ => (hΦd t).mul (hGd t)) (hint.intervalIntegrable 1 u)
  have hzero : (∫ t in (1 : ℝ)..u,
      (a r t * J r t * (∫ σ in t..u, D (r - 3) σ)
        + (∫ σ in (1 : ℝ)..t, a r σ * J r σ) * -(D (r - 3) t))) = 0 := by
    rw [hFTC]
    simp
  have hIaJG : IntervalIntegrable
      (fun t => a r t * J r t * ∫ σ in t..u, D (r - 3) σ) volume 1 u :=
    ((((continuous_a r).mul (continuous_J r)).mul hGcont)).intervalIntegrable 1 u
  have hIΦD : IntervalIntegrable
      (fun t => (∫ σ in (1 : ℝ)..t, a r σ * J r σ) * -(D (r - 3) t)) volume 1 u :=
    (hΦcont.mul (continuous_D (r - 3)).neg).intervalIntegrable 1 u
  rw [intervalIntegral.integral_add hIaJG hIΦD] at hzero
  have hneg : (∫ t in (1 : ℝ)..u, (∫ σ in (1 : ℝ)..t, a r σ * J r σ) * -(D (r - 3) t))
      = -∫ t in (1 : ℝ)..u, (∫ σ in (1 : ℝ)..t, a r σ * J r σ) * D (r - 3) t := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hneg] at hzero
  have heq : (∫ t in (1 : ℝ)..u, a r t * J r t * ∫ σ in t..u, D (r - 3) σ)
      = ∫ t in (1 : ℝ)..u, (∫ σ in (1 : ℝ)..t, a r σ * J r σ) * D (r - 3) t := by
    linarith
  rw [heq]
  -- `Φ(σ) ≤ J_{r+1}(σ)` and the weighted integral bound `integral_J_D_le`
  refine le_trans (intervalIntegral.integral_mono_on hu.1
    ((hΦcont.mul (continuous_D (r - 3))).intervalIntegrable 1 u)
    (((continuous_J (r + 1)).mul (continuous_D (r - 3))).intervalIntegrable 1 u)
    fun t ht => ?_) (integral_J_D_le hr hu)
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
  have hmass := mass_le (show 4 ≤ r by omega) ht.1
  have hJ1 : (0 : ℝ) < J (r + 1) 1 := J_pos one_pos (r + 1)
  exact mul_le_mul_of_nonneg_right (by linarith) (D_pos ht0 (r - 3)).le

namespace IterationData

/-! ## Integrability plumbing (deliverable 1) -/

/-- The continuous half `a_r Y_r` of the recurrence integrand is interval
integrable on any subinterval of `[1, e]` (`Y_r` is only continuous *on*
`[1, e]`, hence the endpoint hypotheses). -/
theorem aY_integrable (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r) {v u : ℝ}
    (hv : v ∈ Set.Icc (1 : ℝ) (Real.exp 1))
    (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    IntervalIntegrable (fun t => a r t * d.Y r t) volume v u :=
  (((continuous_a r).continuousOn).mul
    ((d.Y_cont r hr).mono (uIcc_subset_phaseInterval hv hu))).intervalIntegrable

/-- The forcing half `a_r η_r` of the recurrence integrand is interval
integrable on any subinterval of `[1, e]` (restriction of the packaged
`η_integrable` via `IntervalIntegrable.mono_set`). -/
theorem aη_integrable (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r) {v u : ℝ}
    (hv : v ∈ Set.Icc (1 : ℝ) (Real.exp 1))
    (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    IntervalIntegrable (fun t => a r t * d.η r t) volume v u := by
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  exact (d.η_integrable r hr).mono_set
    (by rw [Set.uIcc_of_le h1e]; exact uIcc_subset_phaseInterval hv hu)

/-- The full recurrence integrand `a_r(Y_r + η_r)` of
`lem:iteration-endpoint-matching` is interval integrable on any subinterval
of `[1, e]`. -/
theorem Y_integrand_integrable (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r)
    {v u : ℝ} (hv : v ∈ Set.Icc (1 : ℝ) (Real.exp 1))
    (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    IntervalIntegrable (fun t => a r t * (d.Y r t + d.η r t)) volume v u := by
  have hfun : (fun t => a r t * (d.Y r t + d.η r t))
      = fun t => a r t * d.Y r t + a r t * d.η r t :=
    funext fun t => mul_add _ _ _
  rw [hfun]
  exact (d.aY_integrable hr hv hu).add (d.aη_integrable hr hv hu)

/-- Transport identity between two interior phases: for `v, u ∈ [1, e]`,
`Y_{r+1}(u) − Y_{r+1}(v) = ∫ᵥᵘ a_r(Y_r + η_r)` — the difference of the two
endpoint-`1` identities of the `IterationData` package, glued with
`integral_add_adjacent_intervals`. -/
theorem Y_transport_sub (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r) {v u : ℝ}
    (hv : v ∈ Set.Icc (1 : ℝ) (Real.exp 1))
    (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    d.Y (r + 1) u - d.Y (r + 1) v
      = ∫ t in v..u, a r t * (d.Y r t + d.η r t) := by
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨le_rfl, h1e⟩
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (d.Y_integrand_integrable hr h1mem hv) (d.Y_integrand_integrable hr hv hu)
  have htu := d.Y_transport r hr u hu
  have htv := d.Y_transport r hr v hv
  linarith

/-- The normalized iterate `K_r = Y_r/J_r` is continuous on `[1, e]`
(`J_r` never vanishes there). -/
theorem Knorm_continuousOn (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r) :
    ContinuousOn (d.Knorm r) (Set.Icc (1 : ℝ) (Real.exp 1)) := by
  show ContinuousOn (fun t => d.Y r t / J r t) (Set.Icc (1 : ℝ) (Real.exp 1))
  exact (d.Y_cont r hr).div (continuous_J r).continuousOn
    fun t ht => (J_pos (lt_of_lt_of_le one_pos ht.1) r).ne'

/-! ## eq. `normalized-transport` (deliverable 2) -/

/-- **eq. `normalized-transport`**: the exact identity
`K_{r+1}(u) = (J_{r+1}(1)·K_r(e) + ∫₁ᵘ a_rJ_rK_r + ∫₁ᵘ a_rη_r)/J_{r+1}(u)`,
from the integral recurrence (`Y_transport`), the endpoint matching
`Y_{r+1}(1) = Y_r(e) = J_{r+1}(1)K_r(e)` (`Y_endpoint`, `J_exp_one`), and the
pointwise rewrite `a_rJ_rK_r = a_rY_r`. -/
theorem Knorm_transport (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r) {u : ℝ}
    (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    d.Knorm (r + 1) u
      = (J (r + 1) 1 * d.Knorm r (Real.exp 1)
          + (∫ t in (1 : ℝ)..u, a r t * J r t * d.Knorm r t)
          + ∫ t in (1 : ℝ)..u, a r t * d.η r t) / J (r + 1) u := by
  have h8 : 8 ≤ r := d.r₀_ge.trans hr
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨le_rfl, h1e⟩
  -- the endpoint atom is `Y_{r+1}(1)`
  have hatom : J (r + 1) 1 * d.Knorm r (Real.exp 1) = d.Y (r + 1) 1 := by
    have hJe : J r (Real.exp 1) = J (r + 1) 1 := J_exp_one (by omega)
    have hJ1 : J (r + 1) 1 ≠ 0 := (J_pos one_pos (r + 1)).ne'
    show J (r + 1) 1 * (d.Y r (Real.exp 1) / J r (Real.exp 1)) = d.Y (r + 1) 1
    rw [hJe, mul_comm, div_mul_cancel₀ _ hJ1]
    exact d.Y_endpoint r hr
  -- `a_r J_r K_r = a_r Y_r` pointwise on `[1, u]`
  have hKJint : (∫ t in (1 : ℝ)..u, a r t * J r t * d.Knorm r t)
      = ∫ t in (1 : ℝ)..u, a r t * d.Y r t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hu.1] at ht
    have hJt : J r t ≠ 0 := (J_pos (lt_of_lt_of_le one_pos ht.1) r).ne'
    show a r t * J r t * (d.Y r t / J r t) = a r t * d.Y r t
    have h : J r t * (d.Y r t / J r t) = d.Y r t := by
      field_simp
    rw [mul_assoc, h]
  -- split the transported integral
  have hsplit : (∫ t in (1 : ℝ)..u, a r t * (d.Y r t + d.η r t))
      = (∫ t in (1 : ℝ)..u, a r t * d.Y r t)
        + ∫ t in (1 : ℝ)..u, a r t * d.η r t := by
    rw [← intervalIntegral.integral_add (d.aY_integrable hr h1mem hu)
      (d.aη_integrable hr h1mem hu)]
    exact intervalIntegral.integral_congr fun t _ => mul_add _ _ _
  -- assemble the numerator
  have hnum : J (r + 1) 1 * d.Knorm r (Real.exp 1)
      + (∫ t in (1 : ℝ)..u, a r t * J r t * d.Knorm r t)
      + (∫ t in (1 : ℝ)..u, a r t * d.η r t) = d.Y (r + 1) u := by
    have htr := d.Y_transport r hr u hu
    rw [hsplit] at htr
    rw [hatom, hKJint]
    linarith
  rw [hnum]
  rfl

/-! ## Sup recursion (deliverable 3) -/

/-- **Sup recursion** (paper: `‖K_{r+1}‖_∞ ≤ ‖K_r‖_∞ + C₀ q_r(1)`, first
display after eq. `forcing-localization`), with the explicit constant
`C₀ = d.K`: from a uniform bound `M` at depth `r`,
`|K_{r+1}(u)| ≤ M + K·q_r(1)` on all of `[1, e]`.  Subprobability of the
transport measure (`mass_le`) plus the forcing bound (`forcing_le`). -/
theorem Knorm_sup_step (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r) (M : ℝ)
    (hM : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1), |d.Knorm r t| ≤ M)
    {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    |d.Knorm (r + 1) u| ≤ M + d.K * q r 1 := by
  have h8 : 8 ≤ r := d.r₀_ge.trans hr
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨le_rfl, h1e⟩
  have hemem : Real.exp 1 ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨h1e, le_rfl⟩
  have hu1 : (1 : ℝ) ≤ u := hu.1
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
  have hJu : (0 : ℝ) < J (r + 1) u := J_pos hu0 (r + 1)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 1 h1mem)
  -- forcing term
  have hforce := forcing_le (show 6 ≤ r by omega) hu d.K_nonneg (d.η r)
    (d.η_bound r hr) (d.aη_integrable hr h1mem hu)
  -- the `a_rJ_rK_r` integral against the sup bound
  have hsubIcc := uIcc_subset_phaseInterval h1mem hu
  have haJK_int : IntervalIntegrable
      (fun t => a r t * J r t * d.Knorm r t) volume 1 u :=
    (((continuous_a r).continuousOn.mul (continuous_J r).continuousOn).mul
      ((d.Knorm_continuousOn hr).mono hsubIcc)).intervalIntegrable
  have hKJabs : |∫ t in (1 : ℝ)..u, a r t * J r t * d.Knorm r t|
      ≤ M * ∫ t in (1 : ℝ)..u, a r t * J r t := by
    have habs := intervalIntegral.abs_integral_le_integral_abs
      (f := fun t => a r t * J r t * d.Knorm r t) (μ := volume) hu1
    have hpt : ∀ t ∈ Set.Icc (1 : ℝ) u,
        |a r t * J r t * d.Knorm r t| ≤ M * (a r t * J r t) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
      have htmem : t ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨ht.1, ht.2.trans hu.2⟩
      have haJ : (0 : ℝ) < a r t * J r t := mul_pos (a_pos r t) (J_pos ht0 r)
      rw [abs_mul, abs_of_pos haJ]
      calc a r t * J r t * |d.Knorm r t|
          ≤ a r t * J r t * M := mul_le_mul_of_nonneg_left (hM t htmem) haJ.le
        _ = M * (a r t * J r t) := mul_comm _ _
    have hint := intervalIntegral.integral_mono_on hu1 haJK_int.abs
      ((((continuous_a r).mul (continuous_J r)).const_mul M).intervalIntegrable 1 u)
      hpt
    rw [intervalIntegral.integral_const_mul] at hint
    exact habs.trans hint
  -- mass and gap monotonicity
  have hmass := mass_le (show 4 ≤ r by omega) hu1
  have hqu : q r u ≤ q r 1 :=
    q_antitoneOn r (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu1) hu1
  -- assemble
  rw [Knorm_transport d hr hu, abs_div, abs_of_pos hJu, div_le_iff₀ hJu]
  have hatomabs : |J (r + 1) 1 * d.Knorm r (Real.exp 1)| ≤ J (r + 1) 1 * M := by
    rw [abs_mul, abs_of_pos (J_pos one_pos (r + 1))]
    exact mul_le_mul_of_nonneg_left (hM _ hemem) (J_pos one_pos (r + 1)).le
  have htri1 := abs_add_le
    (J (r + 1) 1 * d.Knorm r (Real.exp 1)
      + ∫ t in (1 : ℝ)..u, a r t * J r t * d.Knorm r t)
    (∫ t in (1 : ℝ)..u, a r t * d.η r t)
  have htri2 := abs_add_le (J (r + 1) 1 * d.Knorm r (Real.exp 1))
    (∫ t in (1 : ℝ)..u, a r t * J r t * d.Knorm r t)
  have hmassM := mul_le_mul_of_nonneg_left hmass hM0
  have hqK := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hqu hJu.le) d.K_nonneg
  nlinarith

/-! ## The shared numerator estimate for eq. `scalar-cauchy-bound` and
eq. `scalar-endpoint-bound` (deliverables 4 and 6) -/

/-- **Core difference estimate** (proof of eq. `scalar-cauchy-bound`, all
terms except the endpoint atom): in cleared form,
`|K_{r+1}(u) − K_r(u)|·J_{r+1}(u) ≤ J_{r+1}(1)·|K_r(e) − K_r(u)|
  + (6M + K + 7λε_r)·J_{r+1}(u)q_r(u)`,
where `ε_r = 1/E_{r-5}(1)`.  The three interior contributions are: the
continuous localization term (`7λε_r`, via `integral_aJ_tail_le`), the
forcing term (`K`, via `forcing_le`), and the missing-mass term (`6M`, via
`missing_mass_le`). -/
theorem Knorm_diff_core (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r)
    (M lam : ℝ)
    (hM : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1), |d.Knorm r t| ≤ M)
    (hlam : ∀ x ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      ∀ y ∈ Set.Icc (1 : ℝ) (Real.exp 1), y ≤ x →
        |d.Knorm r x - d.Knorm r y| ≤ lam * ∫ t in y..x, D (r - 3) t)
    {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    |d.Knorm (r + 1) u - d.Knorm r u| * J (r + 1) u
      ≤ J (r + 1) 1 * |d.Knorm r (Real.exp 1) - d.Knorm r u|
        + (6 * M + d.K + 7 * lam / E (r - 5) 1) * (J (r + 1) u * q r u) := by
  have h8 : 8 ≤ r := d.r₀_ge.trans hr
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨le_rfl, h1e⟩
  have hu1 : (1 : ℝ) ≤ u := hu.1
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
  have hJu : (0 : ℝ) < J (r + 1) u := J_pos hu0 (r + 1)
  have hlam0 : 0 ≤ lam := nonneg_of_lipschitz_D_weight hlam
  -- cleared transport identity
  have hKmul : d.Knorm (r + 1) u * J (r + 1) u
      = J (r + 1) 1 * d.Knorm r (Real.exp 1)
        + (∫ t in (1 : ℝ)..u, a r t * J r t * d.Knorm r t)
        + ∫ t in (1 : ℝ)..u, a r t * d.η r t := by
    rw [Knorm_transport d hr hu]
    exact div_mul_cancel₀ _ hJu.ne'
  -- split of the `J`-transport
  have haJ_int : IntervalIntegrable (fun t => a r t * J r t) volume 1 u :=
    ((continuous_a r).mul (continuous_J r)).intervalIntegrable 1 u
  have haR_int : IntervalIntegrable (fun t => a r t * Rdefect r t) volume 1 u :=
    ((continuous_a r).mul (continuous_Rdefect (show 3 ≤ r by omega))).intervalIntegrable 1 u
  have hJtr : J (r + 1) u = J (r + 1) 1
      + ((∫ t in (1 : ℝ)..u, a r t * J r t)
        + ∫ t in (1 : ℝ)..u, a r t * Rdefect r t) := by
    have h := J_transport (show 4 ≤ r by omega) u
    have hsp : (∫ t in (1 : ℝ)..u, a r t * (J r t + Rdefect r t))
        = (∫ t in (1 : ℝ)..u, a r t * J r t)
          + ∫ t in (1 : ℝ)..u, a r t * Rdefect r t := by
      rw [← intervalIntegral.integral_add haJ_int haR_int]
      exact intervalIntegral.integral_congr fun t _ => mul_add _ _ _
    linarith
  -- centered integrand
  have hsubIcc := uIcc_subset_phaseInterval h1mem hu
  have haJK_int : IntervalIntegrable
      (fun t => a r t * J r t * d.Knorm r t) volume 1 u :=
    (((continuous_a r).continuousOn.mul (continuous_J r).continuousOn).mul
      ((d.Knorm_continuousOn hr).mono hsubIcc)).intervalIntegrable
  have hsub : (∫ t in (1 : ℝ)..u, a r t * J r t * (d.Knorm r t - d.Knorm r u))
      = (∫ t in (1 : ℝ)..u, a r t * J r t * d.Knorm r t)
        - (∫ t in (1 : ℝ)..u, a r t * J r t) * d.Knorm r u := by
    rw [← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_sub haJK_int (haJ_int.mul_const _)]
    exact intervalIntegral.integral_congr fun t _ => by ring
  -- the key decomposition of the difference
  have hkey : (d.Knorm (r + 1) u - d.Knorm r u) * J (r + 1) u
      = J (r + 1) 1 * (d.Knorm r (Real.exp 1) - d.Knorm r u)
        + (∫ t in (1 : ℝ)..u, a r t * J r t * (d.Knorm r t - d.Knorm r u))
        + (∫ t in (1 : ℝ)..u, a r t * d.η r t)
        - (∫ t in (1 : ℝ)..u, a r t * Rdefect r t) * d.Knorm r u := by
    rw [sub_mul, hKmul, hsub, hJtr]
    ring
  -- continuity of the tail primitive
  have hGcont : Continuous fun t : ℝ => ∫ σ in t..u, D (r - 3) σ := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have h := (((continuous_D (r - 3)).integral_hasStrictDerivAt u t).hasDerivAt).fun_neg
    have hfun : (fun x : ℝ => -∫ σ in u..x, D (r - 3) σ)
        = fun x : ℝ => ∫ σ in x..u, D (r - 3) σ := by
      funext x
      rw [intervalIntegral.integral_symm u x]
    rw [hfun] at h
    exact h.continuousAt
  -- (ii) the continuous localization term
  have hT2 : |∫ t in (1 : ℝ)..u, a r t * J r t * (d.Knorm r t - d.Knorm r u)|
      ≤ 7 * lam / E (r - 5) 1 * (J (r + 1) u * q r u) := by
    have habs := intervalIntegral.abs_integral_le_integral_abs
      (f := fun t => a r t * J r t * (d.Knorm r t - d.Knorm r u)) (μ := volume) hu1
    have hpt : ∀ t ∈ Set.Icc (1 : ℝ) u,
        |a r t * J r t * (d.Knorm r t - d.Knorm r u)|
          ≤ lam * (a r t * J r t * ∫ σ in t..u, D (r - 3) σ) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
      have htmem : t ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨ht.1, ht.2.trans hu.2⟩
      have haJ : (0 : ℝ) < a r t * J r t := mul_pos (a_pos r t) (J_pos ht0 r)
      rw [abs_mul, abs_of_pos haJ]
      have hK := hlam u hu t htmem ht.2
      rw [abs_sub_comm] at hK
      calc a r t * J r t * |d.Knorm r t - d.Knorm r u|
          ≤ a r t * J r t * (lam * ∫ σ in t..u, D (r - 3) σ) :=
            mul_le_mul_of_nonneg_left hK haJ.le
        _ = lam * (a r t * J r t * ∫ σ in t..u, D (r - 3) σ) := by ring
    have hint1 : IntervalIntegrable
        (fun t => |a r t * J r t * (d.Knorm r t - d.Knorm r u)|) volume 1 u :=
      ((((continuous_a r).continuousOn.mul (continuous_J r).continuousOn).mul
        (((d.Knorm_continuousOn hr).mono hsubIcc).sub continuousOn_const)).abs).intervalIntegrable
    have hint2 : IntervalIntegrable
        (fun t => lam * (a r t * J r t * ∫ σ in t..u, D (r - 3) σ)) volume 1 u :=
      ((((continuous_a r).mul (continuous_J r)).mul hGcont).const_mul lam).intervalIntegrable 1 u
    have hmono := intervalIntegral.integral_mono_on hu1 hint1 hint2 hpt
    have htail := integral_aJ_tail_le (show 6 ≤ r by omega) hu
    have hE1 : (0 : ℝ) < E (r - 5) 1 := E_pos_of_one_le (by omega) 1
    have hE1u : E (r - 5) 1 ≤ E (r - 5) u := E_mono (r - 5) hu1
    have hwq : w r u ≤ q r u / E (r - 5) 1 := by
      rw [w_eq_q_div]
      gcongr
      exact (q_pos hu0 r).le
    rw [intervalIntegral.integral_const_mul] at hmono
    calc |∫ t in (1 : ℝ)..u, a r t * J r t * (d.Knorm r t - d.Knorm r u)|
        ≤ ∫ t in (1 : ℝ)..u, |a r t * J r t * (d.Knorm r t - d.Knorm r u)| := habs
      _ ≤ lam * ∫ t in (1 : ℝ)..u, a r t * J r t * ∫ σ in t..u, D (r - 3) σ := hmono
      _ ≤ lam * (7 * (J (r + 1) u * w r u)) :=
          mul_le_mul_of_nonneg_left htail hlam0
      _ ≤ lam * (7 * (J (r + 1) u * (q r u / E (r - 5) 1))) := by
          have := mul_le_mul_of_nonneg_left hwq hJu.le
          nlinarith
      _ = 7 * lam / E (r - 5) 1 * (J (r + 1) u * q r u) := by
          field_simp
  -- (iii) the forcing term
  have hT4 := forcing_le (show 6 ≤ r by omega) hu d.K_nonneg (d.η r)
    (d.η_bound r hr) (d.aη_integrable hr h1mem hu)
  -- (iv) the missing-mass term
  have haR_nonneg : 0 ≤ ∫ t in (1 : ℝ)..u, a r t * Rdefect r t :=
    intervalIntegral.integral_nonneg hu1 fun t ht =>
      mul_nonneg (a_pos r t).le (Rdefect_nonneg (lt_of_lt_of_le one_pos ht.1) r)
  have hT3 : |(∫ t in (1 : ℝ)..u, a r t * Rdefect r t) * d.Knorm r u|
      ≤ 6 * M * (J (r + 1) u * q r u) := by
    rw [abs_mul, abs_of_nonneg haR_nonneg]
    calc (∫ t in (1 : ℝ)..u, a r t * Rdefect r t) * |d.Knorm r u|
        ≤ 6 * (J (r + 1) u * q r u) * M := by
          refine mul_le_mul (missing_mass_le (show 6 ≤ r by omega) hu1)
            (hM u hu) (abs_nonneg _) ?_
          have := q_pos hu0 r
          nlinarith
      _ = 6 * M * (J (r + 1) u * q r u) := by ring
  -- combine the four pieces
  have hcast : |d.Knorm (r + 1) u - d.Knorm r u| * J (r + 1) u
      = |(d.Knorm (r + 1) u - d.Knorm r u) * J (r + 1) u| := by
    rw [abs_mul, abs_of_pos hJu]
  rw [hcast, hkey]
  have htriA := abs_add_le
    (J (r + 1) 1 * (d.Knorm r (Real.exp 1) - d.Knorm r u)
      + ∫ t in (1 : ℝ)..u, a r t * J r t * (d.Knorm r t - d.Knorm r u))
    (∫ t in (1 : ℝ)..u, a r t * d.η r t)
  have htriB := abs_add_le
    (J (r + 1) 1 * (d.Knorm r (Real.exp 1) - d.Knorm r u))
    (∫ t in (1 : ℝ)..u, a r t * J r t * (d.Knorm r t - d.Knorm r u))
  have htriC := abs_sub
    (J (r + 1) 1 * (d.Knorm r (Real.exp 1) - d.Knorm r u)
      + (∫ t in (1 : ℝ)..u, a r t * J r t * (d.Knorm r t - d.Knorm r u))
      + ∫ t in (1 : ℝ)..u, a r t * d.η r t)
    ((∫ t in (1 : ℝ)..u, a r t * Rdefect r t) * d.Knorm r u)
  have hatomabs : |J (r + 1) 1 * (d.Knorm r (Real.exp 1) - d.Knorm r u)|
      = J (r + 1) 1 * |d.Knorm r (Real.exp 1) - d.Knorm r u| := by
    rw [abs_mul, abs_of_pos (J_pos one_pos (r + 1))]
  linarith

/-! ## eq. `scalar-cauchy-bound` (deliverable 4) -/

/-- **eq. `scalar-cauchy-bound`** with explicit constants: under a sup bound
`M`, a Lipschitz-in-`∫D_{r-3}` bound `λ_r = lam`, and an endpoint-jump bound
`s_r = s` at depth `r`,
`|K_{r+1}(u) − K_r(u)| ≤ (6M + K + 14·lam·ε_r + s)·q_r(u)` uniformly on
`[1, e]`, where `ε_r = 1/E_{r-5}(1)` — the paper's
`d_r ≤ C₁(1 + M + s_r + ε_rλ_r)`.  The endpoint atom is split as
`|K_r(e) − K_r(u)| ≤ s·q_r(1) + lam·∫₁ᵘ D_{r-3}` and absorbed via
`endpoint_mass_le` (coefficient `s`) and `endpoint_D_int` (a second `7λε_r`,
whence `14` in total). -/
theorem Knorm_diff_step (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r)
    (M lam s : ℝ)
    (hM : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1), |d.Knorm r t| ≤ M)
    (hlam : ∀ x ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      ∀ y ∈ Set.Icc (1 : ℝ) (Real.exp 1), y ≤ x →
        |d.Knorm r x - d.Knorm r y| ≤ lam * ∫ t in y..x, D (r - 3) t)
    (hs : |d.Knorm r (Real.exp 1) - d.Knorm r 1| ≤ s * q r 1)
    {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    |d.Knorm (r + 1) u - d.Knorm r u|
      ≤ (6 * M + d.K + 14 * lam / E (r - 5) 1 + s) * q r u := by
  have h8 : 8 ≤ r := d.r₀_ge.trans hr
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨le_rfl, h1e⟩
  have hu1 : (1 : ℝ) ≤ u := hu.1
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
  have hJu : (0 : ℝ) < J (r + 1) u := J_pos hu0 (r + 1)
  have hlam0 : 0 ≤ lam := nonneg_of_lipschitz_D_weight hlam
  have hs0 : 0 ≤ s := by
    have hq1 : (0 : ℝ) < q r 1 := q_pos one_pos r
    nlinarith [abs_nonneg (d.Knorm r (Real.exp 1) - d.Knorm r 1)]
  have hcore := d.Knorm_diff_core hr M lam hM hlam hu
  -- refine the endpoint-atom factor
  have hT1 : J (r + 1) 1 * |d.Knorm r (Real.exp 1) - d.Knorm r u|
      ≤ (s + 7 * lam / E (r - 5) 1) * (J (r + 1) u * q r u) := by
    have hJ1 : (0 : ℝ) < J (r + 1) 1 := J_pos one_pos (r + 1)
    -- triangle split through the value at `1`
    have hKu1 : |d.Knorm r u - d.Knorm r 1| ≤ lam * ∫ t in (1 : ℝ)..u, D (r - 3) t :=
      hlam u hu 1 h1mem hu1
    have htri : |d.Knorm r (Real.exp 1) - d.Knorm r u|
        ≤ s * q r 1 + lam * ∫ t in (1 : ℝ)..u, D (r - 3) t := by
      have h := abs_sub (d.Knorm r (Real.exp 1) - d.Knorm r 1)
        (d.Knorm r u - d.Knorm r 1)
      have heq : d.Knorm r (Real.exp 1) - d.Knorm r 1
          - (d.Knorm r u - d.Knorm r 1)
          = d.Knorm r (Real.exp 1) - d.Knorm r u := by ring
      rw [heq] at h
      linarith
    -- absorb the two halves
    have hem := endpoint_mass_le (show 6 ≤ r by omega) hu1
    have hed := endpoint_D_int (show 6 ≤ r by omega) hu
    have hE1 : (0 : ℝ) < E (r - 5) 1 := E_pos_of_one_le (by omega) 1
    have hE1u : E (r - 5) 1 ≤ E (r - 5) u := E_mono (r - 5) hu1
    have hwq : w r u ≤ q r u / E (r - 5) 1 := by
      rw [w_eq_q_div]
      gcongr
      exact (q_pos hu0 r).le
    have hstep1 : J (r + 1) 1 * (s * q r 1) ≤ s * (J (r + 1) u * q r u) := by
      have := mul_le_mul_of_nonneg_left hem hs0
      nlinarith
    have hstep2 : J (r + 1) 1 * (lam * ∫ t in (1 : ℝ)..u, D (r - 3) t)
        ≤ 7 * lam / E (r - 5) 1 * (J (r + 1) u * q r u) := by
      have h1 := mul_le_mul_of_nonneg_left hed hlam0
      have h2 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hwq hJu.le) (by positivity : (0 : ℝ) ≤ 7 * lam)
      have h3 : 7 * lam * (J (r + 1) u * (q r u / E (r - 5) 1))
          = 7 * lam / E (r - 5) 1 * (J (r + 1) u * q r u) := by
        field_simp
      nlinarith
    calc J (r + 1) 1 * |d.Knorm r (Real.exp 1) - d.Knorm r u|
        ≤ J (r + 1) 1 * (s * q r 1 + lam * ∫ t in (1 : ℝ)..u, D (r - 3) t) :=
          mul_le_mul_of_nonneg_left htri hJ1.le
      _ = J (r + 1) 1 * (s * q r 1)
          + J (r + 1) 1 * (lam * ∫ t in (1 : ℝ)..u, D (r - 3) t) := by ring
      _ ≤ s * (J (r + 1) u * q r u)
          + 7 * lam / E (r - 5) 1 * (J (r + 1) u * q r u) := add_le_add hstep1 hstep2
      _ = (s + 7 * lam / E (r - 5) 1) * (J (r + 1) u * q r u) := by ring
  -- divide by `J_{r+1}(u)`
  refine le_of_mul_le_mul_right ?_ hJu
  calc |d.Knorm (r + 1) u - d.Knorm r u| * J (r + 1) u
      ≤ (s + 7 * lam / E (r - 5) 1) * (J (r + 1) u * q r u)
        + (6 * M + d.K + 7 * lam / E (r - 5) 1) * (J (r + 1) u * q r u) := by
        linarith
    _ = (6 * M + d.K + 14 * lam / E (r - 5) 1 + s) * q r u * J (r + 1) u := by ring

/-! ## eq. `scalar-endpoint-bound` (deliverable 6) -/

/-- **eq. `scalar-endpoint-bound`**: the endpoint jump at depth `r + 1`
obeys `|K_{r+1}(e) − K_{r+1}(1)| ≤ (6M + K + 7·lam·ε_r)·q_{r+1}(1)`, with
no `s_r`-dependence — the paper's `s_{r+1} ≤ C₁(1 + M + ε_r λ_r)` with
explicit constants.

The decomposition of `Knorm_diff_core` is evaluated at `u = e`, where its
endpoint-atom factor is `J_{r+1}(1)·|K_r(e) − K_r(e)| = 0` *identically*:
`K_{r+1}(1) = K_r(e)` exactly (`Knorm_endpoint`) and `q_r(e) = q_{r+1}(1)`
(`q_exp_one`).  This is the vanishing in the paper's proof (its display
`α_r(e)(K_r(e) − K_r(e)) = 0`). -/
theorem Knorm_endpoint_step (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r)
    (M lam : ℝ)
    (hM : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1), |d.Knorm r t| ≤ M)
    (hlam : ∀ x ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      ∀ y ∈ Set.Icc (1 : ℝ) (Real.exp 1), y ≤ x →
        |d.Knorm r x - d.Knorm r y| ≤ lam * ∫ t in y..x, D (r - 3) t) :
    |d.Knorm (r + 1) (Real.exp 1) - d.Knorm (r + 1) 1|
      ≤ (6 * M + d.K + 7 * lam / E (r - 5) 1) * q (r + 1) 1 := by
  have h8 : 8 ≤ r := d.r₀_ge.trans hr
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hemem : Real.exp 1 ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨h1e, le_rfl⟩
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hJe : (0 : ℝ) < J (r + 1) (Real.exp 1) := J_pos he0 (r + 1)
  have hcore := d.Knorm_diff_core hr M lam hM hlam hemem
  rw [sub_self, abs_zero, mul_zero, zero_add] at hcore
  -- rewrite the endpoints
  have hK1 : d.Knorm (r + 1) 1 = d.Knorm r (Real.exp 1) :=
    (d.Knorm_endpoint hr (by omega)).symm
  have hqe : q r (Real.exp 1) = q (r + 1) 1 := q_exp_one (by omega)
  rw [hK1, ← hqe]
  refine le_of_mul_le_mul_right ?_ hJe
  calc |d.Knorm (r + 1) (Real.exp 1) - d.Knorm r (Real.exp 1)|
        * J (r + 1) (Real.exp 1)
      ≤ (6 * M + d.K + 7 * lam / E (r - 5) 1)
        * (J (r + 1) (Real.exp 1) * q r (Real.exp 1)) := hcore
    _ = (6 * M + d.K + 7 * lam / E (r - 5) 1) * q r (Real.exp 1)
        * J (r + 1) (Real.exp 1) := by ring

/-! ## eq. `scalar-derivative-bound`: the pointwise quotient-derivative
bound and the Lipschitz transfer (deliverable 5) -/

/-- Pointwise bound on the derivative of the quotient `K_{r+1} = Y_{r+1}/J_{r+1}`
(the value produced by the quotient rule from the recurrence
`Y_{r+1}' = a_r(Y_r + η_r)` and eq. `J-defect`): on `[1, e]`, given a depth-`r`
sup bound `M` and a difference bound `d_r = dr` (eq. `K-cauchy` shape),
`|K_{r+1}'| ≤ (2·dr + 6M + 7K)·D_{r-2}` — the paper's
`λ_{r+1} ≤ C₁(d_r + 1 + M)` with explicit constants, via
`a_rJ_rq_r ≤ 2D_{r-2}J_{r+1}`, `a_r|η_r| ≤ K·D_{r-2}·J_{r+1}` (the factor
`E_{r-2}²/E_{r-1} ≤ 1`), and `a_rR_r ≤ 6D_{r-2}J_{r+1}`
(`Rdefect_le_three_q_mul_J`), and `D_rq_r = D_{r-2}`. -/
theorem Knorm_deriv_quotient_bound (d : IterationData) {r : ℕ}
    (hr : d.r₀ ≤ r) (M dr : ℝ)
    (hM : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1), |d.Knorm r t| ≤ M)
    (hdr : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      |d.Knorm (r + 1) t - d.Knorm r t| ≤ dr * q r t)
    {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    |(a r x * (d.Y r x + d.η r x) * J (r + 1) x
        - d.Y (r + 1) x * (a r x * (J r x + Rdefect r x))) / J (r + 1) x ^ 2|
      ≤ (2 * dr + 6 * M + 7 * d.K) * D (r - 2) x := by
  have h8 : 8 ≤ r := d.r₀_ge.trans hr
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨le_rfl, h1e⟩
  have hx1 : (1 : ℝ) ≤ x := hx.1
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hJx : (0 : ℝ) < J (r + 1) x := J_pos hx0 (r + 1)
  have hJrx : (0 : ℝ) < J r x := J_pos hx0 r
  have hDx : (0 : ℝ) < D (r - 2) x := D_pos hx0 (r - 2)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 1 h1mem)
  have hdr0 : 0 ≤ dr := by
    have h := hdr 1 h1mem
    have hq1 : (0 : ℝ) < q r 1 := q_pos one_pos r
    nlinarith [abs_nonneg (d.Knorm (r + 1) 1 - d.Knorm r 1)]
  -- factor the numerator through the normalized quantities
  have hfact : a r x * (d.Y r x + d.η r x) * J (r + 1) x
      - d.Y (r + 1) x * (a r x * (J r x + Rdefect r x))
      = (a r x * J r x * (d.Knorm r x - d.Knorm (r + 1) x)
          + a r x * d.η r x
          - a r x * Rdefect r x * d.Knorm (r + 1) x) * J (r + 1) x := by
    simp only [IterationData.Knorm]
    field_simp
    ring
  -- (a) the `K_r − K_{r+1}` piece
  have hKd : |d.Knorm r x - d.Knorm (r + 1) x| ≤ dr * q r x := by
    rw [abs_sub_comm]
    exact hdr x hx
  have h1piece : |a r x * J r x * (d.Knorm r x - d.Knorm (r + 1) x)|
      ≤ 2 * dr * (D (r - 2) x * J (r + 1) x) := by
    have haJ : (0 : ℝ) < a r x * J r x := mul_pos (a_pos r x) hJrx
    rw [abs_mul, abs_of_pos haJ]
    calc a r x * J r x * |d.Knorm r x - d.Knorm (r + 1) x|
        ≤ a r x * J r x * (dr * q r x) := mul_le_mul_of_nonneg_left hKd haJ.le
      _ = dr * (a r x * J r x * q r x) := by ring
      _ ≤ dr * (2 * (D (r - 2) x * J (r + 1) x)) :=
          mul_le_mul_of_nonneg_left (a_mul_J_mul_q_le (by omega) hx1) hdr0
      _ = 2 * dr * (D (r - 2) x * J (r + 1) x) := by ring
  -- (b) the forcing piece
  have h2piece : |a r x * d.η r x| ≤ d.K * (D (r - 2) x * J (r + 1) x) := by
    rw [abs_mul, abs_of_pos (a_pos r x)]
    have hEE1 : E (r - 2) x ^ 2 / E (r - 1) x ≤ 1 := by
      have h20 : (20 : ℝ) ≤ E (r - 2) x := twenty_le_E (by omega) hx1
      have hEr1 : E (r - 1) x = Real.exp (E (r - 2) x) := by
        rw [show r - 1 = r - 2 + 1 by omega, E_succ]
      rw [div_le_one (by rw [hEr1]; positivity)]
      calc E (r - 2) x ^ 2 ≤ Real.exp (E (r - 2) x / 2) := sq_le_exp_half h20
        _ ≤ Real.exp (E (r - 2) x) := Real.exp_le_exp.mpr (by linarith)
        _ = E (r - 1) x := hEr1.symm
    have hη1 : |d.η r x| ≤ d.K :=
      calc |d.η r x| ≤ d.K * (E (r - 2) x ^ 2 / E (r - 1) x) := d.η_bound r hr x hx
        _ ≤ d.K * 1 := mul_le_mul_of_nonneg_left hEE1 d.K_nonneg
        _ = d.K := mul_one _
    have haJ1 : a r x ≤ D (r - 2) x * J (r + 1) x :=
      calc a r x ≤ J (r + 1) x := a_le_J_succ (by omega) hx1
        _ ≤ D (r - 2) x * J (r + 1) x :=
            le_mul_of_one_le_left hJx.le (one_le_D hx1 (r - 2))
    calc a r x * |d.η r x|
        ≤ a r x * d.K := mul_le_mul_of_nonneg_left hη1 (a_pos r x).le
      _ ≤ D (r - 2) x * J (r + 1) x * d.K :=
          mul_le_mul_of_nonneg_right haJ1 d.K_nonneg
      _ = d.K * (D (r - 2) x * J (r + 1) x) := by ring
  -- (c) the defect piece, against the depth-`(r+1)` sup bound
  have hKsup : |d.Knorm (r + 1) x| ≤ M + d.K := by
    have h := d.Knorm_sup_step hr M hM hx
    have hq1 : q r 1 ≤ 1 := q_le_one le_rfl r
    nlinarith [d.K_nonneg, (q_pos one_pos r).le]
  have h3piece : |a r x * Rdefect r x * d.Knorm (r + 1) x|
      ≤ 6 * (M + d.K) * (D (r - 2) x * J (r + 1) x) := by
    have hR0 : 0 ≤ Rdefect r x := Rdefect_nonneg hx0 r
    have haR0 : 0 ≤ a r x * Rdefect r x := mul_nonneg (a_pos r x).le hR0
    rw [abs_mul, abs_of_nonneg haR0]
    have haR : a r x * Rdefect r x ≤ 6 * (D (r - 2) x * J (r + 1) x) :=
      calc a r x * Rdefect r x
          ≤ a r x * (3 * q r x * J r x) :=
            mul_le_mul_of_nonneg_left (Rdefect_le_three_q_mul_J (by omega) hx1)
              (a_pos r x).le
        _ = 3 * (a r x * J r x * q r x) := by ring
        _ ≤ 3 * (2 * (D (r - 2) x * J (r + 1) x)) :=
            mul_le_mul_of_nonneg_left (a_mul_J_mul_q_le (by omega) hx1)
              (by norm_num)
        _ = 6 * (D (r - 2) x * J (r + 1) x) := by ring
    calc a r x * Rdefect r x * |d.Knorm (r + 1) x|
        ≤ 6 * (D (r - 2) x * J (r + 1) x) * (M + d.K) :=
          mul_le_mul haR hKsup (abs_nonneg _)
            (by nlinarith [hDx.le, hJx.le])
      _ = 6 * (M + d.K) * (D (r - 2) x * J (r + 1) x) := by ring
  -- assemble the inner bound
  have hinner : |a r x * J r x * (d.Knorm r x - d.Knorm (r + 1) x)
      + a r x * d.η r x
      - a r x * Rdefect r x * d.Knorm (r + 1) x|
      ≤ (2 * dr + 6 * M + 7 * d.K) * D (r - 2) x * J (r + 1) x := by
    have htriA := abs_sub
      (a r x * J r x * (d.Knorm r x - d.Knorm (r + 1) x) + a r x * d.η r x)
      (a r x * Rdefect r x * d.Knorm (r + 1) x)
    have htriB := abs_add_le
      (a r x * J r x * (d.Knorm r x - d.Knorm (r + 1) x))
      (a r x * d.η r x)
    linarith
  -- divide by `J_{r+1}²`
  rw [hfact, abs_div, abs_of_pos (pow_pos hJx 2), div_le_iff₀ (pow_pos hJx 2),
    abs_mul, abs_of_pos hJx]
  calc |a r x * J r x * (d.Knorm r x - d.Knorm (r + 1) x)
        + a r x * d.η r x
        - a r x * Rdefect r x * d.Knorm (r + 1) x| * J (r + 1) x
      ≤ (2 * dr + 6 * M + 7 * d.K) * D (r - 2) x * J (r + 1) x * J (r + 1) x :=
        mul_le_mul_of_nonneg_right hinner hJx.le
    _ = (2 * dr + 6 * M + 7 * d.K) * D (r - 2) x * J (r + 1) x ^ 2 := by ring

/-- **eq. `scalar-derivative-bound`, Lipschitz (integral) form**: under a
depth-`r` sup bound `M`, a difference bound `d_r = dr` (eq. `K-cauchy`
shape), and the *right-derivative* form of the recurrence for `Y_{r+1}`
(hypothesis `hYder`; supplied at every phase by the intended instantiation
`Y = H̄` via `hasDerivWithinAt_Hbar_succ_Ioi`, with no exceptional set —
stronger than the paper's a.e. statement),
`|K_{r+1}(u) − K_{r+1}(v)| ≤ (2·dr + 6M + 7K)·∫ᵥᵘ D_{r-2}` for
`1 ≤ v ≤ u ≤ e`.  This is the depth-`(r+1)` Lipschitz hypothesis with weight
`D_{(r+1)-3} = D_{r-2}` and constant `λ_{r+1} = 2d_r + 6M + 7K` — the
paper's `λ_{r+1} ≤ C₁(d_r + 1 + M)` with explicit constants (no `λ_r` on the
right, exactly as in the paper).  Proof: one-sided mean value
(`image_norm_le_of_norm_deriv_right_le_deriv_boundary`) against the boundary
function `C·∫ᵥ˙ D_{r-2}`, with the pointwise bound
`Knorm_deriv_quotient_bound`. -/
theorem Knorm_lipschitz_step (d : IterationData) {r : ℕ} (hr : d.r₀ ≤ r)
    (M dr : ℝ)
    (hM : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1), |d.Knorm r t| ≤ M)
    (hdr : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      |d.Knorm (r + 1) t - d.Knorm r t| ≤ dr * q r t)
    (hYder : ∀ x ∈ Set.Ico (1 : ℝ) (Real.exp 1),
      HasDerivWithinAt (d.Y (r + 1)) (a r x * (d.Y r x + d.η r x))
        (Set.Ioi x) x)
    {u v : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1))
    (hv : v ∈ Set.Icc (1 : ℝ) (Real.exp 1)) (hvu : v ≤ u) :
    |d.Knorm (r + 1) u - d.Knorm (r + 1) v|
      ≤ (2 * dr + 6 * M + 7 * d.K) * ∫ t in v..u, D (r - 2) t := by
  have h8 : 8 ≤ r := d.r₀_ge.trans hr
  -- the boundary function `B(y) = C·∫ᵥʸ D_{r-2}` and its derivative
  have hB : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => (2 * dr + 6 * M + 7 * d.K) * ∫ t in v..y, D (r - 2) t)
      ((2 * dr + 6 * M + 7 * d.K) * D (r - 2) x) x := fun x =>
    HasDerivAt.const_mul _
      (((continuous_D (r - 2)).integral_hasStrictDerivAt v x).hasDerivAt)
  -- continuity of the recentered quotient on `[v, u]`
  have hf : ContinuousOn
      (fun y => d.Y (r + 1) y / J (r + 1) y - d.Knorm (r + 1) v)
      (Set.Icc v u) := by
    have hsub : Set.Icc v u ⊆ Set.Icc (1 : ℝ) (Real.exp 1) :=
      Set.Icc_subset_Icc hv.1 hu.2
    exact ((d.Knorm_continuousOn (show d.r₀ ≤ r + 1 by omega)).mono hsub).sub
      continuousOn_const
  -- right derivative of the recentered quotient on `[v, u)`
  have hf' : ∀ x ∈ Set.Ico v u, HasDerivWithinAt
      (fun y => d.Y (r + 1) y / J (r + 1) y - d.Knorm (r + 1) v)
      ((a r x * (d.Y r x + d.η r x) * J (r + 1) x
        - d.Y (r + 1) x * (a r x * (J r x + Rdefect r x))) / J (r + 1) x ^ 2)
      (Set.Ici x) x := by
    intro x hx
    have hx1e : x ∈ Set.Ico (1 : ℝ) (Real.exp 1) :=
      ⟨hv.1.trans hx.1, lt_of_lt_of_le hx.2 hu.2⟩
    have hJne : J (r + 1) x ≠ 0 :=
      (J_pos (lt_of_lt_of_le one_pos hx1e.1) (r + 1)).ne'
    have hdiv := (hYder x hx1e).fun_div
      ((hasDerivAt_J_succ (show 4 ≤ r by omega) x).hasDerivWithinAt) hJne
    exact (hdiv.sub_const (d.Knorm (r + 1) v)).Ici_of_Ioi
  -- initial value
  have ha0 : ‖d.Y (r + 1) v / J (r + 1) v - d.Knorm (r + 1) v‖
      ≤ (2 * dr + 6 * M + 7 * d.K) * ∫ t in v..v, D (r - 2) t := by
    simp [IterationData.Knorm]
  -- pointwise derivative bound
  have hbound : ∀ x ∈ Set.Ico v u,
      ‖(a r x * (d.Y r x + d.η r x) * J (r + 1) x
        - d.Y (r + 1) x * (a r x * (J r x + Rdefect r x))) / J (r + 1) x ^ 2‖
      ≤ (2 * dr + 6 * M + 7 * d.K) * D (r - 2) x := by
    intro x hx
    have hx1e : x ∈ Set.Icc (1 : ℝ) (Real.exp 1) :=
      ⟨hv.1.trans hx.1, hx.2.le.trans hu.2⟩
    rw [Real.norm_eq_abs]
    exact d.Knorm_deriv_quotient_bound hr M dr hM hdr hx1e
  have hres := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    hf hf' ha0 hB hbound (Set.right_mem_Icc.mpr hvu)
  simpa only [Real.norm_eq_abs, IterationData.Knorm] using hres

end IterationData

end Erdos320
