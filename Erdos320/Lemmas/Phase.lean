import Erdos320.Lemmas.IterationContraction
import Erdos320.Lemmas.Threshold
import Erdos320.Lemmas.AveragingRelation
import Erdos320.Lemmas.ExactRecurrence

/-!
# The phase function `Φ` and `prop:phase` (eq. `iteration-asymptotic`)

This file instantiates the generic iteration lemma
(`lem:iteration-endpoint-matching`, formalized as
`IterationData.iteration_endpoint_matching` and its def-based API in
`IterationContraction`) with the concrete data of the paper's proof of
`prop:phase`: `Y_r = H̄_r` and `η_r = ρ_r`, with forcing constant `K = 107`
(`rhoDepth_abs_le`, the explicit form of eq. `rho-small`).

* `HbarIterationData` — the hypothesis package `(H̄, ρ, 107, 8)` of the
  iteration lemma, its fields discharged from the `H̄`/`𝓑` basics
  (positivity, monotonicity, continuity, endpoint matching), the recurrence
  of `lem:exact-recurrence` (`ExactRecurrence`), and the forcing bound of
  `lem:threshold` (`Threshold`).
* `phase_hYder` — the everywhere-valid right-derivative form of
  eq. `exact-recurrence` feeding the contraction argument.
* `phasePhi` — **the phase function `Φ`** of `prop:phase`, defined as the
  iteration limit `Ψ` of the normalized iterates `H̄_r/J_r`; positive,
  continuous, with `Φ(1) = Φ(e)` (`phasePhi_pos`, `phasePhi_continuousOn`,
  `phasePhi_endpoint`), and geometric tail
  (`abs_Hbar_div_J_sub_phasePhi_le`).
* `phase_asymptotic` — **`prop:phase`, eq. `iteration-asymptotic`** in
  explicit form: `|F(E_r(u)) − D_r(u)Φ(u)(1 + 1/E_{r-3}(u))| ≤ C·D_{r-2}(u)`
  uniformly on `u ∈ [1, e]` from some depth on.  Since
  `D_{r-2} = D_r·q_r = D_r/(E_{r-3}E_{r-4})` (`q_eq_D_ratio`), the error is
  `o(D_r/E_{r-3})` exactly as the paper claims (`1/E_{r-4}(u) ≤ 1/E_{r-4}(1)
  → 0` uniformly).

The paper's proof of `prop:phase` records the averaging-estimate error
`F(E_r(u)) − H̄_r(u) ≪ E_{r-2}(u)²/E_{r-1}(u)` as negligible; here
this is made explicit via `E_sq_div_le` (the ratio is
`≤ exp(−E_{r-2}(u)/2) ≤ 1 ≤ D_{r-2}(u)`), so it is absorbed into the same
`O(D_{r-2})` term as the contraction tail.  Applying `prop:averaging-relation`
at `X = E_{r-1}(u)` needs `E_{r-1}(u) ≥ 10⁷`, which holds from depth `r ≥ 5`
on (`E₄(1) = exp(E₃(1)) > exp(3.8·10⁶)`); the starting depth `r₀ = 8` of the
iteration package dominates every such threshold.
-/

namespace Erdos320

/-! ## Positivity of `𝓑` on `[1, ∞)` (for the `Y_pos` field)

`𝓑` is affine with slope `1/m_*(0) = 1` on `[0, log 2] = [0, g(1)]`
(`B_right_affine`), so `𝓑(log 2) = log 2 > 0`, and `𝓑` is monotone. -/

/-- The threshold index at `0` is `1`: `g(0) = 0 ≤ 0 < log 2 = g(1)`
(`thr_g_one`), so the first paper index with `g(m) > 0` is `m = 1`. -/
theorem phase_mStar_zero : mStar 0 = 1 := by
  have h1 : 0 < mStar 0 := mStar_pos le_rfl
  have h2 : mStar 0 ≤ 1 := mStar_le_of_lt_g (by
    rw [thr_g_one]
    exact Real.log_pos (by norm_num))
  omega

/-- `𝓑(log 2) = log 2`: on `[0, g(1)] = [0, log 2]` the concave average `𝓑`
is affine with slope `1/m_*(0) = 1` (`B_right_affine`) and `𝓑(0) = 0`
(`thr_B_zero`). -/
theorem phase_B_log_two : B (Real.log 2) = Real.log 2 := by
  have haff := B_right_affine (X := 0) (Y := Real.log 2) le_rfl
    (Real.log_nonneg one_le_two)
    (by rw [phase_mStar_zero, thr_g_one])
  rw [thr_B_zero, phase_mStar_zero] at haff
  simpa using haff

/-- `𝓑(X) > 0` for `X ≥ 1`: `𝓑(X) ≥ 𝓑(log 2) = log 2 > 0` by monotonicity
(`B_mono`).  This is the positivity input `Y_pos` of the iteration package
(the iterated exponentials satisfy `E_{r-1}(u) ≥ 1` throughout `[1, e]`). -/
theorem phase_B_pos_of_one_le {X : ℝ} (hX : 1 ≤ X) : 0 < B X := by
  have hlog : Real.log 2 ≤ X := le_trans (by linarith [Real.log_two_lt_d9]) hX
  have hmono : B (Real.log 2) ≤ B X := B_mono hlog
  rw [phase_B_log_two] at hmono
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-! ## The iteration package `Y_r = H̄_r`, `η_r = ρ_r` -/

/-- The iteration data of `lem:iteration-endpoint-matching` realized by
`Y_r = H̄_r`, `η_r = ρ_r` — the paper's proof of `prop:phase` ("apply
`lem:iteration-endpoint-matching` to `Y_r = H̄_r`").  `lem:exact-recurrence`
supplies the differentiated recurrence (`Y_transport`) and the uniform
forcing bound `|ρ_r| ≤ 107·E_{r-2}²/E_{r-1}`, the explicit `K = 107` form of
eq. `rho-small` (`rhoDepth_abs_le`).  The starting depth `r₀ = 8` clears
every numeric threshold of the localization toolkit. -/
noncomputable def HbarIterationData : IterationData where
  Y := Hbar
  η := rhoDepth
  K := 107
  r₀ := 8
  r₀_ge := le_rfl
  K_nonneg := by norm_num
  Y_pos := fun r _ u hu =>
    phase_B_pos_of_one_le (one_le_E_of_one_le hu.1 (r - 1))
  Y_mono := fun r _ => (Hbar_mono r).monotoneOn _
  Y_cont := fun r _ => (continuous_Hbar r).continuousOn
  Y_endpoint := fun r hr => Hbar_exp_one (by omega)
  Y_transport := fun r hr u hu => Hbar_succ_sub_eq_integral (by omega) hu.1
  η_bound := fun r hr t ht => rhoDepth_abs_le (by omega) ht
  η_integrable := fun r hr => by
    have h1 := intervalIntegrable_recurrenceIntegrand
      (show 3 ≤ r by omega) 1 (Real.exp 1)
    have h2 : IntervalIntegrable (fun t => a r t * Hbar r t)
        MeasureTheory.volume 1 (Real.exp 1) :=
      ((continuous_a r).mul (continuous_Hbar r)).intervalIntegrable 1
        (Real.exp 1)
    have heq : (fun t => a r t * rhoDepth r t)
        = fun t => a r t * (Hbar r t + rhoDepth r t) - a r t * Hbar r t := by
      funext t
      ring
    rw [heq]
    exact h1.sub h2

/-- The right-derivative package feeding the contraction closure lemmas: for
every depth `r ≥ 8 = r₀` and every phase `x ∈ [1, e)`, `H̄_{r+1}` has right
derivative `a_r(x)(H̄_r(x) + ρ_r(x))` at `x` — eq. `exact-recurrence` of
`lem:exact-recurrence` in the everywhere-valid one-sided form
(`hasDerivWithinAt_Hbar_succ_Ioi`), with no breakpoint exclusion. -/
theorem phase_hYder : ∀ r, 8 ≤ r →
    ∀ x ∈ Set.Ico (1 : ℝ) (Real.exp 1),
      HasDerivWithinAt (Hbar (r + 1)) (a r x * (Hbar r x + rhoDepth r x))
        (Set.Ioi x) x :=
  fun r hr x _ => hasDerivWithinAt_Hbar_succ_Ioi (show 3 ≤ r by omega) x

/-! ## The phase function `Φ` -/

/-- **The phase function `Φ` of `prop:phase`**: the iteration limit `Ψ` of
`lem:iteration-endpoint-matching` for the data `Y_r = H̄_r`, `η_r = ρ_r`
("take `Φ = Ψ`") — the pointwise limit of the normalized iterates
`H̄_r(u)/J_r(u)` as `r → ∞`. -/
noncomputable def phasePhi : ℝ → ℝ := HbarIterationData.iterationLimit

/-- `Φ` is continuous on the phase interval `[1, e]` (`prop:phase`:
"a positive continuous function `Φ : [1, e] → (0, ∞)`"). -/
theorem phasePhi_continuousOn :
    ContinuousOn phasePhi (Set.Icc 1 (Real.exp 1)) :=
  HbarIterationData.iterationLimit_continuousOn phase_hYder

/-- `Φ > 0` on `[1, e]` (`prop:phase`). -/
theorem phasePhi_pos :
    ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), 0 < phasePhi u :=
  HbarIterationData.iterationLimit_pos phase_hYder

/-- Endpoint matching `Φ(1) = Φ(e)` (`prop:phase`). -/
theorem phasePhi_endpoint : phasePhi 1 = phasePhi (Real.exp 1) :=
  HbarIterationData.iterationLimit_endpoint phase_hYder

/-- The geometric tail of the iteration (`lem:iteration-endpoint-matching`,
eq. `iteration-endpoint-conclusion`, for `Y_r = H̄_r`): from some depth `r₁`
on, `|H̄_r(u)/J_r(u) − Φ(u)| ≤ C·q_r(u)` uniformly on `[1, e]`, where
`q_r = 1/(E_{r-3}E_{r-4})` is the paper's error scale. -/
theorem abs_Hbar_div_J_sub_phasePhi_le :
    ∃ (C : ℝ) (r₁ : ℕ), 0 ≤ C ∧ ∀ r, r₁ ≤ r →
      ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1),
        |Hbar r u / J r u - phasePhi u| ≤ C * q r u := by
  obtain ⟨C, r₁, hC, h⟩ :=
    HbarIterationData.abs_Knorm_sub_iterationLimit_le phase_hYder
  exact ⟨C, r₁, hC, fun r hr u hu => h r hr u hu⟩

/-! ## `prop:phase`, eq. `iteration-asymptotic` in explicit form -/

/-- **Paper `prop:phase`, eq. `iteration-asymptotic`, explicit form**: there
are `C ≥ 0` and a depth `r₁` with
```
|F(E_r(u)) − D_r(u)·Φ(u)·(1 + 1/E_{r-3}(u))| ≤ C·D_{r-2}(u)
```
for all `r ≥ r₁`, uniformly on `u ∈ [1, e]`.  Since
`D_{r-2} = D_r·q_r = D_r/(E_{r-3}E_{r-4})` (`q_eq_D_ratio`) and
`1/E_{r-4}(u) ≤ 1/E_{r-4}(1) → 0`, the right side is
`o(D_r(u)/E_{r-3}(u))` uniformly — the paper's
`F(E_r(u)) = D_r(u)Φ(u)(1 + 1/E_{r-3}(u) + o(1/E_{r-3}(u)))`.

Proof as in the paper: `prop:averaging-relation` at `X = E_{r-1}(u)` gives
`|F(E_r(u)) − H̄_r(u)| ≤ 7·E_{r-2}²/E_{r-1} ≤ 7·D_{r-2}`; the iteration tail
(`abs_Hbar_div_J_sub_phasePhi_le`) gives
`|H̄_r − J_rΦ| ≤ C₀·J_r·q_r ≤ 2C₀·D_r·q_r = 2C₀·D_{r-2}`; and
`J_r = D_r(1 + 1/E_{r-3})` exactly (`J_eq`, eq. `D-J`). -/
theorem phase_asymptotic :
    ∃ (C : ℝ) (r₁ : ℕ), 0 ≤ C ∧ ∀ r, r₁ ≤ r →
      ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1),
        |FReal (E r u) - D r u * phasePhi u * (1 + 1 / E (r - 3) u)|
          ≤ C * D (r - 2) u := by
  obtain ⟨C₀, r₁', hC₀, htail⟩ := abs_Hbar_div_J_sub_phasePhi_le
  refine ⟨7 + 2 * C₀, max r₁' 8, by linarith, fun r hr u hu => ?_⟩
  have hr8 : 8 ≤ r := le_trans (le_max_right _ _) hr
  have hr₁' : r₁' ≤ r := le_trans (le_max_left _ _) hr
  have hu1 : (1 : ℝ) ≤ u := hu.1
  have hu0 : (0 : ℝ) < u := by linarith
  -- (i) averaging: `|F(E_r(u)) − H̄_r(u)| ≤ 7·E_{r-2}²/E_{r-1} ≤ 7·D_{r-2}`
  have hE2 : (3.8e6 : ℝ) < E (r - 2) u := by
    have h1 : E 3 1 ≤ E (r - 2) 1 :=
      E_mono_depth le_rfl (show 3 ≤ r - 2 by omega)
    have h2 : E (r - 2) 1 ≤ E (r - 2) u := E_mono (r - 2) hu1
    linarith [E_three_one_gt]
  have hEr1exp : E (r - 1) u = Real.exp (E (r - 2) u) := by
    have h := E_succ (r - 2) u
    rwa [show r - 2 + 1 = r - 1 by omega] at h
  have hErexp : E r u = Real.exp (E (r - 1) u) := by
    have h := E_succ (r - 1) u
    rwa [show r - 1 + 1 = r by omega] at h
  have hX' : (10 : ℝ) ^ 7 ≤ E (r - 1) u := by
    calc (10 : ℝ) ^ 7 ≤ Real.exp 20 := thr_ten_pow_seven_le_exp_twenty
      _ ≤ Real.exp (E (r - 2) u) := Real.exp_le_exp.mpr (by linarith)
      _ = E (r - 1) u := hEr1exp.symm
  have havg := averaging_relation hX'
  have hae : averagingError (E (r - 1) u) = FReal (E r u) - Hbar r u := by
    unfold averagingError Hbar
    rw [hErexp]
  have hlog : Real.log (E (r - 1) u) = E (r - 2) u := by
    rw [hEr1exp, Real.log_exp]
  rw [hae, hlog] at havg
  have hsq : E (r - 2) u ^ 2 / E (r - 1) u ≤ 1 := by
    have h := E_sq_div_le (u := u) (j := r - 2)
      (by linarith : (20 : ℝ) ≤ E (r - 2) u)
    rw [show r - 2 + 1 = r - 1 by omega] at h
    calc E (r - 2) u ^ 2 / E (r - 1) u
        ≤ Real.exp (-(E (r - 2) u) / 2) := h
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hD2 : (1 : ℝ) ≤ D (r - 2) u := one_le_D hu1 (r - 2)
  have hi : |FReal (E r u) - Hbar r u| ≤ 7 * D (r - 2) u := by
    calc |FReal (E r u) - Hbar r u|
        ≤ 7 * E (r - 2) u ^ 2 / E (r - 1) u := havg
      _ = 7 * (E (r - 2) u ^ 2 / E (r - 1) u) := by ring
      _ ≤ 7 * 1 := by linarith
      _ ≤ 7 * D (r - 2) u := by linarith
  -- (ii) contraction tail, scaled by `J_r`: `|H̄_r − J_rΦ| ≤ 2C₀·D_{r-2}`
  have hJ : (0 : ℝ) < J r u := J_pos hu0 r
  have hDr : (0 : ℝ) < D r u := D_pos hu0 r
  have hq : (0 : ℝ) < q r u := q_pos hu0 r
  have htail' : |Hbar r u / J r u - phasePhi u| ≤ C₀ * q r u :=
    htail r hr₁' u hu
  have hDq : D r u * q r u = D (r - 2) u := by
    rw [q_eq_D_ratio hu0 (show 5 ≤ r by omega), mul_comm,
      div_mul_cancel₀ _ hDr.ne']
  have hii : |Hbar r u - J r u * phasePhi u| ≤ 2 * C₀ * D (r - 2) u := by
    have heq : Hbar r u - J r u * phasePhi u
        = J r u * (Hbar r u / J r u - phasePhi u) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hJ]
    calc J r u * |Hbar r u / J r u - phasePhi u|
        ≤ J r u * (C₀ * q r u) :=
          mul_le_mul_of_nonneg_left htail' hJ.le
      _ ≤ 2 * D r u * (C₀ * q r u) :=
          mul_le_mul_of_nonneg_right (J_le_two_D hu1 r) (by positivity)
      _ = 2 * C₀ * (D r u * q r u) := by ring
      _ = 2 * C₀ * D (r - 2) u := by rw [hDq]
  -- (iii) `J_r·Φ = D_r·Φ·(1 + 1/E_{r-3})` exactly, and combine
  have hJΦ : D r u * phasePhi u * (1 + 1 / E (r - 3) u)
      = J r u * phasePhi u := by
    rw [J_eq hu0 (show 3 ≤ r by omega)]
    ring
  calc |FReal (E r u) - D r u * phasePhi u * (1 + 1 / E (r - 3) u)|
      = |(FReal (E r u) - Hbar r u) + (Hbar r u - J r u * phasePhi u)| := by
        rw [hJΦ]
        congr 1
        ring
    _ ≤ |FReal (E r u) - Hbar r u| + |Hbar r u - J r u * phasePhi u| :=
        abs_add_le _ _
    _ ≤ 7 * D (r - 2) u + 2 * C₀ * D (r - 2) u := add_le_add hi hii
    _ = (7 + 2 * C₀) * D (r - 2) u := by ring

end Erdos320
