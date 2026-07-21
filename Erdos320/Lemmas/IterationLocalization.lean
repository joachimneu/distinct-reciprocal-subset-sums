import Erdos320.Lemmas.BackwardReference
import Erdos320.Lemmas.ExactRecurrence

/-!
# Localization estimates of the iteration lemma (`lem:iteration-endpoint-matching`)

The four localization bounds from the proof of the manuscript's iteration
lemma (`lem:iteration-endpoint-matching`), in a *measure-free* form: instead
of the paper's measure `dμ_{r,u} = (a_r J_r / J_{r+1}(u)) 𝟙_{[1,u]} dv +
α_r(u) δ_e` we state everything as concrete interval-integral inequalities
on `[1, e]`, which is the form the follow-up contraction argument consumes.

* eq. `D-identity` / eq. `J-defect` are already formalized in
  `Erdos320.Lemmas.BackwardReference` (`hasDerivAt_D_succ`,
  `hasDerivAt_J_succ`, `Rdefect_le_three_q_mul_J`).
* eq. `normalized-transport` (numerator): `J_transport`, `mass_le` — the
  paper's "measure of total mass at most one", integrated form.
* eq. `missing-mass-localization` (`β_r(u) ≪ q_r(u)`): `missing_mass_le`,
  with the explicit constant `6` (via the workhorse `integral_q_Jderiv_le`,
  constant `2`).
* eq. `endpoint-mass-localization` (`α_r(u) q_r(1) ≤ q_r(u)`):
  `endpoint_mass_le` (constant `1`, exactly the paper's display).
* eq. `forcing-localization` (`|∫ a_r η_r| / J_{r+1}(u) ≪ q_r(u)`):
  `forcing_le`, for any forcing `η` obeying the pointwise bound
  `|η| ≤ K·E_{r-2}²/E_{r-1}` — the conclusion carries the *same* constant
  `K` (the super-exponentially small factor `δ_r` is absorbed outright,
  `δ_r(v) ≤ q_r(u)`).
* eq. `averaging-localization` prep (the weight `w_r = D_{r-3}/D_r`):
  `integral_J_D_le` and `endpoint_D_int`, both with the explicit constant
  `7` (the paper has an unspecified `≪`).

Underlying derivative computations (the paper's logarithmic-differentiation
displays `−(log q_r)' = a_{r-2} + a_{r-3}` and
`−(log w_r)' = a_{r-4} + a_{r-3} + a_{r-2}`): `hasDerivAt_q`,
`hasDerivAt_w`, and the product-rule forms `hasDerivAt_J_mul_q`,
`hasDerivAt_J_mul_w`, with the key comparisons
`(J_{r+1} q_r)' ≥ ½ q_r J_{r+1}'` (`half_q_mul_J_deriv_le`) and its
`w_r`-analogue (`half_w_mul_J_deriv_le`).

Paper vs. Lean:

* **Depth threshold.** The paper proves the lemma "for all sufficiently
  large `r`".  Here the uniform threshold for every localization estimate is
  **`r ≥ 6`** (the binding constraint is `Rdefect_le_three_q_mul_J` and the
  index arithmetic for `w_r`); the pure derivative identities hold from
  `r ≥ 5` (`hasDerivAt_q`, `hasDerivAt_J_mul_q`) resp. `r ≥ 6`
  (`hasDerivAt_w`), and the transport identity from `r ≥ 4` (`J_transport`,
  matching `hasDerivAt_J_succ`).
* **Range of `u`.** The paper states all four bounds "uniformly on
  `[1, e]`".  The Lean proofs of `integral_q_Jderiv_le`, `missing_mass_le`,
  `endpoint_mass_le`, `J_transport`, `mass_le` need only `1 ≤ u` — the
  upper cutoff `u ≤ e` is genuinely used only in `forcing_le` (to compare
  `δ_r` against `q_r(u) ≥ q_r(e)`) and in `integral_J_D_le` /
  `endpoint_D_int` (through `t ≤ e` in `D_{r+1} = t·a_r`).
* **Constants.** All the paper's Vinogradov `≪`-constants are made
  explicit: `2`, `6`, `1`, `K` (unchanged), `7` as listed above.
-/

namespace Erdos320

open MeasureTheory

/-! ## Numeric lower bounds on the iterates

Explicit floors for `E j u` used to absorb the paper's implicit constants. -/

/-- `E j u ≥ 15` for `j ≥ 2`, `u ≥ 1` (via the certified `E₂(1) > 15.154`).
Absorbs the paper's "for all sufficiently large `r`" in the comparisons
`(J_{r+1}q_r)' ≥ ½ q_r J_{r+1}'` and its `w_r`-analogue. -/
theorem fifteen_le_E {j : ℕ} (hj : 2 ≤ j) {u : ℝ} (hu : 1 ≤ u) :
    (15 : ℝ) ≤ E j u := by
  calc (15 : ℝ) ≤ 15.154 := by norm_num
    _ ≤ E 2 1 := E_two_one_bounds.1.le
    _ ≤ E 2 u := E_mono 2 hu
    _ ≤ E j u := E_mono_depth hu hj

/-- `E j u ≥ 20` for `j ≥ 3`, `u ≥ 1` (via the certified `E₃(1) > 3.8·10⁶`);
feeds the hypothesis of `E_sq_div_le` in `forcing_le`. -/
theorem twenty_le_E {j : ℕ} (hj : 3 ≤ j) {u : ℝ} (hu : 1 ≤ u) :
    (20 : ℝ) ≤ E j u := by
  calc (20 : ℝ) ≤ 3.8e6 := by norm_num
    _ ≤ E 3 1 := E_three_one_gt.le
    _ ≤ E 3 u := E_mono 3 hu
    _ ≤ E j u := E_mono_depth hu hj

/-! ## The `a`-ladder identities

The one- and two-step backward identities for `a_r` and its monotonicity in
the depth index, factored out of the repeated log-derivative computations in
`lem:iteration-endpoint-matching`. -/

/-- One backward step of the `a`-ladder: `a_r = a_{r-1}·E_{r-2}` for `r ≥ 3`
(the paper's `a_r/a_{r-1} = E_{r-2}`), a re-indexed form of `a_succ`. -/
theorem a_prev_step {r : ℕ} (hr : 3 ≤ r) (u : ℝ) :
    a r u = a (r - 1) u * E (r - 2) u := by
  have h := a_succ (r := r - 1) (by omega) u
  rwa [show r - 1 + 1 = r by omega, show r - 1 - 1 = r - 2 by omega] at h

/-- Two backward steps of the `a`-ladder:
`a_r = a_{r-2}·E_{r-3}·E_{r-2}` for `r ≥ 4`. -/
theorem a_two_step {r : ℕ} (hr : 4 ≤ r) (u : ℝ) :
    a r u = a (r - 2) u * E (r - 3) u * E (r - 2) u := by
  have h1 := a_prev_step (r := r) (by omega) u
  have h2 := a_prev_step (r := r - 1) (by omega) u
  rw [show r - 1 - 1 = r - 2 by omega, show r - 1 - 2 = r - 3 by omega] at h2
  rw [h1, h2]

/-- Monotonicity of `a` in the depth index: `a_k ≤ a_{k+1}` for `k ≥ 2`,
`u ≥ 1` (the new factor `E_{k-1} ≥ 1`). -/
theorem a_le_a_succ {k : ℕ} (hk : 2 ≤ k) {u : ℝ} (hu : 1 ≤ u) :
    a k u ≤ a (k + 1) u := by
  rw [a_succ hk u]
  exact le_mul_of_one_le_right (a_pos k u).le (one_le_E_of_one_le hu (k - 1))

/-! ## Phase-monotonicity of `D` and `J`

`D r` and `J r` are increasing in the phase `u` on `[0, ∞)` (every factor
`E j` is increasing and nonnegative there); used for the endpoint atom in
eq. `averaging-localization`. -/

/-- `D r` is monotone in the phase on nonnegative arguments. -/
theorem D_mono_phase (r : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    D r s ≤ D r t := by
  unfold D
  refine Finset.prod_le_prod (fun j _ => ?_) (fun j _ => E_mono j hst)
  cases j with
  | zero => simpa using hs
  | succ j => exact (E_pos_of_one_le (by omega) s).le

/-- `J r` is monotone in the phase on nonnegative arguments. -/
theorem J_mono_phase (r : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    J r s ≤ J r t := by
  unfold J
  exact add_le_add (D_mono_phase r hs hst) (D_mono_phase (r - 1) hs hst)

/-! ## Continuity of the §5 normalizations

(`continuous_E`, `continuous_a` come from `Erdos320.Lemmas.ExactRecurrence`.)
These supply the interval-integrability of every integrand below. -/

/-- `D r` is continuous (finite product of the continuous `E j`). -/
theorem continuous_D (r : ℕ) : Continuous (D r) := by
  unfold D
  exact continuous_finsetProd _ fun j _ => continuous_E j

/-- `J r = D r + D (r-1)` is continuous. -/
theorem continuous_J (r : ℕ) : Continuous (J r) := by
  unfold J
  exact (continuous_D r).add (continuous_D (r - 1))

/-- `A s = 1 + ∑_{j=3}^s D_j` is continuous. -/
theorem continuous_A (s : ℕ) : Continuous (A s) := by
  unfold A
  exact continuous_const.add (continuous_finsetSum _ fun j _ => continuous_D j)

/-- The defect `R_r` of eq. `J-defect` is continuous for `r ≥ 3`
(the denominator `E_{r-2}` never vanishes). -/
theorem continuous_Rdefect {r : ℕ} (hr : 3 ≤ r) : Continuous (Rdefect r) := by
  unfold Rdefect
  exact (continuous_A (r - 2)).add ((continuous_A (r - 1)).div
    (continuous_E (r - 2)) fun t => (E_pos_of_one_le (by omega) t).ne')

/-- The gap `q_r = 1/(E_{r-3}E_{r-4})` is continuous for `r ≥ 5`
(both denominator factors have index `≥ 1`, hence never vanish). -/
theorem continuous_q {r : ℕ} (hr : 5 ≤ r) : Continuous (q r) := by
  unfold q
  exact continuous_const.div ((continuous_E (r - 3)).mul (continuous_E (r - 4)))
    fun t => (mul_pos (E_pos_of_one_le (by omega) t)
      (E_pos_of_one_le (by omega) t)).ne'

/-! ## The averaging weight `w_r = D_{r-3}/D_r` (eq. `averaging-localization`)

The paper's third localization bound works with `w_r = D_{r-3}/D_r
= q_r/E_{r-5} = 1/(E_{r-3}E_{r-4}E_{r-5})`.  We take the closed `E`-product
form as the *definition* (it is defined and positive for all `u` once
`r ≥ 6`) and prove the two paper identities. -/

/-- `w r u = 1/(E_{r-3}(u)·E_{r-4}(u)·E_{r-5}(u))`: the averaging weight
`w_r` of eq. `averaging-localization` (closed form). -/
noncomputable def w (r : ℕ) (u : ℝ) : ℝ :=
  1 / (E (r - 3) u * E (r - 4) u * E (r - 5) u)

/-- `w r u > 0` for `r ≥ 6` (all three denominator indices are `≥ 1`). -/
theorem w_pos {r : ℕ} (hr : 6 ≤ r) (u : ℝ) : 0 < w r u := by
  unfold w
  exact one_div_pos.mpr (mul_pos (mul_pos (E_pos_of_one_le (by omega) u)
    (E_pos_of_one_le (by omega) u)) (E_pos_of_one_le (by omega) u))

/-- The paper's identity `w_r = q_r/E_{r-5}` (eq. `averaging-localization`,
"put `w_r = D_{r-3}/D_r = q_r/E_{r-5}`"). -/
theorem w_eq_q_div (r : ℕ) (u : ℝ) : w r u = q r u / E (r - 5) u := by
  unfold w q
  rw [div_div]

/-- The paper's defining ratio `w_r = D_{r-3}/D_r` for `r ≥ 6`, `u > 0`. -/
theorem w_eq_D_ratio {u : ℝ} (hu : 0 < u) {r : ℕ} (hr : 6 ≤ r) :
    w r u = D (r - 3) u / D r u := by
  have h1 : D r u = D (r - 1) u * E (r - 3) u := D_eq_D_pred_mul (by omega) u
  have h2 : D (r - 1) u = D (r - 2) u * E (r - 4) u := by
    have h := D_eq_D_pred_mul (r := r - 1) (by omega) u
    rwa [show r - 1 - 1 = r - 2 by omega, show r - 1 - 3 = r - 4 by omega] at h
  have h3 : D (r - 2) u = D (r - 3) u * E (r - 5) u := by
    have h := D_eq_D_pred_mul (r := r - 2) (by omega) u
    rwa [show r - 2 - 1 = r - 3 by omega, show r - 2 - 3 = r - 5 by omega] at h
  have hD3 : D (r - 3) u ≠ 0 := (D_pos hu _).ne'
  have hE3 : E (r - 3) u ≠ 0 := (E_pos_of_pos hu _).ne'
  have hE4 : E (r - 4) u ≠ 0 := (E_pos_of_pos hu _).ne'
  have hE5 : E (r - 5) u ≠ 0 := (E_pos_of_pos hu _).ne'
  unfold w
  rw [h1, h2, h3]
  field_simp

/-- `w r` is continuous for `r ≥ 6`. -/
theorem continuous_w {r : ℕ} (hr : 6 ≤ r) : Continuous (w r) := by
  unfold w
  exact continuous_const.div
    (((continuous_E (r - 3)).mul (continuous_E (r - 4))).mul (continuous_E (r - 5)))
    fun t => (mul_pos (mul_pos (E_pos_of_one_le (by omega) t)
      (E_pos_of_one_le (by omega) t)) (E_pos_of_one_le (by omega) t)).ne'

/-! ## The derivatives of `q_r` and `w_r`

The paper's logarithmic-differentiation displays in the proof of
`lem:iteration-endpoint-matching`: `−(log q_r)' = a_{r-2} + a_{r-3}` and
`−(log w_r)' = a_{r-4} + a_{r-3} + a_{r-2}`, here in cleared
`HasDerivAt` form.  No hypothesis on `u` is needed at all (for these `r`
every `E`-factor involved is automatically positive). -/

/-- `q_r' = −q_r·(a_{r-2} + a_{r-3})` for `r ≥ 5`: the paper's
`−(log q_r)' = a_{r-2} + a_{r-3}` (proof of
`lem:iteration-endpoint-matching`, after eq. `endpoint-mass-localization`),
valid at every real `u`. -/
theorem hasDerivAt_q {r : ℕ} (hr : 5 ≤ r) (u : ℝ) :
    HasDerivAt (q r) (-(q r u) * (a (r - 2) u + a (r - 3) u)) u := by
  have hE3 : (0 : ℝ) < E (r - 3) u := E_pos_of_one_le (by omega) u
  have hE4 : (0 : ℝ) < E (r - 4) u := E_pos_of_one_le (by omega) u
  have hd3 : HasDerivAt (E (r - 3)) (a (r - 1) u) u := by
    have ha : a (r - 1) u = ∏ j ∈ Finset.Icc 1 (r - 3), E j u := by
      unfold a
      rw [show r - 1 - 2 = r - 3 by omega]
    rw [ha]
    exact hasDerivAt_E (r - 3) u
  have hd4 : HasDerivAt (E (r - 4)) (a (r - 2) u) u := by
    have ha : a (r - 2) u = ∏ j ∈ Finset.Icc 1 (r - 4), E j u := by
      unfold a
      rw [show r - 2 - 2 = r - 4 by omega]
    rw [ha]
    exact hasDerivAt_E (r - 4) u
  have hne : E (r - 3) u * E (r - 4) u ≠ 0 := (mul_pos hE3 hE4).ne'
  have hd : HasDerivAt (fun v => 1 / (E (r - 3) v * E (r - 4) v))
      ((0 * (E (r - 3) u * E (r - 4) u)
          - 1 * (a (r - 1) u * E (r - 4) u + E (r - 3) u * a (r - 2) u))
        / (E (r - 3) u * E (r - 4) u) ^ 2) u :=
    (hasDerivAt_const u (1 : ℝ)).div (hd3.mul hd4) hne
  have hfun : (fun v => 1 / (E (r - 3) v * E (r - 4) v)) = q r := rfl
  have hval : (0 * (E (r - 3) u * E (r - 4) u)
          - 1 * (a (r - 1) u * E (r - 4) u + E (r - 3) u * a (r - 2) u))
        / (E (r - 3) u * E (r - 4) u) ^ 2
      = -(q r u) * (a (r - 2) u + a (r - 3) u) := by
    have h1 : a (r - 1) u = a (r - 2) u * E (r - 3) u := by
      have h := a_succ (r := r - 2) (by omega) u
      rwa [show r - 2 + 1 = r - 1 by omega, show r - 2 - 1 = r - 3 by omega] at h
    have h2 : a (r - 2) u = a (r - 3) u * E (r - 4) u := by
      have h := a_succ (r := r - 3) (by omega) u
      rwa [show r - 3 + 1 = r - 2 by omega, show r - 3 - 1 = r - 4 by omega] at h
    have hE3' : E (r - 3) u ≠ 0 := hE3.ne'
    have hE4' : E (r - 4) u ≠ 0 := hE4.ne'
    unfold q
    rw [h1, h2]
    field_simp
    ring
  rw [hfun, hval] at hd
  exact hd

/-- `w_r' = −w_r·(a_{r-2} + a_{r-3} + a_{r-4})` for `r ≥ 6`: the paper's
`−(log w_r)' = a_{r-4} + a_{r-3} + a_{r-2}` (proof of
`lem:iteration-endpoint-matching`, third localization bound), valid at
every real `u`. -/
theorem hasDerivAt_w {r : ℕ} (hr : 6 ≤ r) (u : ℝ) :
    HasDerivAt (w r) (-(w r u) * (a (r - 2) u + a (r - 3) u + a (r - 4) u)) u := by
  have hE3 : (0 : ℝ) < E (r - 3) u := E_pos_of_one_le (by omega) u
  have hE4 : (0 : ℝ) < E (r - 4) u := E_pos_of_one_le (by omega) u
  have hE5 : (0 : ℝ) < E (r - 5) u := E_pos_of_one_le (by omega) u
  have hd3 : HasDerivAt (E (r - 3)) (a (r - 1) u) u := by
    have ha : a (r - 1) u = ∏ j ∈ Finset.Icc 1 (r - 3), E j u := by
      unfold a
      rw [show r - 1 - 2 = r - 3 by omega]
    rw [ha]
    exact hasDerivAt_E (r - 3) u
  have hd4 : HasDerivAt (E (r - 4)) (a (r - 2) u) u := by
    have ha : a (r - 2) u = ∏ j ∈ Finset.Icc 1 (r - 4), E j u := by
      unfold a
      rw [show r - 2 - 2 = r - 4 by omega]
    rw [ha]
    exact hasDerivAt_E (r - 4) u
  have hd5 : HasDerivAt (E (r - 5)) (a (r - 3) u) u := by
    have ha : a (r - 3) u = ∏ j ∈ Finset.Icc 1 (r - 5), E j u := by
      unfold a
      rw [show r - 3 - 2 = r - 5 by omega]
    rw [ha]
    exact hasDerivAt_E (r - 5) u
  have hne : E (r - 3) u * E (r - 4) u * E (r - 5) u ≠ 0 :=
    (mul_pos (mul_pos hE3 hE4) hE5).ne'
  have hd : HasDerivAt (fun v => 1 / (E (r - 3) v * E (r - 4) v * E (r - 5) v))
      ((0 * (E (r - 3) u * E (r - 4) u * E (r - 5) u)
          - 1 * ((a (r - 1) u * E (r - 4) u + E (r - 3) u * a (r - 2) u) * E (r - 5) u
            + E (r - 3) u * E (r - 4) u * a (r - 3) u))
        / (E (r - 3) u * E (r - 4) u * E (r - 5) u) ^ 2) u :=
    (hasDerivAt_const u (1 : ℝ)).div ((hd3.mul hd4).mul hd5) hne
  have hfun : (fun v => 1 / (E (r - 3) v * E (r - 4) v * E (r - 5) v)) = w r := rfl
  have hval : (0 * (E (r - 3) u * E (r - 4) u * E (r - 5) u)
          - 1 * ((a (r - 1) u * E (r - 4) u + E (r - 3) u * a (r - 2) u) * E (r - 5) u
            + E (r - 3) u * E (r - 4) u * a (r - 3) u))
        / (E (r - 3) u * E (r - 4) u * E (r - 5) u) ^ 2
      = -(w r u) * (a (r - 2) u + a (r - 3) u + a (r - 4) u) := by
    have h1 : a (r - 1) u = a (r - 2) u * E (r - 3) u := by
      have h := a_succ (r := r - 2) (by omega) u
      rwa [show r - 2 + 1 = r - 1 by omega, show r - 2 - 1 = r - 3 by omega] at h
    have h2 : a (r - 2) u = a (r - 3) u * E (r - 4) u := by
      have h := a_succ (r := r - 3) (by omega) u
      rwa [show r - 3 + 1 = r - 2 by omega, show r - 3 - 1 = r - 4 by omega] at h
    have h3 : a (r - 3) u = a (r - 4) u * E (r - 5) u := by
      have h := a_succ (r := r - 4) (by omega) u
      rwa [show r - 4 + 1 = r - 3 by omega, show r - 4 - 1 = r - 5 by omega] at h
    have hE3' : E (r - 3) u ≠ 0 := hE3.ne'
    have hE4' : E (r - 4) u ≠ 0 := hE4.ne'
    have hE5' : E (r - 5) u ≠ 0 := hE5.ne'
    unfold w
    rw [h1, h2, h3]
    field_simp
    ring
  rw [hfun, hval] at hd
  exact hd

/-! ## Product-rule derivatives of `J_{r+1}·q_r` and `J_{r+1}·w_r` -/

/-- Product rule for `J_{r+1}·q_r` (from eq. `J-defect` and
`hasDerivAt_q`), the object behind eq. `missing-mass-localization` and
eq. `endpoint-mass-localization`. -/
theorem hasDerivAt_J_mul_q {r : ℕ} (hr : 5 ≤ r) (u : ℝ) :
    HasDerivAt (fun v => J (r + 1) v * q r v)
      (a r u * (J r u + Rdefect r u) * q r u
        - J (r + 1) u * (q r u * (a (r - 2) u + a (r - 3) u))) u := by
  have h : HasDerivAt (fun v => J (r + 1) v * q r v)
      (a r u * (J r u + Rdefect r u) * q r u
        + J (r + 1) u * (-(q r u) * (a (r - 2) u + a (r - 3) u))) u :=
    (hasDerivAt_J_succ (by omega) u).mul (hasDerivAt_q hr u)
  have hval : a r u * (J r u + Rdefect r u) * q r u
        + J (r + 1) u * (-(q r u) * (a (r - 2) u + a (r - 3) u))
      = a r u * (J r u + Rdefect r u) * q r u
        - J (r + 1) u * (q r u * (a (r - 2) u + a (r - 3) u)) := by ring
  rw [hval] at h
  exact h

/-- Product rule for `J_{r+1}·w_r` (from eq. `J-defect` and
`hasDerivAt_w`), the object behind eq. `averaging-localization`. -/
theorem hasDerivAt_J_mul_w {r : ℕ} (hr : 6 ≤ r) (u : ℝ) :
    HasDerivAt (fun v => J (r + 1) v * w r v)
      (a r u * (J r u + Rdefect r u) * w r u
        - J (r + 1) u * (w r u * (a (r - 2) u + a (r - 3) u + a (r - 4) u))) u := by
  have h : HasDerivAt (fun v => J (r + 1) v * w r v)
      (a r u * (J r u + Rdefect r u) * w r u
        + J (r + 1) u * (-(w r u) * (a (r - 2) u + a (r - 3) u + a (r - 4) u))) u :=
    (hasDerivAt_J_succ (by omega) u).mul (hasDerivAt_w hr u)
  have hval : a r u * (J r u + Rdefect r u) * w r u
        + J (r + 1) u * (-(w r u) * (a (r - 2) u + a (r - 3) u + a (r - 4) u))
      = a r u * (J r u + Rdefect r u) * w r u
        - J (r + 1) u * (w r u * (a (r - 2) u + a (r - 3) u + a (r - 4) u)) := by ring
  rw [hval] at h
  exact h

/-- Continuity of the derivative of `J_{r+1}·q_r` (integrability input for
the fundamental theorem of calculus below). -/
theorem continuous_J_mul_q_deriv {r : ℕ} (hr : 5 ≤ r) :
    Continuous fun t => a r t * (J r t + Rdefect r t) * q r t
      - J (r + 1) t * (q r t * (a (r - 2) t + a (r - 3) t)) :=
  (((continuous_a r).mul ((continuous_J r).add (continuous_Rdefect (by omega)))).mul
      (continuous_q hr)).sub
    ((continuous_J (r + 1)).mul ((continuous_q hr).mul
      ((continuous_a (r - 2)).add (continuous_a (r - 3)))))

/-- Continuity of the derivative of `J_{r+1}·w_r`. -/
theorem continuous_J_mul_w_deriv {r : ℕ} (hr : 6 ≤ r) :
    Continuous fun t => a r t * (J r t + Rdefect r t) * w r t
      - J (r + 1) t * (w r t * (a (r - 2) t + a (r - 3) t + a (r - 4) t)) :=
  (((continuous_a r).mul ((continuous_J r).add
        (continuous_Rdefect (by omega)))).mul (continuous_w hr)).sub
    ((continuous_J (r + 1)).mul ((continuous_w hr).mul
      (((continuous_a (r - 2)).add (continuous_a (r - 3))).add (continuous_a (r - 4)))))

/-! ## The comparison `(J_{r+1}q_r)' ≥ ½ q_r J_{r+1}'` (and `w_r`-analogue)

The paper's key display: "Since `−(log q_r)' = a_{r-2} + a_{r-3}` whereas
`(log J_{r+1})' ≍ a_{r-1}`, one has `(J_{r+1}q_r)' ≥ ½ q_r J_{r+1}'`."
Quantitatively the point is `J_{r+1}·(a_{r-2}+a_{r-3}) ≤ ½ a_r J_r`, which
holds as soon as `E_{r-3} ≥ 8`; our floor `E_{r-3} ≥ 15` (from `r ≥ 5`,
`u ≥ 1`) covers both this and the three-term `w_r`-version (which needs
`E_{r-3} ≥ 12`). -/

/-- `J_{r+1}·(a_{r-2} + a_{r-3}) ≤ ½ a_r J_r` for `r ≥ 5`, `u ≥ 1`: the
quantitative heart of the paper's `(J_{r+1}q_r)' ≥ ½ q_r J_{r+1}'`. -/
theorem J_succ_mul_a_sum_le {r : ℕ} (hr : 5 ≤ r) {u : ℝ} (hu : 1 ≤ u) :
    J (r + 1) u * (a (r - 2) u + a (r - 3) u) ≤ 1 / 2 * (a r u * J r u) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have h32 : a (r - 3) u ≤ a (r - 2) u := by
    have h := a_le_a_succ (k := r - 3) (by omega) hu
    rwa [show r - 3 + 1 = r - 2 by omega] at h
  have hJ : J (r + 1) u ≤ 2 * D (r + 1) u := J_le_two_D hu (r + 1)
  have hD : D (r + 1) u = D r u * E (r - 2) u := D_succ (by omega) u
  have haf : a r u = a (r - 2) u * E (r - 3) u * E (r - 2) u := a_two_step (by omega) u
  have hE15 : (15 : ℝ) ≤ E (r - 3) u := fifteen_le_E (by omega) hu
  have hDJ : D r u ≤ J r u := D_le_J hu0 r
  have hsum_nonneg : 0 ≤ a (r - 2) u + a (r - 3) u :=
    add_nonneg (a_pos _ u).le (a_pos _ u).le
  have hDp : (0 : ℝ) < D (r + 1) u := D_pos hu0 (r + 1)
  have step1 : J (r + 1) u * (a (r - 2) u + a (r - 3) u)
      ≤ 2 * D (r + 1) u * (2 * a (r - 2) u) :=
    mul_le_mul hJ (by linarith) hsum_nonneg (by linarith)
  have h8 : 8 * D r u ≤ E (r - 3) u * J r u := by
    have hprod : 0 ≤ (E (r - 3) u - 8) * J r u :=
      mul_nonneg (by linarith) (J_pos hu0 r).le
    nlinarith
  have hE2X : (0 : ℝ) ≤ E (r - 2) u * a (r - 2) u :=
    mul_nonneg (E_pos_of_one_le (by omega) u).le (a_pos _ u).le
  have step2 : 2 * D (r + 1) u * (2 * a (r - 2) u) ≤ 1 / 2 * (a r u * J r u) := by
    rw [hD, haf]
    nlinarith [mul_le_mul_of_nonneg_right h8 hE2X]
  linarith

/-- `J_{r+1}·(a_{r-2} + a_{r-3} + a_{r-4}) ≤ ½ a_r J_r` for `r ≥ 6`,
`u ≥ 1`: the three-term analogue behind `(J_{r+1}w_r)' ≥ ½ w_r J_{r+1}'`
(eq. `averaging-localization`). -/
theorem J_succ_mul_a_sum_three_le {r : ℕ} (hr : 6 ≤ r) {u : ℝ} (hu : 1 ≤ u) :
    J (r + 1) u * (a (r - 2) u + a (r - 3) u + a (r - 4) u)
      ≤ 1 / 2 * (a r u * J r u) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have h32 : a (r - 3) u ≤ a (r - 2) u := by
    have h := a_le_a_succ (k := r - 3) (by omega) hu
    rwa [show r - 3 + 1 = r - 2 by omega] at h
  have h43 : a (r - 4) u ≤ a (r - 3) u := by
    have h := a_le_a_succ (k := r - 4) (by omega) hu
    rwa [show r - 4 + 1 = r - 3 by omega] at h
  have hJ : J (r + 1) u ≤ 2 * D (r + 1) u := J_le_two_D hu (r + 1)
  have hD : D (r + 1) u = D r u * E (r - 2) u := D_succ (by omega) u
  have haf : a r u = a (r - 2) u * E (r - 3) u * E (r - 2) u := a_two_step (by omega) u
  have hE15 : (15 : ℝ) ≤ E (r - 3) u := fifteen_le_E (by omega) hu
  have hDJ : D r u ≤ J r u := D_le_J hu0 r
  have hsum_nonneg : 0 ≤ a (r - 2) u + a (r - 3) u + a (r - 4) u :=
    add_nonneg (add_nonneg (a_pos _ u).le (a_pos _ u).le) (a_pos _ u).le
  have hDp : (0 : ℝ) < D (r + 1) u := D_pos hu0 (r + 1)
  have step1 : J (r + 1) u * (a (r - 2) u + a (r - 3) u + a (r - 4) u)
      ≤ 2 * D (r + 1) u * (3 * a (r - 2) u) :=
    mul_le_mul hJ (by linarith) hsum_nonneg (by linarith)
  have h12 : 12 * D r u ≤ E (r - 3) u * J r u := by
    have hprod : 0 ≤ (E (r - 3) u - 12) * J r u :=
      mul_nonneg (by linarith) (J_pos hu0 r).le
    nlinarith
  have hE2X : (0 : ℝ) ≤ E (r - 2) u * a (r - 2) u :=
    mul_nonneg (E_pos_of_one_le (by omega) u).le (a_pos _ u).le
  have step2 : 2 * D (r + 1) u * (3 * a (r - 2) u) ≤ 1 / 2 * (a r u * J r u) := by
    rw [hD, haf]
    nlinarith [mul_le_mul_of_nonneg_right h12 hE2X]
  linarith

/-- Pointwise form of the paper's `(J_{r+1}q_r)' ≥ ½ q_r J_{r+1}'`
(proof of `lem:iteration-endpoint-matching`): the derivative of
`J_{r+1}·q_r` dominates half of `q_r·J_{r+1}'`, for `r ≥ 5`, `u ≥ 1`. -/
theorem half_q_mul_J_deriv_le {r : ℕ} (hr : 5 ≤ r) {u : ℝ} (hu : 1 ≤ u) :
    1 / 2 * (q r u * (a r u * (J r u + Rdefect r u)))
      ≤ a r u * (J r u + Rdefect r u) * q r u
        - J (r + 1) u * (q r u * (a (r - 2) u + a (r - 3) u)) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hq : (0 : ℝ) < q r u := q_pos hu0 r
  have hR : 0 ≤ Rdefect r u := Rdefect_nonneg hu0 r
  have ha : (0 : ℝ) < a r u := a_pos r u
  have hkey : J (r + 1) u * (a (r - 2) u + a (r - 3) u)
      ≤ 1 / 2 * (a r u * (J r u + Rdefect r u)) := by
    have h := J_succ_mul_a_sum_le hr hu
    have haR : 0 ≤ a r u * Rdefect r u := mul_nonneg ha.le hR
    linarith
  have hmul := mul_le_mul_of_nonneg_left hkey hq.le
  linarith

/-- Pointwise form of the paper's `(J_{r+1}w_r)' ≫ w_r J_{r+1}'`
(eq. `averaging-localization`), with the explicit factor `½`, for `r ≥ 6`,
`u ≥ 1`. -/
theorem half_w_mul_J_deriv_le {r : ℕ} (hr : 6 ≤ r) {u : ℝ} (hu : 1 ≤ u) :
    1 / 2 * (w r u * (a r u * (J r u + Rdefect r u)))
      ≤ a r u * (J r u + Rdefect r u) * w r u
        - J (r + 1) u * (w r u * (a (r - 2) u + a (r - 3) u + a (r - 4) u)) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hw : (0 : ℝ) < w r u := w_pos hr u
  have hR : 0 ≤ Rdefect r u := Rdefect_nonneg hu0 r
  have ha : (0 : ℝ) < a r u := a_pos r u
  have hkey : J (r + 1) u * (a (r - 2) u + a (r - 3) u + a (r - 4) u)
      ≤ 1 / 2 * (a r u * (J r u + Rdefect r u)) := by
    have h := J_succ_mul_a_sum_three_le hr hu
    have haR : 0 ≤ a r u * Rdefect r u := mul_nonneg ha.le hR
    linarith
  have hmul := mul_le_mul_of_nonneg_left hkey hw.le
  linarith

/-! ## Transport identities (fundamental theorem of calculus) -/

/-- The `J`-transport identity: for `r ≥ 4`,
`J_{r+1}(u) − J_{r+1}(1) = ∫_1^u a_r(J_r + R_r)` — the integrated form of
eq. `J-defect` behind eq. `normalized-transport`.  Valid for every real `u`
(no ordering against `1` is needed). -/
theorem J_transport {r : ℕ} (hr : 4 ≤ r) (u : ℝ) :
    J (r + 1) u - J (r + 1) 1
      = ∫ t in (1 : ℝ)..u, a r t * (J r t + Rdefect r t) := by
  have hcont : Continuous fun t => a r t * (J r t + Rdefect r t) :=
    (continuous_a r).mul ((continuous_J r).add (continuous_Rdefect (by omega)))
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_J_succ hr t) (hcont.intervalIntegrable 1 u)).symm

/-- Transport identity for `J_{r+1}·q_r`, `r ≥ 5` (fundamental theorem of
calculus for `hasDerivAt_J_mul_q`). -/
theorem J_mul_q_transport {r : ℕ} (hr : 5 ≤ r) (u : ℝ) :
    J (r + 1) u * q r u - J (r + 1) 1 * q r 1
      = ∫ t in (1 : ℝ)..u, (a r t * (J r t + Rdefect r t) * q r t
          - J (r + 1) t * (q r t * (a (r - 2) t + a (r - 3) t))) :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_J_mul_q hr t)
    ((continuous_J_mul_q_deriv hr).intervalIntegrable 1 u)).symm

/-- Transport identity for `J_{r+1}·w_r`, `r ≥ 6` (fundamental theorem of
calculus for `hasDerivAt_J_mul_w`). -/
theorem J_mul_w_transport {r : ℕ} (hr : 6 ≤ r) (u : ℝ) :
    J (r + 1) u * w r u - J (r + 1) 1 * w r 1
      = ∫ t in (1 : ℝ)..u, (a r t * (J r t + Rdefect r t) * w r t
          - J (r + 1) t * (w r t * (a (r - 2) t + a (r - 3) t + a (r - 4) t))) :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_J_mul_w hr t)
    ((continuous_J_mul_w_deriv hr).intervalIntegrable 1 u)).symm

/-- The subprobability bound of eq. `normalized-transport`: the continuous
part `∫_1^u a_r J_r` plus the endpoint atom `J_{r+1}(1)` never exceed the
normalizer `J_{r+1}(u)` (the paper's "measure of total mass at most one",
cleared of the division by `J_{r+1}(u)`), for `r ≥ 4`, `u ≥ 1`. -/
theorem mass_le {r : ℕ} (hr : 4 ≤ r) {u : ℝ} (hu : 1 ≤ u) :
    J (r + 1) 1 + (∫ t in (1 : ℝ)..u, a r t * J r t) ≤ J (r + 1) u := by
  have ht := J_transport hr u
  have hcont1 : Continuous fun t => a r t * J r t :=
    (continuous_a r).mul (continuous_J r)
  have hcont2 : Continuous fun t => a r t * (J r t + Rdefect r t) :=
    (continuous_a r).mul ((continuous_J r).add (continuous_Rdefect (by omega)))
  have hmono : (∫ t in (1 : ℝ)..u, a r t * J r t)
      ≤ ∫ t in (1 : ℝ)..u, a r t * (J r t + Rdefect r t) :=
    intervalIntegral.integral_mono_on hu (hcont1.intervalIntegrable 1 u)
      (hcont2.intervalIntegrable 1 u) fun t htI =>
        mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right
            (Rdefect_nonneg (lt_of_lt_of_le one_pos htI.1) r))
          (a_pos r t).le
  linarith

/-! ## The integrated comparison (workhorse) and
eq. `missing-mass-localization`, eq. `endpoint-mass-localization` -/

/-- **Integrated comparison** (proof of `lem:iteration-endpoint-matching`,
"integration proves the claim"): `∫_1^u q_r · J_{r+1}' ≤ 2 J_{r+1}(u)q_r(u)`
for `r ≥ 6`, `u ≥ 1`.  (The paper restricts to `u ∈ [1, e]`; the upper
cutoff is not needed.) -/
theorem integral_q_Jderiv_le {r : ℕ} (hr : 6 ≤ r) {u : ℝ} (hu : 1 ≤ u) :
    (∫ t in (1 : ℝ)..u, q r t * (a r t * (J r t + Rdefect r t)))
      ≤ 2 * (J (r + 1) u * q r u) := by
  have hcont1 : Continuous fun t => q r t * (a r t * (J r t + Rdefect r t)) :=
    (continuous_q (by omega)).mul
      ((continuous_a r).mul ((continuous_J r).add (continuous_Rdefect (by omega))))
  have hint : (∫ t in (1 : ℝ)..u, 1 / 2 * (q r t * (a r t * (J r t + Rdefect r t))))
      ≤ ∫ t in (1 : ℝ)..u, (a r t * (J r t + Rdefect r t) * q r t
          - J (r + 1) t * (q r t * (a (r - 2) t + a (r - 3) t))) :=
    intervalIntegral.integral_mono_on hu
      ((hcont1.const_mul (1 / 2)).intervalIntegrable 1 u)
      ((continuous_J_mul_q_deriv (by omega)).intervalIntegrable 1 u)
      fun t ht => half_q_mul_J_deriv_le (by omega) ht.1
  rw [intervalIntegral.integral_const_mul, ← J_mul_q_transport (by omega) u] at hint
  have hend : 0 ≤ J (r + 1) 1 * q r 1 :=
    mul_nonneg (J_pos one_pos (r + 1)).le (q_pos one_pos r).le
  linarith

/-- **eq. `missing-mass-localization`**: the missing mass `β_r(u)`, cleared
of the division by `J_{r+1}(u)`, is at most `6·J_{r+1}(u)q_r(u)`; i.e.
`β_r(u) ≤ 6 q_r(u)`.  Explicit constant for the paper's `β_r(u) ≪ q_r(u)`;
holds for `r ≥ 6` and all `u ≥ 1`. -/
theorem missing_mass_le {r : ℕ} (hr : 6 ≤ r) {u : ℝ} (hu : 1 ≤ u) :
    (∫ t in (1 : ℝ)..u, a r t * Rdefect r t) ≤ 6 * (J (r + 1) u * q r u) := by
  have hcontL : Continuous fun t => a r t * Rdefect r t :=
    (continuous_a r).mul (continuous_Rdefect (by omega))
  have hcont1 : Continuous fun t => q r t * (a r t * (J r t + Rdefect r t)) :=
    (continuous_q (by omega)).mul
      ((continuous_a r).mul ((continuous_J r).add (continuous_Rdefect (by omega))))
  have hpt : ∀ t ∈ Set.Icc (1 : ℝ) u,
      a r t * Rdefect r t ≤ 3 * (q r t * (a r t * (J r t + Rdefect r t))) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
    have h1 := mul_le_mul_of_nonneg_left
      (Rdefect_le_three_q_mul_J hr ht.1) (a_pos r t).le
    have h2 : 0 ≤ q r t * a r t * Rdefect r t :=
      mul_nonneg (mul_nonneg (q_pos ht0 r).le (a_pos r t).le)
        (Rdefect_nonneg ht0 r)
    nlinarith
  have hint := intervalIntegral.integral_mono_on hu
    (hcontL.intervalIntegrable (μ := volume) 1 u)
    ((hcont1.const_mul 3).intervalIntegrable 1 u) hpt
  rw [intervalIntegral.integral_const_mul] at hint
  have h3 := integral_q_Jderiv_le hr hu
  linarith

/-- **eq. `endpoint-mass-localization`**: `α_r(u) q_r(1) ≤ q_r(u)`, cleared
of the division by `J_{r+1}(u)`, i.e. `J_{r+1}(1)q_r(1) ≤ J_{r+1}(u)q_r(u)`
— exactly the paper's display, with constant `1`.  Monotonicity of
`J_{r+1}·q_r` from the comparison `(J_{r+1}q_r)' ≥ ½ q_r J_{r+1}' ≥ 0`;
holds for `r ≥ 6` and all `u ≥ 1` ("remains uniform as `u ↓ 1`"). -/
theorem endpoint_mass_le {r : ℕ} (hr : 6 ≤ r) {u : ℝ} (hu : 1 ≤ u) :
    J (r + 1) 1 * q r 1 ≤ J (r + 1) u * q r u := by
  have htr := J_mul_q_transport (by omega : 5 ≤ r) u
  have hnn : 0 ≤ ∫ t in (1 : ℝ)..u, (a r t * (J r t + Rdefect r t) * q r t
      - J (r + 1) t * (q r t * (a (r - 2) t + a (r - 3) t))) := by
    refine intervalIntegral.integral_nonneg hu fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
    have h := half_q_mul_J_deriv_le (by omega : 5 ≤ r) ht.1
    have hW : 0 ≤ q r t * (a r t * (J r t + Rdefect r t)) :=
      mul_nonneg (q_pos ht0 r).le (mul_nonneg (a_pos r t).le
        (add_nonneg (J_pos ht0 r).le (Rdefect_nonneg ht0 r)))
    linarith
  linarith

/-! ## eq. `forcing-localization` -/

/-- **eq. `forcing-localization`**: for any forcing `η` with the pointwise
bound `|η| ≤ K·E_{r-2}²/E_{r-1}` on `[1, e]` (the shape of the recurrence
error `η_r`, cf. eq. `rho-small`), the localized average obeys
`|∫_1^u a_r η| ≤ K·J_{r+1}(u)q_r(u)` — the paper's
`|∫_1^u a_r η_r|/J_{r+1}(u) ≪ q_r(u)` with the *same* constant `K`
(the super-exponential factor `δ_r(v) = E_{r-2}²/(E_{r-1}J_r)` satisfies
`δ_r(v) ≤ e^{-T/2} ≤ 1/(T·U) = q_r(e) ≤ q_r(u)` outright, with
`T = E_{r-2}(1)`, `U = E_{r-3}(1)`).  Requires `r ≥ 6` and `u ∈ [1, e]`;
integrability of `a_r·η` is a hypothesis (η is not assumed continuous). -/
theorem forcing_le {r : ℕ} (hr : 6 ≤ r) {u : ℝ}
    (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) {K : ℝ} (hK : 0 ≤ K) (η : ℝ → ℝ)
    (hη : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      |η t| ≤ K * (E (r - 2) t ^ 2 / E (r - 1) t))
    (hmeas : IntervalIntegrable (fun t => a r t * η t) volume 1 u) :
    |∫ t in (1 : ℝ)..u, a r t * η t| ≤ K * (J (r + 1) u * q r u) := by
  have h1u : (1 : ℝ) ≤ u := hu.1
  have hue : u ≤ Real.exp 1 := hu.2
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos h1u
  -- the super-exponential factor is dominated by `q r u`, uniformly on `[1, u]`
  have hdelta : ∀ t ∈ Set.Icc (1 : ℝ) u,
      E (r - 2) t ^ 2 / E (r - 1) t ≤ q r u := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht.1
    have hE20t : (20 : ℝ) ≤ E (r - 2) t := twenty_le_E (by omega) ht1
    have hstep : E (r - 2) t ^ 2 / E (r - 1) t
        ≤ Real.exp (-(E (r - 2) t) / 2) := by
      have h := E_sq_div_le (u := t) (j := r - 2) hE20t
      rwa [show r - 2 + 1 = r - 1 by omega] at h
    have hstep2 : Real.exp (-(E (r - 2) t) / 2)
        ≤ Real.exp (-(E (r - 2) 1) / 2) := by
      have hmono : E (r - 2) 1 ≤ E (r - 2) t := E_mono (r - 2) ht1
      exact Real.exp_le_exp.mpr (by linarith)
    have hT20 : (20 : ℝ) ≤ E (r - 2) 1 := twenty_le_E (by omega) le_rfl
    have hU1 : (1 : ℝ) ≤ E (r - 3) 1 := one_le_E_of_one_le le_rfl (r - 3)
    have hUT : E (r - 3) 1 ≤ E (r - 2) 1 := by
      have h := (E_lt_E_succ (r - 3) 1).le
      rwa [show r - 3 + 1 = r - 2 by omega] at h
    have hstep3 : Real.exp (-(E (r - 2) 1) / 2)
        ≤ 1 / (E (r - 2) 1 * E (r - 3) 1) := by
      have hsq : E (r - 2) 1 ^ 2 ≤ Real.exp (E (r - 2) 1 / 2) :=
        sq_le_exp_half hT20
      have hTU_pos : (0 : ℝ) < E (r - 2) 1 * E (r - 3) 1 :=
        mul_pos (by linarith) (by linarith)
      have hle : E (r - 2) 1 * E (r - 3) 1 ≤ Real.exp (E (r - 2) 1 / 2) := by
        nlinarith
      rw [show -(E (r - 2) 1) / 2 = -(E (r - 2) 1 / 2) by ring, Real.exp_neg,
        inv_eq_one_div]
      exact one_div_le_one_div_of_le hTU_pos hle
    have hq1 : (1 : ℝ) / (E (r - 2) 1 * E (r - 3) 1) = q r (Real.exp 1) := by
      rw [q_exp_one (by omega : 4 ≤ r)]
      unfold q
      rw [show r + 1 - 3 = r - 2 by omega, show r + 1 - 4 = r - 3 by omega]
    have hqu : q r (Real.exp 1) ≤ q r u := by
      have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      exact q_antitoneOn r (Set.mem_Ici.mpr h1u) (Set.mem_Ici.mpr h1e) hue
    linarith
  -- pointwise: `|a_r η| ≤ K q_r(u) · a_r J_r`
  have hq : (0 : ℝ) < q r u := q_pos hu0 r
  have hpt : ∀ t ∈ Set.Icc (1 : ℝ) u,
      |a r t * η t| ≤ K * q r u * (a r t * J r t) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht.1
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
    have htmem : t ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨ht1, ht.2.trans hue⟩
    have ha := a_pos r t
    have hJ1t : (1 : ℝ) ≤ J r t := le_trans (one_le_D ht1 r) (D_le_J ht0 r)
    have h1 : |η t| ≤ K * q r u :=
      (hη t htmem).trans (mul_le_mul_of_nonneg_left (hdelta t ht) hK)
    have hfin : |η t| ≤ K * q r u * J r t :=
      h1.trans (le_mul_of_one_le_right (mul_nonneg hK hq.le) hJ1t)
    rw [abs_mul, abs_of_pos ha]
    calc a r t * |η t| ≤ a r t * (K * q r u * J r t) :=
          mul_le_mul_of_nonneg_left hfin ha.le
      _ = K * q r u * (a r t * J r t) := by ring
  -- integrate and absorb `∫ a_r J_r ≤ J_{r+1}(u)` (from `mass_le`)
  have habs : |∫ t in (1 : ℝ)..u, a r t * η t|
      ≤ ∫ t in (1 : ℝ)..u, |a r t * η t| :=
    intervalIntegral.abs_integral_le_integral_abs h1u
  have hcontKJ : Continuous fun t => K * q r u * (a r t * J r t) :=
    ((continuous_a r).mul (continuous_J r)).const_mul _
  have hint2 := intervalIntegral.integral_mono_on h1u hmeas.abs
    (hcontKJ.intervalIntegrable 1 u) hpt
  rw [intervalIntegral.integral_const_mul] at hint2
  have hmass := mass_le (by omega : 4 ≤ r) h1u
  have hJ1pos : (0 : ℝ) < J (r + 1) 1 := J_pos one_pos (r + 1)
  have hiJ : (∫ t in (1 : ℝ)..u, a r t * J r t) ≤ J (r + 1) u := by linarith
  have hKq : 0 ≤ K * q r u := mul_nonneg hK hq.le
  calc |∫ t in (1 : ℝ)..u, a r t * η t|
      ≤ ∫ t in (1 : ℝ)..u, |a r t * η t| := habs
    _ ≤ K * q r u * ∫ t in (1 : ℝ)..u, a r t * J r t := hint2
    _ ≤ K * q r u * J (r + 1) u := mul_le_mul_of_nonneg_left hiJ hKq
    _ = K * (J (r + 1) u * q r u) := by ring

/-! ## eq. `averaging-localization` (the `w_r`-weighted integrals) -/

/-- **eq. `averaging-localization`, continuous part**: the paper's
`∫_1^u J_{r+1}(t) D_{r-3}(t) dt ≪ J_{r+1}(u) w_r(u)`, with the explicit
constant `7` (internally `(12/5)e < 33/5 < 7`, via
`J_{r+1} ≤ (6/5)D_{r+1} = (6/5)·t·a_r` and
`a_r D_{r-3} ≤ 2 (J_{r+1}w_r)'`).  Requires `r ≥ 6`, `u ∈ [1, e]`. -/
theorem integral_J_D_le {r : ℕ} (hr : 6 ≤ r) {u : ℝ}
    (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    (∫ t in (1 : ℝ)..u, J (r + 1) t * D (r - 3) t)
      ≤ 7 * (J (r + 1) u * w r u) := by
  have h1u : (1 : ℝ) ≤ u := hu.1
  have hue : u ≤ Real.exp 1 := hu.2
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos h1u
  have hpt : ∀ t ∈ Set.Icc (1 : ℝ) u,
      J (r + 1) t * D (r - 3) t
        ≤ 33 / 5 * (a r t * (J r t + Rdefect r t) * w r t
            - J (r + 1) t * (w r t * (a (r - 2) t + a (r - 3) t + a (r - 4) t))) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht.1
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
    have ha := a_pos r t
    have hD3 : (0 : ℝ) < D (r - 3) t := D_pos ht0 (r - 3)
    -- `J_{r+1}(t) ≤ (6/5) D_{r+1}(t)` from `J_eq` and `E_{r-2}(t) ≥ 15 ≥ 5`
    have hJD : J (r + 1) t ≤ 6 / 5 * D (r + 1) t := by
      have hE5' : (5 : ℝ) ≤ E (r - 2) t := by
        have := fifteen_le_E (j := r - 2) (by omega) ht1
        linarith
      have hJe := J_eq (u := t) ht0 (r := r + 1) (by omega)
      rw [show r + 1 - 3 = r - 2 by omega] at hJe
      have hDp : (0 : ℝ) < D (r + 1) t := D_pos ht0 (r + 1)
      have hinv : 1 / E (r - 2) t ≤ 1 / 5 :=
        one_div_le_one_div_of_le (by norm_num) hE5'
      rw [hJe]
      linarith [mul_le_mul_of_nonneg_left hinv hDp.le]
    -- `D_{r+1}(t) = t · a_r(t)` (the identity `a_{r-1} = D_r/u`)
    have hDa : D (r + 1) t = a r t * t := by
      rw [a_eq_D_succ_div ht0.ne' (by omega : 2 ≤ r)]
      exact (div_mul_cancel₀ _ ht0.ne').symm
    -- `½ a_r D_{r-3} ≤ (J_{r+1}w_r)'` via `w_r D_r = D_{r-3}`
    have hwD : w r t * D r t = D (r - 3) t := by
      rw [w_eq_D_ratio ht0 hr]
      exact div_mul_cancel₀ _ (D_pos ht0 r).ne'
    have hchain : 1 / 2 * (a r t * D (r - 3) t)
        ≤ a r t * (J r t + Rdefect r t) * w r t
          - J (r + 1) t * (w r t * (a (r - 2) t + a (r - 3) t + a (r - 4) t)) := by
      have hhalf := half_w_mul_J_deriv_le hr ht1
      have hDJR : D r t ≤ J r t + Rdefect r t := by
        linarith [D_le_J ht0 r, Rdefect_nonneg ht0 r]
      have hw0 : (0 : ℝ) < w r t := w_pos hr t
      have hprod := mul_le_mul_of_nonneg_left hDJR (mul_nonneg hw0.le ha.le)
      rw [← hwD]
      linarith
    have haD3 : (0 : ℝ) ≤ a r t * D (r - 3) t := mul_nonneg ha.le hD3.le
    have hte : t ≤ 2.75 := by
      have := Real.exp_one_lt_d9
      linarith [ht.2]
    calc J (r + 1) t * D (r - 3) t
        ≤ 6 / 5 * D (r + 1) t * D (r - 3) t :=
          mul_le_mul_of_nonneg_right hJD hD3.le
      _ = 6 / 5 * t * (a r t * D (r - 3) t) := by rw [hDa]; ring
      _ ≤ 33 / 10 * (a r t * D (r - 3) t) := by
          linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2.75 - t) haD3]
      _ ≤ 33 / 5 * (a r t * (J r t + Rdefect r t) * w r t
            - J (r + 1) t * (w r t * (a (r - 2) t + a (r - 3) t + a (r - 4) t))) := by
          linarith
  have hcontL : Continuous fun t => J (r + 1) t * D (r - 3) t :=
    (continuous_J (r + 1)).mul (continuous_D (r - 3))
  have hint := intervalIntegral.integral_mono_on h1u
    (hcontL.intervalIntegrable (μ := volume) 1 u)
    (((continuous_J_mul_w_deriv hr).const_mul (33 / 5)).intervalIntegrable 1 u) hpt
  rw [intervalIntegral.integral_const_mul, ← J_mul_w_transport hr u] at hint
  have hJw1 : 0 ≤ J (r + 1) 1 * w r 1 :=
    mul_nonneg (J_pos one_pos (r + 1)).le (w_pos hr 1).le
  have hJwu : 0 ≤ J (r + 1) u * w r u :=
    mul_nonneg (J_pos hu0 (r + 1)).le (w_pos hr u).le
  linarith

/-- **eq. `averaging-localization`, endpoint atom**: the paper's
`α_r(u) ∫_1^u D_{r-3}(t) dt ≪ w_r(u)`, cleared of the division by
`J_{r+1}(u)`, with the explicit constant `7` (from `J_{r+1}(1) ≤ J_{r+1}(t)`
and `integral_J_D_le`).  Requires `r ≥ 6`, `u ∈ [1, e]`. -/
theorem endpoint_D_int {r : ℕ} (hr : 6 ≤ r) {u : ℝ}
    (hu : u ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :
    J (r + 1) 1 * (∫ t in (1 : ℝ)..u, D (r - 3) t)
      ≤ 7 * (J (r + 1) u * w r u) := by
  have h1u : (1 : ℝ) ≤ u := hu.1
  have hpt : ∀ t ∈ Set.Icc (1 : ℝ) u,
      J (r + 1) 1 * D (r - 3) t ≤ J (r + 1) t * D (r - 3) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
    exact mul_le_mul_of_nonneg_right (J_mono_phase (r + 1) zero_le_one ht.1)
      (D_pos ht0 (r - 3)).le
  have hint := intervalIntegral.integral_mono_on h1u
    (((continuous_D (r - 3)).const_mul (J (r + 1) 1)).intervalIntegrable (μ := volume) 1 u)
    (((continuous_J (r + 1)).mul (continuous_D (r - 3))).intervalIntegrable 1 u) hpt
  rw [intervalIntegral.integral_const_mul] at hint
  exact hint.trans (integral_J_D_le hr hu)

end Erdos320
