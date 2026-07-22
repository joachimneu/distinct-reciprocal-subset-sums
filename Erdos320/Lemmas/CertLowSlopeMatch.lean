import Erdos320.Lemmas.CoreClosedForm
import Erdos320.Lemmas.PhaseEnclosure
import Erdos320.Lemmas.CertLowCurvature

/-!
# Certificate `comp:low`, eq. `low-slope-match`, proved in Lean

The manuscript's display `eq:low-slope-match` asserts that on the wide low input
range `f ∈ [2.78, 2.80]` the slope-matched candidate constant
`f·y(f)/((log N₀)·Q₃*(u(f)))` stays below `1.11635`, where `y(f) = log x(f)`,
`u(f) = log₃ x(f)`, `x(f) = 65 659 969·f/log 65 659 969` is the low breakpoint
coordinate, and `N₀ = 65 659 969 = ⌊e¹⁸⌋`.  Here the tighter **core-level** form
`f·log x(f) < 1.1163·(log N₀ · Q̃₃(log₃ x(f)))`,
for the reference core `Q̃₃ = QrefCore3` and constant `1.1163 < 1.11635`, is
proved inside Lean.

Via the exact core slope identity `cert_qCore_slope`
(`Q̃₃(log₃ ξ) = ξ·log ξ·q̃'(ξ)`) and the linear relation `f = ξ·log N₀/N₀`, the
claim is, after dividing by the positive factor `log N₀·ξ·log ξ`, **equivalent**
to the clean rational slope bound
`q̃'(ξ) > 1/(1.1163·N₀)`     (⋆)
uniformly for `ξ = x(f)`, `f ∈ [2.78, 2.80]`.

`q̃'` is **antitone** on the low window (its second derivative is `≤ 0`, reusing
the public `lowCurvatureCert`), so its minimum over `ξ ∈ [x(2.78), x(2.80)]` is
attained at the right endpoint.  Bounding `x(f) ≤ 10 213 830` for `f ≤ 2.80`,
it suffices to verify (⋆) at the single rational point `ξ_hi = 10 213 830`.
There, `q̃'(ξ_hi) = Q̃₄'(u_hi)/(ξ_hi·log ξ_hi·log₂ ξ_hi)`, and the bound reads,
after clearing the (positive) denominators,
`1.1163·N₀·Q̃₄'(u_hi) > ξ_hi·log ξ_hi·log₂ ξ_hi`     (⋆⋆)
(numerically `4.58490·10⁸ > 4.58472·10⁸`, a thin `~4.6·10⁻⁵` relative margin).

Because the margin is thinner than the sharp phase window `S`'s enclosure width,
(⋆⋆) needs *point-specific* tight enclosures of `log ξ_hi`, `log₂ ξ_hi`,
`log₃ ξ_hi` at `ξ_hi = 10 213 830` (proved below by six `exp`-of-rational
anchors), together with the grouped-form lower bound `Q̃₄'(u_hi) ≥ 6.2553`.

The theorem `lowSlopeMatchCert` certifies the core-level slope-match bound
behind the paper's display `eq:low-slope-match`, on exactly the paper's input
range `f ∈ [2.78, 2.80]`.
-/

namespace Erdos320

/-! ## Point `exp`-of-rational anchors at `ξ_hi = 10 213 830`

Same technique as `PhaseEnclosure.lean`: split `exp t = (exp 1)^k · exp(frac)`,
bound `(exp 1)^k` by `Real.exp_one_lt_d9` / `Real.exp_one_gt_d9`, and the
fractional factor by the Taylor toolkit (`Real.exp_bound'` for upper,
`Real.sum_le_exp_of_nonneg` for lower). -/

/-- `exp 16.13924 ≤ 10 213 830` (pins `log 10 213 830` from below). -/
private theorem match_expA1 : Real.exp (16.13924 : ℝ) ≤ 10213830 := by
  have hsplit : Real.exp (16.13924 : ℝ)
      = Real.exp 1 ^ 16 * Real.exp (0.13924 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 16 ≤ (2.7182818286 : ℝ) ^ 16 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 16
  have hef : Real.exp (0.13924 : ℝ) ≤ (1.14940 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.13924 : ℝ) by norm_num)
      (by norm_num) (n := 7) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 16 * Real.exp (0.13924 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 16 * (1.14940 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 10213830 := by norm_num

/-- `10 213 830 ≤ exp 16.13927` (pins `log 10 213 830` from above). -/
private theorem match_expA2 : (10213830 : ℝ) ≤ Real.exp (16.13927 : ℝ) := by
  have hsplit : Real.exp (16.13927 : ℝ)
      = Real.exp 1 ^ 16 * Real.exp (0.13927 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 16 ≤ Real.exp 1 ^ 16 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 16
  have hef : (1.14942 : ℝ) ≤ Real.exp (0.13927 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.13927 : ℝ) by norm_num) 10)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (10213830 : ℝ) ≤ (2.7182818283 : ℝ) ^ 16 * (1.14942 : ℝ) := by norm_num
    _ ≤ Real.exp 1 ^ 16 * Real.exp (0.13927 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- `exp 2.781253 ≤ 16.13924` (pins `log₂ 10 213 830` from below). -/
private theorem match_expA3 : Real.exp (2.781253 : ℝ) ≤ 16.13924 := by
  have hsplit : Real.exp (2.781253 : ℝ)
      = Real.exp 1 ^ 2 * Real.exp (0.781253 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
  have hef : Real.exp (0.781253 : ℝ) ≤ (2.184208 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.781253 : ℝ) by norm_num)
      (by norm_num) (n := 12) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 2 * Real.exp (0.781253 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 2 * (2.184208 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 16.13924 := by norm_num

/-- `16.13927 ≤ exp 2.781256` (pins `log₂ 10 213 830` from above). -/
private theorem match_expA4 : (16.13927 : ℝ) ≤ Real.exp (2.781256 : ℝ) := by
  have hsplit : Real.exp (2.781256 : ℝ)
      = Real.exp 1 ^ 2 * Real.exp (0.781256 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 2
  have hef : (2.1842135 : ℝ) ≤ Real.exp (0.781256 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.781256 : ℝ) by norm_num) 14)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (16.13927 : ℝ) ≤ (2.7182818283 : ℝ) ^ 2 * (2.1842135 : ℝ) := by norm_num
    _ ≤ Real.exp 1 ^ 2 * Real.exp (0.781256 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- `exp 1.022901 ≤ 2.781253` (pins `log₃ 10 213 830` from below). -/
private theorem match_expA5 : Real.exp (1.022901 : ℝ) ≤ 2.781253 := by
  have hsplit : Real.exp (1.022901 : ℝ)
      = Real.exp 1 ^ 1 * Real.exp (0.022901 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 1 ≤ (2.7182818286 : ℝ) ^ 1 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 1
  have hef : Real.exp (0.022901 : ℝ) ≤ (1.0231653 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.022901 : ℝ) by norm_num)
      (by norm_num) (n := 6) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 1 * Real.exp (0.022901 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 1 * (1.0231653 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 2.781253 := by norm_num

/-- `2.781256 ≤ exp 1.022903` (pins `log₃ 10 213 830` from above). -/
private theorem match_expA6 : (2.781256 : ℝ) ≤ Real.exp (1.022903 : ℝ) := by
  have hsplit : Real.exp (1.022903 : ℝ)
      = Real.exp 1 ^ 1 * Real.exp (0.022903 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 1 ≤ Real.exp 1 ^ 1 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 1
  have hef : (1.0231671 : ℝ) ≤ Real.exp (0.022903 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.022903 : ℝ) by norm_num) 7)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (2.781256 : ℝ) ≤ (2.7182818283 : ℝ) ^ 1 * (1.0231671 : ℝ) := by norm_num
    _ ≤ Real.exp 1 ^ 1 * Real.exp (0.022903 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- **Point enclosure at `ξ_hi = 10 213 830`:**
`log ξ_hi ∈ [16.13924, 16.13927]`, `log₂ ξ_hi ∈ [2.781253, 2.781256]`,
`log₃ ξ_hi ∈ [1.022901, 1.022903]`. -/
private theorem match_pointEnclosure :
    (16.13924 : ℝ) ≤ Real.log 10213830 ∧ Real.log 10213830 ≤ 16.13927
      ∧ (2.781253 : ℝ) ≤ Real.log (Real.log 10213830)
        ∧ Real.log (Real.log 10213830) ≤ 2.781256
      ∧ (1.022901 : ℝ) ≤ iteratedLog 3 10213830
        ∧ iteratedLog 3 10213830 ≤ 1.022903 := by
  have hL_lo : (16.13924 : ℝ) ≤ Real.log 10213830 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]; exact match_expA1
  have hL_hi : Real.log 10213830 ≤ 16.13927 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; exact match_expA2
  have hlogpos : (0 : ℝ) < Real.log 10213830 := by linarith
  have hLL_lo : (2.781253 : ℝ) ≤ Real.log (Real.log 10213830) := by
    have h1 : (2.781253 : ℝ) ≤ Real.log 16.13924 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]; exact match_expA3
    have h2 : Real.log 16.13924 ≤ Real.log (Real.log 10213830) :=
      Real.log_le_log (by norm_num) hL_lo
    linarith
  have hLL_hi : Real.log (Real.log 10213830) ≤ 2.781256 := by
    have h1 : Real.log (Real.log 10213830) ≤ Real.log 16.13927 :=
      Real.log_le_log hlogpos hL_hi
    have h2 : Real.log 16.13927 ≤ 2.781256 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]; exact match_expA4
    linarith
  have hloglogpos : (0 : ℝ) < Real.log (Real.log 10213830) := by linarith
  refine ⟨hL_lo, hL_hi, hLL_lo, hLL_hi, ?_, ?_⟩
  · rw [cert_iteratedLog_three_eq]
    have h1 : (1.022901 : ℝ) ≤ Real.log 2.781253 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]; exact match_expA5
    have h2 : Real.log 2.781253 ≤ Real.log (Real.log (Real.log 10213830)) :=
      Real.log_le_log (by norm_num) hLL_lo
    linarith
  · rw [cert_iteratedLog_three_eq]
    have h1 : Real.log (Real.log (Real.log 10213830)) ≤ Real.log 2.781256 :=
      Real.log_le_log hloglogpos hLL_hi
    have h2 : Real.log 2.781256 ≤ 1.022903 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]; exact match_expA6
    linarith

/-! ## Endpoint slope bound (⋆⋆) -/

set_option maxHeartbeats 1000000 in
/-- Grouped-form lower bound `Q̃₄'(log₃ 10 213 830) ≥ 6.2553` from the closed
form of `Q̃₄'` (`CoreClosedForm.lean`) and the point enclosure above. -/
private theorem match_Qp_lb :
    (6.2553 : ℝ) ≤ deriv QrefCore4 (iteratedLog 3 10213830) := by
  have hξ39 : (3.9e6 : ℝ) < 10213830 := by norm_num
  have hu1 : 1 < iteratedLog 3 10213830 := cert_one_lt_iteratedLog_three hξ39
  have hu0 : (0 : ℝ) < iteratedLog 3 10213830 := by linarith
  obtain ⟨_, _, hLL_lo, hLL_hi, hu_lo, hu_hi⟩ := match_pointEnclosure
  obtain ⟨hL_lo, hL_hi, _, _, _, _⟩ := match_pointEnclosure
  have h15 : (15 : ℝ) ≤ 10213830 := by norm_num
  have hE1 : E 1 (iteratedLog 3 10213830) = Real.log (Real.log 10213830) :=
    E1_iteratedLog3 h15
  have hE2 : E 2 (iteratedLog 3 10213830) = Real.log 10213830 := E2_iteratedLog3 h15
  have he1pos : 0 < E 1 (iteratedLog 3 10213830) := E_pos_of_one_le (by omega) _
  have he2pos : 0 < E 2 (iteratedLog 3 10213830) := E_pos_of_one_le (by omega) _
  have he3pos : 0 < E 3 (iteratedLog 3 10213830) := E_pos_of_one_le (by omega) _
  set u := iteratedLog 3 10213830 with hu
  set e1 := E 1 u with he1def
  set e2 := E 2 u with he2def
  set e3 := E 3 u with he3def
  have he1ne : e1 ≠ 0 := he1pos.ne'
  have he2ne : e2 ≠ 0 := he2pos.ne'
  -- numeric bounds on `e1 = log₂ ξ`, `e2 = log ξ`, `u = log₃ ξ`
  have he1lo : (2.781253 : ℝ) ≤ e1 := by rw [hE1]; exact hLL_lo
  have he1hi : e1 ≤ 2.781256 := by rw [hE1]; exact hLL_hi
  have he2lo : (16.13924 : ℝ) ≤ e2 := by rw [hE2]; exact hL_lo
  have he2hi : e2 ≤ 16.13927 := by rw [hE2]; exact hL_hi
  have hulo : (1.022901 : ℝ) ≤ u := hu_lo
  have huhi : u ≤ 1.022903 := hu_hi
  -- looser (W-window) bounds, to discharge the remainder positivity by `gcongr`
  have g1lo : (2.778213 : ℝ) ≤ e1 := by linarith
  have g1hi : e1 ≤ 2.783744 := by linarith
  have g2lo : (16.090256 : ℝ) ≤ e2 := by linarith
  have g2hi : e2 ≤ 16.179468 := by linarith
  have g3lo : (1.021808 : ℝ) ≤ u := by linarith
  have g3hi : u ≤ 1.023797 := by linarith
  have he1nn : (0 : ℝ) ≤ e1 := he1pos.le
  have he2nn : (0 : ℝ) ≤ e2 := he2pos.le
  have hunn : (0 : ℝ) ≤ u := hu0.le
  -- grouped closed form: decoupled leading part + `E₃`-free remainder
  have hgroup := cert_grouped_deriv_QrefCore4 hu0
  rw [← he1def, ← he2def, ← he3def] at hgroup
  rw [hgroup]
  -- remainder ≥ 0 (dominant positive monomials outweigh the four negatives)
  have hRp0 : (0 : ℝ) ≤ 2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
      + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
      + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
      + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3 := by
    have b1 : (2.778213 : ℝ) ^ 3 * 16.090256 ^ 3 ≤ e1 ^ 3 * e2 ^ 3 := by gcongr
    have b2 : (1.021808 : ℝ) * 2.778213 ^ 4 * 16.090256 ^ 3
        ≤ u * e1 ^ 4 * e2 ^ 3 := by gcongr
    have n1 : e1 ^ 2 ≤ (2.783744 : ℝ) ^ 2 := by gcongr
    have n2 : e1 ^ 2 * e2 ^ 2 ≤ (2.783744 : ℝ) ^ 2 * 16.179468 ^ 2 := by gcongr
    have n3 : e1 ^ 3 * e2 ^ 2 ≤ (2.783744 : ℝ) ^ 3 * 16.179468 ^ 2 := by gcongr
    have n4 : u * e1 ^ 3 * e2 ^ 2
        ≤ (1.023797 : ℝ) * 2.783744 ^ 3 * 16.179468 ^ 2 := by gcongr
    have hpos : (0 : ℝ) ≤ 2 * e1 + e1 * e2 + 2 * e1 ^ 3 + e1 ^ 3 * e2
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 := by positivity
    nlinarith [b1, b2, n1, n2, n3, n4, hpos]
  have hden : (0 : ℝ) < e1 ^ 2 * e2 ^ 2 * e3 := by positivity
  have hrem : (0 : ℝ) ≤ (2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
      + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
      + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
      + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3) / (e1 ^ 2 * e2 ^ 2 * e3) :=
    div_nonneg hRp0 hden.le
  -- the leading part is ≥ 6.2553, via the correlated group `A = e1 + u·e1`
  have hAlo : (5.62619 : ℝ) ≤ e1 + u * e1 := by
    nlinarith [mul_le_mul hulo he1lo (by norm_num : (0 : ℝ) ≤ 2.781253) hu0.le, he1lo]
  have hAe2 : e1 / e2 + u * e1 / e2 ≤ 0.348606 := by
    rw [← add_div, div_le_iff₀ he2pos]
    nlinarith [he1hi, he2lo,
      mul_le_mul huhi he1hi he1pos.le (by norm_num : (0 : ℝ) ≤ 1.022903)]
  have hrecip : 1 / (e1 * e2) ≤ 0.022279 := by
    rw [div_le_iff₀ (mul_pos he1pos he2pos)]
    nlinarith [mul_le_mul he1lo he2lo (by norm_num : (0 : ℝ) ≤ 16.13924) he1pos.le]
  linarith [hAlo, hAe2, hrecip, hrem]

set_option maxHeartbeats 1000000 in
/-- **(⋆) at the right endpoint** (via the cleared-denominator form (⋆⋆)):
`q̃'(10 213 830) > 1/(1.1163·N₀)`. -/
private theorem match_endpoint_slope :
    1 / (1.1163 * 65659969) < deriv qCore 10213830 := by
  have hξ39 : (3.9e6 : ℝ) < 10213830 := by norm_num
  obtain ⟨hL_lo, hL_hi, hLL_lo, hLL_hi, _, _⟩ := match_pointEnclosure
  have hlogpos : (0 : ℝ) < Real.log 10213830 := by linarith
  have hloglogpos : (0 : ℝ) < Real.log (Real.log 10213830) := by linarith
  have hQlb := match_Qp_lb
  -- `q̃'(ξ_hi) = Q̃₄'(u_hi) / (ξ_hi·log ξ_hi·log₂ ξ_hi)`
  have hdq : deriv qCore 10213830
      = deriv QrefCore4 (iteratedLog 3 10213830)
        / (10213830 * Real.log 10213830 * Real.log (Real.log 10213830)) := by
    rw [cert_deriv_qCore_eq hξ39, cert_iteratedLogThreeDeriv, ← div_eq_mul_inv]
  have hDpos : (0 : ℝ) < 10213830 * Real.log 10213830 * Real.log (Real.log 10213830) := by
    positivity
  have hcoef : (0 : ℝ) < 1.1163 * 65659969 := by norm_num
  -- (⋆⋆): the denominator product is below `1.1163·N₀·Q̃₄'`
  have hRHS : 10213830 * Real.log 10213830 * Real.log (Real.log 10213830)
      ≤ 10213830 * 16.13927 * 2.781256 := by
    have step1 : (10213830 : ℝ) * Real.log 10213830 ≤ 10213830 * 16.13927 := by
      nlinarith [hL_hi]
    calc 10213830 * Real.log 10213830 * Real.log (Real.log 10213830)
        ≤ (10213830 * 16.13927) * 2.781256 :=
          mul_le_mul step1 hLL_hi hloglogpos.le (by positivity)
      _ = 10213830 * 16.13927 * 2.781256 := by ring
  have hnum : (10213830 : ℝ) * 16.13927 * 2.781256 < 1.1163 * 65659969 * 6.2553 := by
    norm_num
  have hmono : (1.1163 : ℝ) * 65659969 * 6.2553
      ≤ 1.1163 * 65659969 * deriv QrefCore4 (iteratedLog 3 10213830) := by
    nlinarith [hQlb]
  have key : 10213830 * Real.log 10213830 * Real.log (Real.log 10213830)
      < deriv QrefCore4 (iteratedLog 3 10213830) * (1.1163 * 65659969) := by
    nlinarith [hRHS, hnum, hmono]
  rw [hdq, div_lt_div_iff₀ hcoef hDpos, one_mul]
  exact key

/-! ## Antitonicity of `q̃'` on the low window -/

set_option maxHeartbeats 1000000 in
/-- `q̃'` is antitone on `[10 140 000, 10 214 000]`: its second derivative is
`≤ 0` there (via the public `lowCurvatureCert` with `f = 2.79`, whose chord
window `[0.96·x(2.79), 1.04·x(2.79)]` contains the whole interval). -/
private theorem match_antitone :
    AntitoneOn (deriv qCore) (Set.Icc (10140000 : ℝ) 10214000) := by
  obtain ⟨hLlo, hLhi⟩ := cert_log_N0_bounds
  have hLpos : (0 : ℝ) < Real.log 65659969 := by linarith
  have hw1 : 0.96 * lowBreakpointX 2.79 ≤ 10140000 := by
    rw [lowBreakpointX,
      show (0.96 : ℝ) * (65659969 * 2.79 / Real.log 65659969)
        = 0.96 * 65659969 * 2.79 / Real.log 65659969 from by ring, div_le_iff₀ hLpos]
    nlinarith [hLlo]
  have hw2 : (10214000 : ℝ) ≤ 1.04 * lowBreakpointX 2.79 := by
    rw [lowBreakpointX,
      show (1.04 : ℝ) * (65659969 * 2.79 / Real.log 65659969)
        = 1.04 * 65659969 * 2.79 / Real.log 65659969 from by ring, le_div_iff₀ hLpos]
    nlinarith [hLhi]
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
  · intro x hx
    rw [Set.mem_Icc] at hx
    have hx39 : (3.9e6 : ℝ) < x := by linarith [hx.1]
    exact ((cert_hasDerivAt_deriv_qCore hx39).continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Icc, Set.mem_Ioo] at hx
    have hx39 : (3.9e6 : ℝ) < x := by linarith [hx.1]
    exact ((cert_hasDerivAt_deriv_qCore hx39).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Icc, Set.mem_Ioo] at hx
    have hx1 : 0.96 * lowBreakpointX 2.79 ≤ x := by linarith [hw1, hx.1]
    have hx2 : x ≤ 1.04 * lowBreakpointX 2.79 := by linarith [hw2, hx.2]
    exact (lowCurvatureCert 2.79 (by norm_num) (by norm_num) x hx1 hx2).2.1

/-! ## The proved certificate -/

set_option maxHeartbeats 1000000 in
/-- **Proved core-level input to `eq:low-slope-match`**:
`f·log x(f) < 1.1163·(log N₀ · Q̃₃(log₃ x(f)))` for every `f ∈ [2.78, 2.80]`,
where `x(f) = 65 659 969·f/log 65 659 969` and `N₀ = 65 659 969`. -/
theorem lowSlopeMatchCert (f : ℝ) (h1 : (2.78 : ℝ) ≤ f) (h2 : f ≤ 2.80) :
    f * Real.log (lowBreakpointX f)
      < 1.1163 * (Real.log 65659969 * QrefCore3 (iteratedLog 3 (lowBreakpointX f))) := by
  obtain ⟨hLlo, hLhi⟩ := cert_log_N0_bounds
  have hLpos : (0 : ℝ) < Real.log 65659969 := by linarith
  set ξ := lowBreakpointX f with hξdef
  -- `ξ ∈ [10 140 000, 10 213 830] ⊆ [10 140 000, 10 214 000]`
  have hξlo : (10140000 : ℝ) ≤ ξ := by
    rw [hξdef, lowBreakpointX, le_div_iff₀ hLpos]; nlinarith [h1, hLhi]
  have hξhi30 : ξ ≤ 10213830 := by
    rw [hξdef, lowBreakpointX, div_le_iff₀ hLpos]; nlinarith [h2, hLlo]
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hξpos : (0 : ℝ) < ξ := by linarith
  have hlogξpos : (0 : ℝ) < Real.log ξ := by linarith [(cert_logs_pos hξ39).1]
  -- antitonicity: `q̃'(ξ) ≥ q̃'(10 213 830) > 1/(1.1163·N₀)`
  have hmemξ : ξ ∈ Set.Icc (10140000 : ℝ) 10214000 := ⟨hξlo, by linarith [hξhi30]⟩
  have hmemhi : (10213830 : ℝ) ∈ Set.Icc (10140000 : ℝ) 10214000 :=
    ⟨by norm_num, by norm_num⟩
  have hanti : deriv qCore 10213830 ≤ deriv qCore ξ :=
    match_antitone hmemξ hmemhi hξhi30
  have hderiv : 1 / (1.1163 * 65659969) < deriv qCore ξ :=
    lt_of_lt_of_le match_endpoint_slope hanti
  -- slope identity `Q̃₃(log₃ ξ) = ξ·log ξ·q̃'(ξ)` and `65659969·f = ξ·log N₀`
  have hslope : QrefCore3 (iteratedLog 3 ξ) = ξ * Real.log ξ * deriv qCore ξ := by
    have hs := cert_qCore_slope hξ39
    rw [eq_div_iff hlogξpos.ne'] at hs
    rw [← hs]; ring
  have hf : f = ξ * Real.log 65659969 / 65659969 := by
    rw [hξdef, lowBreakpointX]; field_simp
  -- `1 < deriv·(1.1163·N₀)`
  have hd1 : (1 : ℝ) < deriv qCore ξ * (1.1163 * 65659969) := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 1.1163 * 65659969)] at hderiv
    exact hderiv
  have hpos : (0 : ℝ) < ξ * Real.log 65659969 * Real.log ξ := by positivity
  have hmul := mul_lt_mul_of_pos_left hd1 hpos
  rw [hf, hslope]
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by norm_num : (0 : ℝ) < 65659969)]
  nlinarith [hmul]

end Erdos320
