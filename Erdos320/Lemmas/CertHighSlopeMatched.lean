import Erdos320.Lemmas.CoreClosedForm
import Erdos320.Lemmas.PhaseEnclosureHigh
import Erdos320.Lemmas.CertLowCurvature

/-!
# Certificate `comp:high`, eq. `slope-matched-monotonicity`, proved in Lean

The manuscript's directed-interval certificate asserts that on the wide high
input range `f ∈ [3.24, 46]` the slope-matched candidate constant computed from
the core stays **above** `1.1794`, in the form
`1.1794·(log N₁ · Q̃₃(log₃ x(f))) < f·log x(f)`,
where
`x(f) = N₁·f/log N₁` is the high breakpoint coordinate and
`N₁ = 16 948 892 444 103 337 141 417 836 114 = ⌊e⁶⁵⌋`.  Here that evaluation is
proved inside Lean.

Via the exact core slope identity `cert_qCore_slope`
(`Q̃₃(log₃ ξ) = ξ·log ξ·q̃'(ξ)`) and the linear relation `f = ξ·log N₁/N₁`, the
claim is, after dividing by the positive factor `log N₁·ξ·log ξ`, **equivalent**
to the clean rational slope bound
`q̃'(ξ) < 1/(1.1794·N₁)`     (⋆)
uniformly for `ξ = x(f)`, `f ∈ [3.24, 46]`.

`q̃'` is **antitone** on the high window (its second derivative is `≤ 0` there,
proved below by the same chain-rule/closed-form route as `CertLowCurvature.lean`
but with the high-window enclosures of `PhaseEnclosureHigh.lean`), so its maximum
over `ξ = x(f)`, `f ∈ [3.24, 46]`, is attained at the *left* endpoint `f = 3.24`.
Bounding `x(f) ≥ x(3.24) ≥ N₁·3.24/65.01 ≥ 8.447·10²⁶` (using `log N₁ ≤ 65.01`),
it suffices to verify (⋆) at the single rational point `ξ_lo = 8.447·10²⁶`.
There, `q̃'(ξ_lo) = Q̃₄'(u_lo)/(ξ_lo·log ξ_lo·log₂ ξ_lo)`, and the bound reads,
after clearing the (positive) denominators,
`Q̃₄'(u_lo)·(1.1794·N₁) < ξ_lo·log ξ_lo·log₂ ξ_lo`     (⋆⋆)
(numerically `2.161450·10²⁹ < 2.161481·10²⁹`, a thin `~1.5·10⁻⁵` relative
margin).

Because the margin is thinner than what a window-wide enclosure could deliver,
(⋆⋆)
needs *point-specific* tight enclosures of `log ξ_lo`, `log₂ ξ_lo`,
`log₃ ξ_lo` at `ξ_lo = 8.447·10²⁶` (proved below by six `exp`-of-rational
anchors), together with the grouped-form upper bound `Q̃₄'(u_lo) ≤ 10.813`.

**Route note (rational endpoint anchor).**  The endpoint analysis is
carried out at the *fixed rational* point `ξ_lo = 8.447·10²⁶` rather than at the
scale `x(3.24)` itself (which depends on the irrational `log N₁`).  Working at
`x(3.24)` would leave the loose enclosure `log N₁ ∈ [64.99, 65.01]` inside the
`~830`-scale endpoint inequality, and its `0.01` width there destroys the thin
`~1.5·10⁻⁵` margin (the honest inequality then fails).  Evaluating instead at a
rational `ξ_lo ≤ x(3.24)` removes `log N₁` from the endpoint check entirely
(only the integer `N₁` remains, in the clean rational threshold `1/(1.1794·N₁)`),
which is exactly why the low sibling `CertLowSlopeMatch.lean` also anchors at a
rational endpoint.  All stated numeric targets are verified outer bounds.

The theorem `highSlopeMatchedCert` certifies the core-level lower bound behind
the paper's slope-matched monotonicity display `eq:slope-matched-monotonicity`
(and its consequence `Ĉ > 1.1793`), on exactly the paper's input range
`f ∈ [3.24, 46]`.
-/

namespace Erdos320

/-! ## Point `exp`-of-rational anchors at `ξ_lo = 8.447·10²⁶`

Same technique as `PhaseEnclosure.lean` / `PhaseEnclosureHigh.lean`: split
`exp t = (exp 1)^k · exp(frac)`, bound `(exp 1)^k` by `Real.exp_one_lt_d9` /
`Real.exp_one_gt_d9`, and the fractional factor by the Taylor toolkit
(`Real.exp_bound'` for upper, `Real.sum_le_exp_of_nonneg` for lower). -/

/-- `exp 62.0010 ≤ 8.447·10²⁶` (pins `log ξ_lo` from below). -/
private theorem highMatch_expB1 : Real.exp (62.0010 : ℝ) ≤ 8.447e26 := by
  have hsplit : Real.exp (62.0010 : ℝ)
      = Real.exp 1 ^ 62 * Real.exp (0.0010 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 62 ≤ (2.7182818286 : ℝ) ^ 62 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 62
  have hef : Real.exp (0.0010 : ℝ) ≤ (1.0010006 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.0010 : ℝ) by norm_num)
      (by norm_num) (n := 6) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 62 * Real.exp (0.0010 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 62 * (1.0010006 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 8.447e26 := by norm_num

/-- `8.447·10²⁶ ≤ exp 62.0011` (pins `log ξ_lo` from above). -/
private theorem highMatch_expB2 : (8.447e26 : ℝ) ≤ Real.exp (62.0011 : ℝ) := by
  have hsplit : Real.exp (62.0011 : ℝ)
      = Real.exp 1 ^ 62 * Real.exp (0.0011 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 62 ≤ Real.exp 1 ^ 62 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 62
  have hef : (1.0011006 : ℝ) ≤ Real.exp (0.0011 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.0011 : ℝ) by norm_num) 5)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (8.447e26 : ℝ) ≤ (2.7182818283 : ℝ) ^ 62 * (1.0011006 : ℝ) := by norm_num
    _ ≤ Real.exp 1 ^ 62 * Real.exp (0.0011 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- `exp 4.127149 ≤ 62.0010` (pins `log₂ ξ_lo` from below). -/
private theorem highMatch_expB3 : Real.exp (4.127149 : ℝ) ≤ 62.0010 := by
  have hsplit : Real.exp (4.127149 : ℝ)
      = Real.exp 1 ^ 4 * Real.exp (0.127149 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
  have hef : Real.exp (0.127149 : ℝ) ≤ (1.1355863 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.127149 : ℝ) by norm_num)
      (by norm_num) (n := 8) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 4 * Real.exp (0.127149 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 4 * (1.1355863 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 62.0010 := by norm_num

/-- `62.0011 ≤ exp 4.127153` (pins `log₂ ξ_lo` from above). -/
private theorem highMatch_expB4 : (62.0011 : ℝ) ≤ Real.exp (4.127153 : ℝ) := by
  have hsplit : Real.exp (4.127153 : ℝ)
      = Real.exp 1 ^ 4 * Real.exp (0.127153 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 4
  have hef : (1.1355907 : ℝ) ≤ Real.exp (0.127153 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.127153 : ℝ) by norm_num) 9)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (62.0011 : ℝ) ≤ (2.7182818283 : ℝ) ^ 4 * (1.1355907 : ℝ) := by norm_num
    _ ≤ Real.exp 1 ^ 4 * Real.exp (0.127153 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- `exp 1.417586 ≤ 4.127149` (pins `log₃ ξ_lo` from below). -/
private theorem highMatch_expB5 : Real.exp (1.417586 : ℝ) ≤ 4.127149 := by
  have hsplit : Real.exp (1.417586 : ℝ)
      = Real.exp 1 ^ 1 * Real.exp (0.417586 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 ^ 1 ≤ (2.7182818286 : ℝ) ^ 1 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 1
  have hef : Real.exp (0.417586 : ℝ) ≤ (1.5182920 : ℝ) := by
    refine (Real.exp_bound' (show (0 : ℝ) ≤ (0.417586 : ℝ) by norm_num)
      (by norm_num) (n := 10) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 1 * Real.exp (0.417586 : ℝ)
      ≤ (2.7182818286 : ℝ) ^ 1 * (1.5182920 : ℝ) :=
        mul_le_mul he1 hef (Real.exp_pos _).le (by positivity)
    _ ≤ 4.127149 := by norm_num

/-- `4.127153 ≤ exp 1.417589` (pins `log₃ ξ_lo` from above). -/
private theorem highMatch_expB6 : (4.127153 : ℝ) ≤ Real.exp (1.417589 : ℝ) := by
  have hsplit : Real.exp (1.417589 : ℝ)
      = Real.exp 1 ^ 1 * Real.exp (0.417589 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he1 : (2.7182818283 : ℝ) ^ 1 ≤ Real.exp 1 ^ 1 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 1
  have hef : (1.5182965 : ℝ) ≤ Real.exp (0.417589 : ℝ) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ (0.417589 : ℝ) by norm_num) 11)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hsplit]
  calc (4.127153 : ℝ) ≤ (2.7182818283 : ℝ) ^ 1 * (1.5182965 : ℝ) := by norm_num
    _ ≤ Real.exp 1 ^ 1 * Real.exp (0.417589 : ℝ) :=
        mul_le_mul he1 hef (by norm_num) (by positivity)

/-- **Point enclosure at `ξ_lo = 8.447·10²⁶`:**
`log ξ_lo ∈ [62.0010, 62.0011]`, `log₂ ξ_lo ∈ [4.127149, 4.127153]`,
`log₃ ξ_lo ∈ [1.417586, 1.417589]`. -/
private theorem highMatch_pointEnclosure :
    (62.0010 : ℝ) ≤ Real.log 8.447e26 ∧ Real.log 8.447e26 ≤ 62.0011
      ∧ (4.127149 : ℝ) ≤ Real.log (Real.log 8.447e26)
        ∧ Real.log (Real.log 8.447e26) ≤ 4.127153
      ∧ (1.417586 : ℝ) ≤ iteratedLog 3 8.447e26
        ∧ iteratedLog 3 8.447e26 ≤ 1.417589 := by
  have hL_lo : (62.0010 : ℝ) ≤ Real.log 8.447e26 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]; exact highMatch_expB1
  have hL_hi : Real.log 8.447e26 ≤ 62.0011 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; exact highMatch_expB2
  have hlogpos : (0 : ℝ) < Real.log 8.447e26 := by linarith
  have hLL_lo : (4.127149 : ℝ) ≤ Real.log (Real.log 8.447e26) := by
    have h1 : (4.127149 : ℝ) ≤ Real.log 62.0010 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]; exact highMatch_expB3
    have h2 : Real.log 62.0010 ≤ Real.log (Real.log 8.447e26) :=
      Real.log_le_log (by norm_num) hL_lo
    linarith
  have hLL_hi : Real.log (Real.log 8.447e26) ≤ 4.127153 := by
    have h1 : Real.log (Real.log 8.447e26) ≤ Real.log 62.0011 :=
      Real.log_le_log hlogpos hL_hi
    have h2 : Real.log 62.0011 ≤ 4.127153 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]; exact highMatch_expB4
    linarith
  have hloglogpos : (0 : ℝ) < Real.log (Real.log 8.447e26) := by linarith
  refine ⟨hL_lo, hL_hi, hLL_lo, hLL_hi, ?_, ?_⟩
  · rw [cert_iteratedLog_three_eq]
    have h1 : (1.417586 : ℝ) ≤ Real.log 4.127149 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]; exact highMatch_expB5
    have h2 : Real.log 4.127149 ≤ Real.log (Real.log (Real.log 8.447e26)) :=
      Real.log_le_log (by norm_num) hLL_lo
    linarith
  · rw [cert_iteratedLog_three_eq]
    have h1 : Real.log (Real.log (Real.log 8.447e26)) ≤ Real.log 4.127153 :=
      Real.log_le_log hloglogpos hLL_hi
    have h2 : Real.log 4.127153 ≤ 1.417589 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]; exact highMatch_expB6
    linarith

/-! ## Endpoint slope bound (⋆⋆) -/

set_option maxHeartbeats 1000000 in
/-- Grouped-form upper bound `Q̃₄'(log₃ ξ_lo) ≤ 10.813` from the closed form of
`Q̃₄'` (`CoreClosedForm.lean`) and the point enclosure above. -/
private theorem highMatch_Qp_ub :
    deriv QrefCore4 (iteratedLog 3 8.447e26) ≤ 10.813 := by
  have hξ39 : (3.9e6 : ℝ) < 8.447e26 := by norm_num
  have hu1 : 1 < iteratedLog 3 8.447e26 := cert_one_lt_iteratedLog_three hξ39
  have hu0 : (0 : ℝ) < iteratedLog 3 8.447e26 := by linarith
  obtain ⟨hL_lo, hL_hi, hLL_lo, hLL_hi, hu_lo, hu_hi⟩ := highMatch_pointEnclosure
  have h15 : (15 : ℝ) ≤ 8.447e26 := by norm_num
  have hE1 : E 1 (iteratedLog 3 8.447e26) = Real.log (Real.log 8.447e26) :=
    E1_iteratedLog3 h15
  have hE2 : E 2 (iteratedLog 3 8.447e26) = Real.log 8.447e26 := E2_iteratedLog3 h15
  have he1pos : 0 < E 1 (iteratedLog 3 8.447e26) := E_pos_of_one_le (by omega) _
  have he2pos : 0 < E 2 (iteratedLog 3 8.447e26) := E_pos_of_one_le (by omega) _
  have he3pos : 0 < E 3 (iteratedLog 3 8.447e26) := E_pos_of_one_le (by omega) _
  have he3eq : E 3 (iteratedLog 3 8.447e26) = 8.447e26 := cert_E_three_iteratedLog h15
  set u := iteratedLog 3 8.447e26 with hu
  set e1 := E 1 u with he1def
  set e2 := E 2 u with he2def
  set e3 := E 3 u with he3def
  have he1ne : e1 ≠ 0 := he1pos.ne'
  have he2ne : e2 ≠ 0 := he2pos.ne'
  have he1lo : (4.127149 : ℝ) ≤ e1 := by rw [hE1]; exact hLL_lo
  have he1hi : e1 ≤ 4.127153 := by rw [hE1]; exact hLL_hi
  have he2lo : (62.0010 : ℝ) ≤ e2 := by rw [hE2]; exact hL_lo
  have he2hi : e2 ≤ 62.0011 := by rw [hE2]; exact hL_hi
  have hulo : (1.417586 : ℝ) ≤ u := hu_lo
  have huhi : u ≤ 1.417589 := hu_hi
  have he3lo : (8.447e26 : ℝ) ≤ e3 := he3eq.ge
  have he1nn : (0 : ℝ) ≤ e1 := he1pos.le
  have he2nn : (0 : ℝ) ≤ e2 := he2pos.le
  have hunn : (0 : ℝ) ≤ u := hu0.le
  -- grouped closed form: decoupled leading part + `E₃`-free remainder
  have hgroup := cert_grouped_deriv_QrefCore4 hu0
  rw [← he1def, ← he2def, ← he3def] at hgroup
  rw [hgroup]
  -- remainder is nonnegative and negligible (`E₃ = ξ_lo ≥ 8·10²⁶`)
  have hden : (0 : ℝ) < e1 ^ 2 * e2 ^ 2 * e3 := by positivity
  have hden_lo : (5e30 : ℝ) ≤ e1 ^ 2 * e2 ^ 2 * e3 := by
    have h : (4.127149 : ℝ) ^ 2 * 62.0010 ^ 2 * 8.447e26 ≤ e1 ^ 2 * e2 ^ 2 * e3 := by
      gcongr
    nlinarith [h]
  have hRpden_hi : (2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
      + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
      + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
      + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3) / (e1 ^ 2 * e2 ^ 2 * e3) ≤ 0.00001 := by
    rw [div_le_iff₀ hden]
    have hp : 2 + 2 * e1 + e1 * e2 + 2 * e1 ^ 3 + e1 ^ 3 * e2 + e1 ^ 3 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3
        ≤ 2 + 2 * 4.127153 + 4.127153 * 62.0011 + 2 * 4.127153 ^ 3
            + 4.127153 ^ 3 * 62.0011 + 4.127153 ^ 3 * 62.0011 ^ 3
            + 2 * 1.417589 * 4.127153 ^ 3 + 1.417589 * 4.127153 ^ 3 * 62.0011
            + 1.417589 * 4.127153 ^ 3 * 62.0011 ^ 3
            + 1.417589 * 4.127153 ^ 4 * 62.0011 ^ 3 := by gcongr
    have hn : (0 : ℝ) ≤ e1 ^ 2 + e1 ^ 2 * e2 ^ 2 + e1 ^ 3 * e2 ^ 2 + u * e1 ^ 3 * e2 ^ 2 := by
      positivity
    nlinarith [hden_lo, hp, hn]
  -- termwise reciprocal enclosures for the leading part
  have tb_ue1_hi : u * e1 ≤ 5.850607 := by
    nlinarith [mul_le_mul huhi he1hi he1pos.le (by norm_num : (0 : ℝ) ≤ 1.417589)]
  have tb_e1e2r_lo : (0.066565 : ℝ) ≤ e1 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [he1lo, he2hi]
  have tb_ue1e2r_lo : (0.094362 : ℝ) ≤ u * e1 / e2 := by
    rw [le_div_iff₀ he2pos]
    nlinarith [mul_le_mul hulo he1lo (by norm_num : (0 : ℝ) ≤ 4.127149) hu0.le, he2hi]
  have tb_recip_lo : (0.003907 : ℝ) ≤ 1 / (e1 * e2) := by
    rw [le_div_iff₀ (mul_pos he1pos he2pos)]; nlinarith [he1hi, he2hi]
  linarith [he1hi, tb_ue1_hi, tb_e1e2r_lo, tb_ue1e2r_lo, tb_recip_lo, hRpden_hi]

set_option maxHeartbeats 1000000 in
/-- **(⋆) at the left endpoint** (proved via the cleared-denominator form
(⋆⋆)): `q̃'(8.447·10²⁶) < 1/(1.1794·N₁)`. -/
private theorem highMatch_endpoint_slope :
    deriv qCore 8.447e26 < 1 / (1.1794 * 16948892444103337141417836114) := by
  have hξ39 : (3.9e6 : ℝ) < 8.447e26 := by norm_num
  obtain ⟨hL_lo, hL_hi, hLL_lo, hLL_hi, _, _⟩ := highMatch_pointEnclosure
  have hlogpos : (0 : ℝ) < Real.log 8.447e26 := by linarith
  have hloglogpos : (0 : ℝ) < Real.log (Real.log 8.447e26) := by linarith
  have hQub := highMatch_Qp_ub
  -- `q̃'(ξ_lo) = Q̃₄'(u_lo) / (ξ_lo·log ξ_lo·log₂ ξ_lo)`
  have hdq : deriv qCore 8.447e26
      = deriv QrefCore4 (iteratedLog 3 8.447e26)
        / (8.447e26 * Real.log 8.447e26 * Real.log (Real.log 8.447e26)) := by
    rw [cert_deriv_qCore_eq hξ39, cert_iteratedLogThreeDeriv, ← div_eq_mul_inv]
  have hDpos : (0 : ℝ) < 8.447e26 * Real.log 8.447e26 * Real.log (Real.log 8.447e26) := by
    positivity
  have hcoef : (0 : ℝ) < 1.1794 * 16948892444103337141417836114 := by norm_num
  -- (⋆⋆): `1.1794·N₁·Q̃₄'` is below the denominator product
  have hRHS : 8.447e26 * 62.0010 * 4.127149
      ≤ 8.447e26 * Real.log 8.447e26 * Real.log (Real.log 8.447e26) := by
    have step1 : (8.447e26 : ℝ) * 62.0010 ≤ 8.447e26 * Real.log 8.447e26 := by
      nlinarith [hL_lo]
    calc 8.447e26 * 62.0010 * 4.127149
        ≤ (8.447e26 * Real.log 8.447e26) * 4.127149 :=
          mul_le_mul_of_nonneg_right step1 (by norm_num)
      _ ≤ 8.447e26 * Real.log 8.447e26 * Real.log (Real.log 8.447e26) :=
          mul_le_mul_of_nonneg_left hLL_lo (by positivity)
  have hLHS : deriv QrefCore4 (iteratedLog 3 8.447e26)
      * (1.1794 * 16948892444103337141417836114)
      ≤ 10.813 * (1.1794 * 16948892444103337141417836114) :=
    mul_le_mul_of_nonneg_right hQub (by norm_num)
  have hnum : (10.813 : ℝ) * (1.1794 * 16948892444103337141417836114)
      < 8.447e26 * 62.0010 * 4.127149 := by norm_num
  have key : deriv QrefCore4 (iteratedLog 3 8.447e26)
      * (1.1794 * 16948892444103337141417836114)
      < 8.447e26 * Real.log 8.447e26 * Real.log (Real.log 8.447e26) := by
    linarith [hLHS, hnum, hRHS]
  rw [hdq, div_lt_div_iff₀ hDpos hcoef, one_mul]
  exact key

/-! ## Curvature on the high window: `q̃'' ≤ 0`

The two grouped-form bounds `Q̃₄' ≥ 10` and `Q̃₄'' ≤ 20` on the full high window
`WH = [8·10²⁶, 1.3·10²⁸]` (via `PhaseEnclosureHigh.lean`), together with
`P = log ξ·log₂ ξ + log₂ ξ + 1 ≥ 250`, give `Q̃₄'' ≤ Q̃₄'·P`, hence
`q̃''(ξ) = (Q̃₄'' − Q̃₄'·P)/D² ≤ 0`.  These bounds are deliberately loose (the
margins are enormous), so the leading parts are bounded termwise and the
`E₃`-free remainders are negligible. -/

set_option maxHeartbeats 1000000 in
/-- Lower bound `Q̃₄'(log₃ ξ) ≥ 10` on the full high window `WH`. -/
private theorem highMatch_Qp_lb {ξ : ℝ} (hlo : (8e26 : ℝ) ≤ ξ) (hhi : ξ ≤ 1.3e28) :
    (10 : ℝ) ≤ deriv QrefCore4 (iteratedLog 3 ξ) := by
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hu0 : (0 : ℝ) < iteratedLog 3 ξ := by linarith [cert_one_lt_iteratedLog_three hξ39]
  obtain ⟨_, _, _, _, _, _⟩ := phaseEnclosure_WH hlo hhi
  obtain ⟨he1lo, he1hi, he2lo, he2hi, he3eq⟩ := phaseEnclosure_E_WH hlo hhi
  obtain ⟨_, _, _, _, hulo, huhi⟩ := phaseEnclosure_WH hlo hhi
  have he1pos : 0 < E 1 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he2pos : 0 < E 2 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he3pos : 0 < E 3 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  set u := iteratedLog 3 ξ with hu
  set e1 := E 1 u with he1def
  set e2 := E 2 u with he2def
  set e3 := E 3 u with he3def
  have he1ne : e1 ≠ 0 := he1pos.ne'
  have he2ne : e2 ≠ 0 := he2pos.ne'
  have he1nn : (0 : ℝ) ≤ e1 := he1pos.le
  have he2nn : (0 : ℝ) ≤ e2 := he2pos.le
  have hunn : (0 : ℝ) ≤ u := hu0.le
  have hden_pos : (0 : ℝ) < e1 ^ 2 * e2 ^ 2 * e3 := by positivity
  have hRp0 : (0 : ℝ) ≤ 2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
      + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
      + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
      + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3 := by
    have b1 : (4.12627 : ℝ) ^ 3 * 61.94665 ^ 3 ≤ e1 ^ 3 * e2 ^ 3 := by gcongr
    have b2 : (1.41737 : ℝ) * 4.12627 ^ 4 * 61.94665 ^ 3
        ≤ u * e1 ^ 4 * e2 ^ 3 := by gcongr
    have n1 : e1 ^ 2 ≤ (4.1703 : ℝ) ^ 2 := by gcongr
    have n2 : e1 ^ 2 * e2 ^ 2 ≤ (4.1703 : ℝ) ^ 2 * 64.73475 ^ 2 := by gcongr
    have n3 : e1 ^ 3 * e2 ^ 2 ≤ (4.1703 : ℝ) ^ 3 * 64.73475 ^ 2 := by gcongr
    have n4 : u * e1 ^ 3 * e2 ^ 2
        ≤ (1.42799 : ℝ) * 4.1703 ^ 3 * 64.73475 ^ 2 := by gcongr
    have hpos : (0 : ℝ) ≤ 2 * e1 + e1 * e2 + 2 * e1 ^ 3 + e1 ^ 3 * e2
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 := by positivity
    nlinarith [b1, b2, n1, n2, n3, n4, hpos]
  have hrem : (0 : ℝ) ≤ (2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
      + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
      + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
      + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3) / (e1 ^ 2 * e2 ^ 2 * e3) :=
    div_nonneg hRp0 hden_pos.le
  have hgroup := cert_grouped_deriv_QrefCore4 hu0
  rw [← he1def, ← he2def, ← he3def] at hgroup
  rw [hgroup]
  have hue1_lo : (5.84 : ℝ) ≤ u * e1 := by
    nlinarith [mul_le_mul hulo he1lo (by norm_num : (0 : ℝ) ≤ 4.12627) hu0.le]
  have he1e2r_hi : e1 / e2 + u * e1 / e2 ≤ 0.164 := by
    rw [← add_div, div_le_iff₀ he2pos]
    nlinarith [he1hi, mul_le_mul huhi he1hi he1pos.le (by norm_num : (0 : ℝ) ≤ 1.42799),
      he2lo]
  have hrecip_hi : 1 / (e1 * e2) ≤ 0.004 := by
    rw [div_le_iff₀ (mul_pos he1pos he2pos)]
    nlinarith [mul_le_mul he1lo he2lo (by norm_num : (0 : ℝ) ≤ 61.94665) he1pos.le]
  linarith [he1lo, hue1_lo, he1e2r_hi, hrecip_hi, hrem]

set_option maxHeartbeats 2000000 in
/-- Upper bound `Q̃₄''(log₃ ξ) ≤ 20` on the full high window `WH`. -/
private theorem highMatch_Qpp_ub {ξ : ℝ} (hlo : (8e26 : ℝ) ≤ ξ) (hhi : ξ ≤ 1.3e28) :
    deriv (deriv QrefCore4) (iteratedLog 3 ξ) ≤ 20 := by
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hu0 : (0 : ℝ) < iteratedLog 3 ξ := by linarith [cert_one_lt_iteratedLog_three hξ39]
  obtain ⟨_, _, _, _, hulo, huhi⟩ := phaseEnclosure_WH hlo hhi
  obtain ⟨he1lo, he1hi, he2lo, he2hi, he3eq⟩ := phaseEnclosure_E_WH hlo hhi
  have he1pos : 0 < E 1 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he2pos : 0 < E 2 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he3pos : 0 < E 3 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  set u := iteratedLog 3 ξ with hu
  set e1 := E 1 u with he1def
  set e2 := E 2 u with he2def
  set e3 := E 3 u with he3def
  have he1ne : e1 ≠ 0 := he1pos.ne'
  have he2ne : e2 ≠ 0 := he2pos.ne'
  have he1nn : (0 : ℝ) ≤ e1 := he1pos.le
  have he2nn : (0 : ℝ) ≤ e2 := he2pos.le
  have hunn : (0 : ℝ) ≤ u := hu0.le
  have he3lo : (8e26 : ℝ) ≤ e3 := by rw [he3eq]; exact hlo
  have hden_pos : (0 : ℝ) < e1 ^ 2 * e2 ^ 2 * e3 := by positivity
  have hden_lo : (5e30 : ℝ) ≤ e1 ^ 2 * e2 ^ 2 * e3 := by
    have h : (4.12627 : ℝ) ^ 2 * 61.94665 ^ 2 * 8e26 ≤ e1 ^ 2 * e2 ^ 2 * e3 := by gcongr
    nlinarith [h]
  have hRppden_hi : ((6 * e1 ^ 3 + 3 * e1 ^ 3 * e2 + 3 * e1 ^ 3 * e2 ^ 3 + 3 * e1 ^ 4 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + 4 * u * e1 ^ 4 * e2 ^ 3
        + u * e1 ^ 5 * e2 ^ 3)
      - (4 + 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
        + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
        + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4)) / (e1 ^ 2 * e2 ^ 2 * e3) ≤ 0.01 := by
    rw [div_le_iff₀ hden_pos]
    have hp : 6 * e1 ^ 3 + 3 * e1 ^ 3 * e2 + 3 * e1 ^ 3 * e2 ^ 3 + 3 * e1 ^ 4 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + 4 * u * e1 ^ 4 * e2 ^ 3
        + u * e1 ^ 5 * e2 ^ 3
        ≤ 6 * 4.1703 ^ 3 + 3 * 4.1703 ^ 3 * 64.73475 + 3 * 4.1703 ^ 3 * 64.73475 ^ 3
            + 3 * 4.1703 ^ 4 * 64.73475 ^ 3 + 2 * 1.42799 * 4.1703 ^ 3
            + 1.42799 * 4.1703 ^ 3 * 64.73475 + 1.42799 * 4.1703 ^ 3 * 64.73475 ^ 3
            + 4 * 1.42799 * 4.1703 ^ 4 * 64.73475 ^ 3
            + 1.42799 * 4.1703 ^ 5 * 64.73475 ^ 3 := by gcongr
    have hn : (0 : ℝ) ≤ 4 + 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
        + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
        + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4 := by positivity
    nlinarith [hden_lo, hp, hn]
  have hgroupPP := cert_grouped_deriv2_QrefCore4 hu0
  rw [← he1def, ← he2def, ← he3def] at hgroupPP
  rw [hgroupPP]
  have hE1sq_hi : e1 ^ 2 ≤ (4.1703 : ℝ) ^ 2 := by nlinarith [he1hi, he1pos]
  have tb_recip_hi : 1 / (e1 * e2) ≤ 0.004 := by
    rw [div_le_iff₀ (mul_pos he1pos he2pos)]
    nlinarith [mul_le_mul he1lo he2lo (by norm_num : (0 : ℝ) ≤ 61.94665) he1pos.le]
  have tb_e2recip_hi : 1 / e2 ≤ 0.0162 := by
    rw [div_le_iff₀ he2pos]; nlinarith [he2lo]
  have tb_e1e2r_lo : (0.0637 : ℝ) ≤ e1 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [he1lo, he2hi]
  have tb_e1sqe2r_hi : e1 ^ 2 / e2 ≤ 0.281 := by
    rw [div_le_iff₀ he2pos]; nlinarith [hE1sq_hi, he2lo]
  have tb_ue1e2r_lo : (0.0903 : ℝ) ≤ u * e1 / e2 := by
    rw [le_div_iff₀ he2pos]
    nlinarith [mul_le_mul hulo he1lo (by norm_num : (0 : ℝ) ≤ 4.12627) hu0.le, he2hi]
  have tb_ue1_hi : u * e1 ≤ 5.9552 := by
    nlinarith [mul_le_mul huhi he1hi he1pos.le (by norm_num : (0 : ℝ) ≤ 1.42799)]
  have tb_ue1sqe2r_hi : u * e1 ^ 2 / e2 ≤ 0.401 := by
    rw [div_le_iff₀ he2pos]
    nlinarith [mul_le_mul huhi hE1sq_hi (by positivity) (by norm_num : (0 : ℝ) ≤ 1.42799),
      he2lo]
  linarith [tb_recip_hi, tb_e2recip_hi, tb_e1e2r_lo, he1hi, tb_e1sqe2r_hi,
    tb_ue1e2r_lo, tb_ue1_hi, tb_ue1sqe2r_hi, hRppden_hi]

set_option maxHeartbeats 1000000 in
/-- `q̃''(ξ) ≤ 0` on the full high window `WH = [8·10²⁶, 1.3·10²⁸]`. -/
private theorem highMatch_deriv2_nonpos {ξ : ℝ} (hlo : (8e26 : ℝ) ≤ ξ)
    (hhi : ξ ≤ 1.3e28) : deriv (deriv qCore) ξ ≤ 0 := by
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hξpos : (0 : ℝ) < ξ := by linarith
  obtain ⟨hLxlo, _, hLLxlo, _, _, _⟩ := phaseEnclosure_WH hlo hhi
  have hLxpos : (0 : ℝ) < Real.log ξ := by linarith
  have hLLxpos : (0 : ℝ) < Real.log (Real.log ξ) := by linarith
  have hQp_lo := highMatch_Qp_lb hlo hhi
  have hQpp_ub := highMatch_Qpp_ub hlo hhi
  set u := iteratedLog 3 ξ with hu
  have hd2 : deriv (deriv qCore) ξ
      = (deriv (deriv QrefCore4) u
          - deriv QrefCore4 u
            * (Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1))
        / (ξ * Real.log ξ * Real.log (Real.log ξ)) ^ 2 := by
    rw [cert_deriv2_qCore_eq hξ39, ← hu, cert_iteratedLogThreeDeriv,
      cert_iteratedLogThreeDeriv2]
    field_simp
    ring
  rw [hd2]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have hP : (250 : ℝ)
      ≤ Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1 := by
    nlinarith [hLxlo, hLLxlo, hLxpos, hLLxpos]
  have hQpP : (10 : ℝ) * 250 ≤ deriv QrefCore4 u
      * (Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1) :=
    mul_le_mul hQp_lo hP (by norm_num) (by linarith [hQp_lo])
  linarith [hQpP, hQpp_ub]

set_option maxHeartbeats 1000000 in
/-- `q̃'` is antitone on `[8.447·10²⁶, 1.3·10²⁸]`: its second derivative is `≤ 0`
there (via `highMatch_deriv2_nonpos`). -/
private theorem highMatch_antitone :
    AntitoneOn (deriv qCore) (Set.Icc (8.447e26 : ℝ) 1.3e28) := by
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
    have hx8 : (8e26 : ℝ) ≤ x := by linarith [hx.1]
    have hx13 : x ≤ 1.3e28 := by linarith [hx.2]
    exact highMatch_deriv2_nonpos hx8 hx13

/-! ## The proved certificate -/

set_option maxHeartbeats 1000000 in
/-- **Proved core-level input to `eq:slope-matched-monotonicity`**:
`1.1794·(log N₁ · Q̃₃(log₃ x(f))) < f·log x(f)`
for every `f ∈ [3.24, 46]`, where `x(f) = N₁·f/log N₁` and
`N₁ = 16 948 892 444 103 337 141 417 836 114`. -/
theorem highSlopeMatchedCert (f : ℝ) (h1 : (3.24 : ℝ) ≤ f) (h2 : f ≤ 46) :
    1.1794 * (Real.log 16948892444103337141417836114
        * QrefCore3 (iteratedLog 3 (highBreakpointX f)))
      < f * Real.log (highBreakpointX f) := by
  obtain ⟨hLlo, hLhi⟩ := cert_log_N1_bounds
  have hLpos : (0 : ℝ) < Real.log 16948892444103337141417836114 := by linarith
  have hLne : Real.log 16948892444103337141417836114 ≠ 0 := hLpos.ne'
  have hNne : (16948892444103337141417836114 : ℝ) ≠ 0 := by norm_num
  set ξ := highBreakpointX f with hξdef
  -- `ξ ∈ [8.447·10²⁶, 1.3·10²⁸]`
  have hξloB : (8.447e26 : ℝ) ≤ ξ := by
    rw [hξdef, highBreakpointX, le_div_iff₀ hLpos]; nlinarith [h1, hLhi]
  have hξhiW : ξ ≤ 1.3e28 := by
    rw [hξdef, highBreakpointX, div_le_iff₀ hLpos]; nlinarith [h2, hLlo]
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hlogξpos : (0 : ℝ) < Real.log ξ := by linarith [(cert_logs_pos hξ39).1]
  -- antitonicity: `q̃'(ξ) ≤ q̃'(8.447·10²⁶) < 1/(1.1794·N₁)`
  have hmemξ : ξ ∈ Set.Icc (8.447e26 : ℝ) 1.3e28 := ⟨hξloB, hξhiW⟩
  have hmemB : (8.447e26 : ℝ) ∈ Set.Icc (8.447e26 : ℝ) 1.3e28 :=
    ⟨le_refl _, by norm_num⟩
  have hanti : deriv qCore ξ ≤ deriv qCore 8.447e26 :=
    highMatch_antitone hmemB hmemξ hξloB
  have hderiv : deriv qCore ξ < 1 / (1.1794 * 16948892444103337141417836114) :=
    lt_of_le_of_lt hanti highMatch_endpoint_slope
  -- slope identity `Q̃₃(log₃ ξ) = ξ·log ξ·q̃'(ξ)` and `N₁·f = ξ·log N₁`
  have hslope : QrefCore3 (iteratedLog 3 ξ) = ξ * Real.log ξ * deriv qCore ξ := by
    have hs := cert_qCore_slope hξ39
    rw [eq_div_iff hlogξpos.ne'] at hs
    rw [← hs]; ring
  have hf : f = ξ * Real.log 16948892444103337141417836114 / 16948892444103337141417836114 := by
    rw [hξdef, highBreakpointX]; field_simp
  -- `deriv·(1.1794·N₁) < 1`
  have hd1 : deriv qCore ξ * (1.1794 * 16948892444103337141417836114) < 1 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 1.1794 * 16948892444103337141417836114)] at hderiv
    exact hderiv
  have hpos : (0 : ℝ) < ξ * Real.log 16948892444103337141417836114 * Real.log ξ := by
    positivity
  have hmul := mul_lt_mul_of_pos_left hd1 hpos
  rw [hf, hslope]
  rw [div_mul_eq_mul_div, lt_div_iff₀ (by norm_num : (0 : ℝ) < 16948892444103337141417836114)]
  nlinarith [hmul]

end Erdos320
